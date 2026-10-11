#!/usr/bin/env python3
"""Read-only checks of the Git-visible submission candidate, not a Palomar verdict.

Includes tracked and nonignored untracked files, excluding tracked deletions.
Use --require-clean after committing to require an immutable local snapshot.
Palomar additionally validates metadata, detects the license, authenticates
dependencies, parses module headers with Lean, and runs Comparator remotely.
"""

import argparse
import json
import pathlib
import re
import subprocess
import sys


ROOT = pathlib.Path(__file__).resolve().parents[1]
COMPILED = {".olean", ".ilean", ".a", ".bc", ".dll", ".dylib", ".o", ".obj", ".so", ".trace"}
LICENSE_NAME = re.compile(r"(?:license|licence|copying|unlicense|ofl)(?:\.(?:md|markdown|txt))?", re.I)


def git(*args):
    return subprocess.check_output(["git", "-C", str(ROOT), *args])


def module_header(source):
    """Recognize a leading module command after ordinary nested/line comments."""
    index = 0
    while True:
        while index < len(source) and source[index].isspace():
            index += 1
        if source.startswith("--", index):
            newline = source.find("\n", index)
            index = len(source) if newline < 0 else newline + 1
        elif source.startswith("/-", index):
            if source.startswith(("/-!", "/--"), index):
                return False  # Module/declaration documentation belongs after module.
            depth = 1
            index += 2
            while depth and index < len(source):
                if source.startswith("/-", index):
                    depth += 1
                    index += 2
                elif source.startswith("-/", index):
                    depth -= 1
                    index += 2
                else:
                    index += 1
            if depth:
                return False
        else:
            return re.match(r"module(?:\s|$|--|/-)", source[index:]) is not None


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--require-clean", action="store_true")
    args = parser.parse_args()
    errors = []
    names = {pathlib.Path(name.decode()) for name in
             git("ls-files", "-z", "--cached", "--others", "--exclude-standard").split(b"\0") if name}
    names = {name for name in names if not {".git", ".lake"}.intersection(name.parts)
             and ((ROOT / name).exists() or (ROOT / name).is_symlink())}
    required = {"lean-toolchain", "lake-manifest.json", "formalization.yaml", "comparator.json",
                "Challenge.lean", "Solution.lean"}
    for name in sorted(required):
        if pathlib.Path(name) not in names:
            errors.append(f"missing Git-visible required file: {name}")
    lakefiles = names.intersection({pathlib.Path("lakefile.lean"), pathlib.Path("lakefile.toml")})
    if len(lakefiles) != 1:
        errors.append("exactly one root lakefile.lean or lakefile.toml is required")
    licenses = [name for name in names if len(name.parts) == 1 and LICENSE_NAME.fullmatch(name.name)]
    if len(licenses) != 1:
        errors.append("exactly one conventional root license file is required")
    total_bytes = 0
    lean_count = 0
    for name in sorted(names):
        path = ROOT / name
        if path.is_symlink():
            if path.suffix == ".lean" or name in licenses or str(name) in required or name in lakefiles:
                errors.append(f"submitted source/configuration must not be a symlink: {name}")
            continue
        if not path.is_file():
            errors.append(f"not a regular submitted file (possibly a submodule): {name}")
            continue
        data = path.read_bytes()
        total_bytes += len(data)
        if path.suffix in COMPILED:
            errors.append(f"compiled artifact outside .lake: {name}")
        if data.startswith(b"version https://git-lfs.github.com/spec/v1"):
            errors.append(f"Git LFS pointer: {name}")
        if path.suffix == ".lean" or name in licenses:
            try:
                source = data.decode("utf-8")
            except UnicodeDecodeError:
                errors.append(f"not UTF-8: {name}")
                continue
            if name in licenses and (not source.strip() or len(data) > 1024 * 1024):
                errors.append(f"license must be nonempty and at most 1 MiB: {name}")
            if path.suffix == ".lean":
                lean_count += 1
                lines = data.count(b"\n") + int(bool(data) and not data.endswith(b"\n"))
                if lines > 10000:
                    errors.append(f"{name}: {lines} physical lines exceed 10000")
                if path.name != "lakefile.lean" and not module_header(source):
                    errors.append(f"{name}: missing leading module command")
                if name == pathlib.Path("Challenge.lean") and (lines > 1000 or len(data) > 100 * 1024):
                    errors.append("Challenge.lean exceeds 1000 lines or 100 KiB")
    if total_bytes > 500 * 1024 * 1024:
        errors.append("submitted files exceed 500 MiB")
    try:
        manifest = json.loads((ROOT / "lake-manifest.json").read_text())
        for package in manifest["packages"]:
            if package.get("type") != "git":
                errors.append(f"this project expects pinned Git dependencies: {package.get('name')}")
            elif not re.fullmatch(r"https://github\.com/[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+", package["url"]):
                errors.append(f"dependency must use a public GitHub HTTPS URL: {package.get('name')}")
            elif not re.fullmatch(r"[0-9a-f]{40}", package["rev"]):
                errors.append(f"dependency must use a full commit SHA: {package.get('name')}")
    except (OSError, ValueError, KeyError, TypeError) as error:
        errors.append(f"cannot check dependency manifest: {error}")
    status = git("status", "--porcelain").decode()
    if args.require_clean and status:
        errors.append("working tree is not clean; commit the final candidate before selecting its SHA")
    if errors:
        print("Submission structure check failed:", file=sys.stderr)
        for error in errors:
            print(f"  - {error}", file=sys.stderr)
        return 1
    print(f"Submission structure passed: {len(names)} candidate files, {lean_count} Lean files.")
    if status:
        print("Uncommitted changes are included locally; they must be committed and pushed for Palomar.")
    else:
        print(f"Clean local snapshot: {git('rev-parse', 'HEAD').decode().strip()}")
    print("This preliminary check does not replace Palomar's full hosted verification.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
