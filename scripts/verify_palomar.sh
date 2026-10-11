#!/usr/bin/env bash
set -euo pipefail

# Local checks. The full hosted preflight is .github/workflows/palomar.yml.
# On macOS, --build-only builds the submission and audits its theorem axioms.
# The default additionally runs sandboxed Comparator on Linux with the two
# independent kernels that Palomar uses.
build_only=false
case "${1:-}" in
  "") ;;
  --build-only) build_only=true ;;
  *) echo "Usage: $0 [--build-only]" >&2; exit 2 ;;
esac
if [[ $# -gt 1 ]]; then
  echo "Usage: $0 [--build-only]" >&2
  exit 2
fi

repository_root=$(cd "$(dirname "$0")/.." && pwd)
cd "$repository_root"
for required_command in git lake lean python3; do
  if ! command -v "$required_command" >/dev/null 2>&1; then
    echo "error: $required_command is required" >&2
    exit 2
  fi
done
python3 scripts/check_submission.py
if [[ "$build_only" == false ]]; then
  if [[ $(uname -s) != Linux ]]; then
    echo "error: sandboxed Comparator requires Linux and bubblewrap." >&2
    echo "Use --build-only for local checks, then run the Palomar preflight workflow." >&2
    exit 2
  fi
  if ! command -v "${COMPARATOR_BWRAP:-bwrap}" >/dev/null 2>&1; then
    echo "error: install bubblewrap or set COMPARATOR_BWRAP to its executable." >&2
    exit 2
  fi
fi

lean_prefix=$(lean --print-prefix)
if [[ "$build_only" == false ]]; then
  for required_tool in lake leanexport leanchecker nanoda_bin con-ron; do
    if [[ ! -x "$lean_prefix/bin/$required_tool" ]]; then
      echo "error: the selected Lean toolchain does not bundle $required_tool" >&2
      exit 2
    fi
  done
fi

check_dir=$(mktemp -d "${TMPDIR:-/tmp}/fnz-palomar.XXXXXX")
trap 'rm -rf "$check_dir"' EXIT
python3 - "$check_dir" "$lean_prefix" <<'PY'
import json
import pathlib
import re
import sys

destination, prefix = map(pathlib.Path, sys.argv[1:])
try:
    config = json.loads(pathlib.Path("comparator.json").read_text())
    if not isinstance(config, dict):
        raise ValueError("expected one JSON object")
    if "external_kernels" in config:
        raise ValueError("Palomar rejects external_kernels in the submitted config")
    supported = {
        "challenge_module", "solution_module", "theorem_names", "definition_names",
        "permitted_axioms", "enable_nanoda",
    }
    if set(config) - supported:
        raise ValueError(f"unsupported fields: {', '.join(sorted(set(config) - supported))}")
    if config.get("challenge_module") != "Challenge" or config.get("solution_module") != "Solution":
        raise ValueError("this script expects the Challenge and Solution modules")
    allowed = {"propext", "Quot.sound", "Classical.choice"}
    axioms = config.get("permitted_axioms")
    if not isinstance(axioms, list) or any(not isinstance(x, str) or x not in allowed for x in axioms):
        raise ValueError("permitted_axioms must list only the three standard axioms")
    names = config.get("theorem_names")
    if not isinstance(names, list) or not names:
        raise ValueError("theorem_names must be a nonempty list")
    if any(not isinstance(name, str) or not re.fullmatch(r"[A-Za-z_][A-Za-z_0-9']*(?:\.[A-Za-z_][A-Za-z_0-9']*)*", name) for name in names):
        raise ValueError("theorem_names must contain ordinary Lean declaration names")
    definitions = config.get("definition_names", [])
    if definitions:
        raise ValueError("this submission has no definition holes; definition_names must be empty")
except (OSError, ValueError) as error:
    raise SystemExit(f"error: comparator.json: {error}")

# Palomar registers its own bundled checkers; use the same pair locally.
config.pop("enable_nanoda", None)
config["external_kernels"] = {
    "nanoda": [str(prefix / "bin/nanoda_bin")],
    "con-ron": [str(prefix / "bin/con-ron")],
}
(destination / "comparator.json").write_text(json.dumps(config, indent=2) + "\n")

lean_names = ", ".join("`" + name for name in names)
lean_axioms = ", ".join("`" + name for name in axioms)
(destination / "AxiomAudit.lean").write_text(f"""module
import all Solution
import Lean.Util.CollectAxioms

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[{lean_axioms}]
  for name in (#[{lean_names}] : Array Name) do
    unless (← getEnv).contains name do
      throwError "missing submission theorem: {{name}}"
    let axioms ← collectAxioms name
    for axiomName in axioms do
      unless allowed.contains axiomName do
        throwError "{{name}} uses forbidden axiom {{axiomName}}"
    logInfo m!"{{name}} uses axioms {{axioms}}"
""")
PY

lake build FnZPositiveCones Challenge Solution
lake env lean "$check_dir/AxiomAudit.lean"
if [[ "$build_only" == true ]]; then
  echo "Local structure, build, and theorem axiom checks passed. Full hosted verification is still required."
else
  lake comparator --config "$check_dir/comparator.json"
  echo "Local Comparator passed. Run the full hosted preflight on the final public commit before submitting."
fi
