# Finitely generated positive cones in Fₙ × ℤ

This Lean 4/Mathlib project proves Theorem 1.1 and Corollary 1.2 of
Hang Lu Su's [*Finitely generated positive cones in Fₙ × ℤ*](https://arxiv.org/abs/2608.31103v1).
For every rank `n ≥ 2`, the group `Fₙ × ℤ` has a finitely generated positive
cone if and only if `n` is even.

## Submitted statements

[Challenge.lean](Challenge.lean) states the two claims using Mathlib and two
explicit definitions. A strict positive cone is a subsemigroup excluding the
identity such that every nonidentity element or its inverse belongs to it.
Finite generation uses `Subsemigroup.closure`, so products are nonempty.

```lean
∀ n : ℕ, 2 ≤ n → Even n →
  HasFGPositiveCone (FreeGroup (Fin n) × Multiplicative ℤ)

∀ n : ℕ, 2 ≤ n →
  (HasFGPositiveCone (FreeGroup (Fin n) × Multiplicative ℤ) ↔ Even n)
```

[Solution.lean](Solution.lean) repeats these definitions and proves both claims
from the library. It does not import the Challenge. The Challenge's two deliberate
`sorry` declarations are statement placeholders for Comparator;
[comparator.json](comparator.json) selects their proved counterparts.

Both library endpoints are in [Main.lean](FnZPositiveCones/Main.lean). Use
`import FnZPositiveCones.Main` for these results or `import FnZPositiveCones`
for the complete library. No extra mathematical hypothesis appears in either
endpoint. The library also contains a generating-set upper bound and stronger
non-isolation results; these are not separate selected claims.

## Verification

The Lean version is pinned in [lean-toolchain](lean-toolchain), and the Mathlib
revision is pinned in [lakefile.lean](lakefile.lean) and
[lake-manifest.json](lake-manifest.json). With Lean installed, run:

```bash
bash scripts/verify_palomar.sh --build-only
lake env lean ProofAudit.lean
lake env lean FinalContractAudit.lean
```

The first command builds the library, Challenge, and Solution, then checks that
the submitted proofs use only `propext`, `Classical.choice`, and `Quot.sound`.
Warnings for the two Challenge placeholders are expected. The retained Lean
audits check exact theorem types, boundary cases, and critical proof dependencies.

On Linux with `bubblewrap`, `bash scripts/verify_palomar.sh` also runs sandboxed
Comparator with the toolchain's independent kernels. The
[Lean and Comparator workflow](.github/workflows/lean.yml) runs this Linux build
and proof verification on pushes to `palomar/**` branches. It works while the
repository is private and saves a verification log. These checks do not include
Palomar's Challenge provenance checks or editorial review.

The [Palomar preflight workflow](.github/workflows/palomar.yml) runs the official
full verifier for an exact publicly fetchable commit. To dispatch it through
GitHub Actions, first make the workflow available on the repository's default
branch, then select the commit to verify. Inspect that full report before
submission. Local compilation and the private-repository workflow do not
establish that the official preflight has passed. The preflight workflow does
not submit or register the result, and a passing report is not editorial acceptance.

An optional certificate regression check is available:

```bash
python3 verify_certificates.py --max-d 128
```

This Python check supplements the Lean proofs. The fixed identities and the
required results for every degree are proved in Lean.

## Review and provenance

[REVIEW_START_HERE.md](REVIEW_START_HERE.md) gives a focused review path.
[formalization.yaml](formalization.yaml) records sources, scope, proof changes,
authorship, and AI involvement. AI agents substantially developed both the
formal proofs and the review reports. No completed independent human mathematical
review is documented.

The construction follows the paper's subgroup tower, with weighted-action
proofs of the marked isomorphism and free basis. The classification uses a
direct finite-generation argument through circle domains and endpoint parity.
These and the auxiliary proof replacements are described in
[blueprint.md](blueprint.md) and [EXTERNAL_OBLIGATIONS.md](EXTERNAL_OBLIGATIONS.md).
The retained review reports document historical snapshots. Their references to
old namespaces, toolchains, or removed development artifacts are not current
verification instructions.
