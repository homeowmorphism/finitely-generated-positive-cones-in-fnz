# Review the submitted mathematics

The two selected results are Theorem 1.1 and Corollary 1.2 of
[Su, *Finitely generated positive cones in Fₙ × ℤ*](https://arxiv.org/abs/2608.31103v1).
Human review should confirm that the formal statements express the intended
mathematics. Lean checks the proofs of those statements.

## Statement and scope

Start with [Challenge.lean](Challenge.lean), which uses Mathlib and defines the
submission's mathematical terms independently of the proof library. Check:

1. `IsPositiveCone` represents a strict positive cone for a left order.
   Multiplication closure and exclusion of `1` also ensure that an element
   and its inverse cannot both belong to the cone.
2. `HasFGPositiveCone` means generation by a finite set under nonempty
   semigroup products. A `Finset` expresses finiteness; it does not assert
   an algorithm for membership in the generated cone.
3. `FreeGroup (Fin n) × Multiplicative ℤ` is the intended direct product.
4. Both statements cover every natural rank `n ≥ 2`, including rank two.
   The classification is an equivalence with `Even n`.

[Solution.lean](Solution.lean) proves these statements using the corresponding
endpoints in [Main.lean](FnZPositiveCones/Main.lean). The definitions match
[Interfaces.lean](FnZPositiveCones/Interfaces.lean). Comparator checks the
selected Challenge and Solution declarations; the Challenge placeholders are
not proof dependencies of the Solution.

The selected claims make no assertion for ranks zero or one. The optional
`6*(n-1)+1` generator bound is an upper bound, not a minimality result. Stronger
odd-rank non-isolation theorems are part of the library but are not separate
claims selected for submission. See [formalization.yaml](formalization.yaml)
for the full scope and source attribution.

## Construction and converse

For the even-rank construction, begin with
[Construction.lean](FnZPositiveCones/Construction.lean). The main review points are:

- [Schreier/Positive.lean](FnZPositiveCones/Schreier/Positive.lean): right-coset
  representatives and generation of the restricted cone by nonempty products.
- [Gamma/Isomorphism.lean](FnZPositiveCones/Gamma/Isomorphism.lean): the marked
  product isomorphism and the exact image `psi_C` of `b⁶`.
- [Cover/ExplicitBasis.lean](FnZPositiveCones/Cover/ExplicitBasis.lean): the
  explicit rank `d+1`, including `d=1`, and the substitution `d=n-1`.
- [External/BaseCone.lean](FnZPositiveCones/External/BaseCone.lean): identity
  exclusion and totality for the actual strict two-generator semigroup.

For the converse, follow `even_of_hasFGPositiveCone` in
[Classification.lean](FnZPositiveCones/Classification.lean), then
`hasFGPositiveCone_exists_finiteNormalizedDomains` in
[External/CircularFGPingPong.lean](FnZPositiveCones/External/CircularFGPingPong.lean),
and `NormalizedIntervalData.even_card` in
[External/CircularGapConnectivity.lean](FnZPositiveCones/External/CircularGapConnectivity.lean).
This route constructs the cofinal quotient, finite domains, and successor
from finite positive generation. The endpoint argument proves the connectivity
needed for parity. These are proved inputs, not extra hypotheses of the final
classification.

The converse replaces the paper's route through the full isolated-order
theorem. [CLASSIFICATION_REVIEW.md](CLASSIFICATION_REVIEW.md) explains that
replacement. The auxiliary isolated-order branch has further replacements
recorded in [EXTERNAL_OBLIGATIONS.md](EXTERNAL_OBLIGATIONS.md).

## Evidence and its limits

Use the commands in [README.md](README.md#verification) on the exact submission
commit. [ProofAudit.lean](ProofAudit.lean) checks the two endpoint types,
rank-two existence, rank-three nonexistence, and axiom dependencies.
[FinalContractAudit.lean](FinalContractAudit.lean) checks critical construction
contracts and traverses the stronger non-isolation theorem's dependencies.
The Python certificate checker is supplementary evidence.

The retained review reports were written by AI agents. Their use of
"independent" refers to separate agent reviews, not human peer review.
[FINAL_CONTRACT_REVIEW.md](FINAL_CONTRACT_REVIEW.md) discloses overlap between
review and implementation work. [AUDIT_REPORT.md](AUDIT_REPORT.md) records an
audit of an earlier commit and its limitations, including incomplete checks
against the cited external papers. Those reports do not certify later edits
or replace Palomar's full verification report.
