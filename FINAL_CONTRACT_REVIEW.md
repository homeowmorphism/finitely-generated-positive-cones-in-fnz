> Historical AI review of the snapshot identified below. This report is not
> a verification report for the current submission commit. Old namespaces,
> toolchains, and checkpoint statuses are preserved as written. Commit hashes and removed development files refer to the
> private development repository, not to this public snapshot.
> See [README.md](README.md) for current checks and
> [formalization.yaml](formalization.yaml) for review disclosure.

# Final contract and dependency review

Reviewed on 2026-09-21 against the actual Lean source and compiled declarations.
This review did not edit the library, manifest, root imports, or dependencies.
It checks complete mathematical contracts rather than treating manifest shape
validation or declaration existence as proof of those contracts.

The reviewer implemented several earlier algebraic and external modules, including
the base cone, central-endpoint argument, and last-letter density. Those parts
also have reviews by other workers; this document does not claim independent
authorship review of the reviewer's own proofs. Its fresh contribution is the
combined exact-statement, acceptance-lemma, and dependency audit.

## Mathematical contracts

The supplied `Interfaces.lean` is unchanged from `HEAD`. `IsPositiveCone` remains
an identity-excluding `Subsemigroup` cone in an arbitrary group, and
`SemigroupFG` uses `Subsemigroup.closure`. Neither group commutativity nor a
monoid closure has entered the target definitions.

- **E00–E02:** `base_one_not_mem` and `base_total` prove exclusion and totality
  for the literal closure of `{aGamma, bGamma}` in the specified presented group.
  The action used for exclusion satisfies the actual presentation relation.
  Its strict movement invariant is closed under nonempty multiplication.
  Totality's temporary `nonnegative` monoid has carrier exactly identity or
  membership in the original strict semigroup; it is not the endpoint cone.
- **T00–T03:** representatives satisfy `g * (rightRep hT g)⁻¹ ∈ K`, so these
  are right cosets `K*g`. `positiveSchreierSet` is a set of elements of `K` and
  expressly excludes `1`. The closure induction allows an identity intermediate
  value, then `positiveSchreier_closure_eq` rules out that value for the final
  positive element using `hP.1`. Thus the final generation is by nonempty
  semigroup products. No normality or prefix-closed transversal is assumed.
- **G00–G15:** the six Schreier relations, X/Y₀/Z word identities, generator
  expansions, and all four X/Y₀/Z/C weight evaluations are present, not merely
  the single entry point listed per task. `H_marked_product_equiv` is built from
  the explicit product homomorphism, its checked weighted left inverse, and
  surjectivity. Its `MulEquiv` inverse laws and
  `ψ(C) = y⁻¹ * x⁻¹ * y * x * z⁻¹` are retained exactly.
- **D00–D05 and B00–B06:** the right-action multiplication convention remains
  consistent with the explicit weighted actions. `coverExplicitBasis` has
  injective lift by its weight inverse and surjective lift by checked basis
  generation. `coverRankEquiv` gives the actual equivalence with
  `FreeGroup (Fin (d+1))`, not an unspecified freeness instance or rank bound.
  All positive degrees are covered by `[NeZero d]`. Invertibility of two is
  derived from oddness/coprimality, including odd composite degree; no field
  assumption occurs. The optional source-coordinate conjugacies and alternating
  word statement are present.
- **K00–K07:** the second subgroup remains a `Subgroup gammaH`. Its product
  equivalence preserves the subtype membership proof and checks both inverses.
  Exponents involving subtraction are integers. `conditionalEvenRank` really
  has type `BaseConeGoal → EvenRankGoal` and calls the verified rank equivalence.
- **M00/M01/M02:** the literal unconditional requested types are present.
  M00 applies the conditional construction to `baseCone`; M01 combines M00
  with the independently checked FG obstruction. The stronger O00/O01 route
  is also now proved. M02 is an existential bound of `6*(n-1)+1`, not a
  minimality claim. The audit checks `n=2`, the bound `7`, `d=1` rank two,
  and the odd-rank contradiction at `n=3` explicitly.
- **O00/O01:** `mmrt_no_isolated_order_odd` in `External/OddRankComplete.lean`
  has the exact `LeftOrderOddRankObstructionGoal` type. `oddRankObstruction`
  has the exact `OddRankObstructionGoal` type. Neither theorem assumes finite
  positive generation, cofinality, separation, a successor, domain data, or
  any unproved dynamical input. The conditional O03 milestone remains intact.

## Source correspondence and the stronger branch

The source statements remain unchanged. The checked base-cone action and
positive-fraction normal form replace the cited external proof. The weighted
certificate and explicit free basis replace the sketched subgroup and rank
identifications. They have actual Lean proofs, rather than a Python certificate
or a citation as a proof premise.

For MMRT's noncofinal branch, the finite central-orbit endpoint gives an action
of the free factor with a weakly monotone, unbounded orbit. The original order
resolves ties in the completion. Two perturbations preserve every finite trace
and give opposite strict signs for one common element. This proves nonisolation
without the unresolved varying-primitive bound in the original longer route.

For the circular branch, isolation gives an actual successor and isolated lift
order. Each nonempty closed invariant set avoiding the basepoint has a convex
complement stabilizer with injective free projection. Finite determination
restricts to that stabilizer, and free-group nonisolation makes it cyclic.
Cyclic accumulation plus the tight orbit-gap property excludes derived orbit
points inside the complement. Applying this to each actual last-letter derived
set proves the required density. The supported finite-trace argument then proves
first-letter closure separation. Generic finite normalized domains and their
checked connected endpoint relation give the parity obstruction. This argument
does not assume a unique minimal invariant set or absence of finite orbits.

## Manifest correction

The previous edge `F02 → F01` conflated generic normalized-domain geometry with
the FG constructor. The corrected graph introduces:

| Node | Actual declaration | Mathematical prerequisites |
|---|---|---|
| S00 | `CircularDynamics.finiteNormalizedDomains` | C05; successor and separation are explicit theorem inputs |
| I00 | `NoncofinalEndpointAction.isolatedOddRankCenterCofinal` | C05; the action, perturbation and completion helpers are checked internally |
| I01 | `isolatedCircularSeparation` | C05; realization, successor, density and supported perturbation helpers are checked internally |

S00 lives in `External/CircularFGPingPong.lean`, but its type has no FG premise.
The FG-specialized F01 applies S00, while F02 now depends on S00 directly and
F03 depends on F02. O00 depends on C00, C05, F03, I00 and I01; O01 depends on
O00 and C05. These corrections were sent to the coordinator and are present in
the inspected 72-node, 150-edge manifest, whose topological order has no violations.
This distinguishes mathematical proof dependencies from transitive module imports.

## Verification

All 163 implementation modules were directly root-imported at the review
snapshot. The mathlib checkout is still
`dec5b2b780537b6eaf7f5e5f000c12f7387fb24d`, and the toolchain remains
`leanprover/lean4:v4.35.0-rc2`. There is no `HEAD` diff in the target interfaces,
toolchain, `lakefile.toml`, or `lake-manifest.json`. A source scan found only
commentary mentions of forbidden proof placeholders, with no such commands in
the accepted tree.

The independent `/private/tmp/FinalContractAudit.lean` checks the literal
contracts and specializations above, prints axioms for 19 critical declarations,
and traverses theorem bodies to distinguish the stronger O00 proof from the
FG-specific path. After the coordinator's full 9102-job artifact build,
`lake env lean /private/tmp/FinalContractAudit.lean` exited **0**, with no errors
or warnings. The exact-type checks include the two unconditional requested
endpoints, original O00/O01, both conditional milestones, degree one, rank two,
the seven-generator upper bound, composite odd degree nine, the marked inverse
laws, right representatives, and the strict Schreier closure equality.

All 19 axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`.
The proof-body traversal explicitly finds the generic `finiteNormalizedDomains`,
`NormalizedIntervalData.backward_forward`, `NormalizedIntervalData.even_card`,
`isolatedOddRankCenterCofinal`, and `isolatedCircularSeparation` in O00's
dependencies. It confirms that O00 does **not** depend on
`NoncofinalPrecone.center_cofinal_of_semigroupFG`,
`semigroupFG_exists_finiteNormalizedDomains`, or
`hasFGPositiveCone_exists_finiteNormalizedDomains`. The traversal inspects
theorem bodies (`ConstantInfo.value? true`), not only their types or imports.
All 67 proof-task declaration pointers also occur in their recorded source
modules. No missing acceptance declaration or mathematical prerequisite remains
from this review.

Durable output: [final-contract-audit.log](build_logs/implementation-2026-09-21/final-contract-audit.log).
The root build and repository-wide audit/certificate commands are the
coordinator's separate verification responsibility. Earlier historical review
files describe the state when they were written; this review supersedes their
claims that O00/O01 remain open.
