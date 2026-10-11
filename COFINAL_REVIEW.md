> Historical AI review of the snapshot identified below. This report is not
> a verification report for the current submission commit. Old namespaces,
> toolchains, and checkpoint statuses are preserved as written. Commit hashes and removed development files refer to the
> private development repository, not to this public snapshot.
> See [README.md](README.md) for current checks and
> [formalization.yaml](formalization.yaml) for review disclosure.

# Independent review of the cofinal circular-order adapter

Reviewer: `/root/gamma`, 2026-09-20. Read-only review of implementation by the coordinator and other workers. This review covers the new cofinal branch, not the still-unproved dynamical obstructions.

The reviewed proof recovers the original left order and transfers isolation in the required direction. No mathematical gap or accidental extra hypothesis was found in the source review.

- `CofinalCocycle.lean` defines the section height using the actual representative in `[1,z)`. Its multiplication cocycle is `height(g) + height(h) - height(gh)`, with integer arithmetic. The theorem `cofinalProductCocycle_value` identifies this with the floor of the product of representatives.
- `cofinalProductCocycle_eq_circular_value` handles identity factors explicitly. Products below `z` have carry zero and increasing representatives; products at or above `z` have carry one and wrap strictly below the first representative. Returning products are included in the wrapped case. This proves equality with the actual circular-order carry, including degenerate triples, rather than an arbitrary cohomologous cocycle.
- `cofinalProductExtensionEquiv` has explicit mutually inverse maps `(g,k) ↦ (g,height(g)+k)` and `(g,m) ↦ (g,m-height(g))`. Its multiplication proof uses the stated cocycle, with the correct sign. `cofinalProductExtensionEquiv_positive_iff` proves the exact sign rule: positive height, or zero height and nonidentity base. No abelian hypothesis on the base group is used.
- The free-group generator heights are fixed at `-height(of i)`. Consequently the composed free section sends every marked free generator to `(of i,1)`, and the composed product map is the identity. `cofinalCircularProductPositive_recovery` therefore recovers the original positive semigroup, not just an isomorphic ordered group or an unrelated lift.
- `CocycleTopology.lean` proves continuity by induction on each fixed free word. Cone equality determines all section heights using the signs of `(g,-height(g))`; the section multiplication identity then determines the cocycle. `CircularInjectivity.lean` recovers every ternary carry from the cocycle, and strict orientations from nondegenerate carries. These give injectivity of `circularFreeProductCone` for fixed generator heights.
- `CircularTopology.lean` uses the actual product topology on strict circular signs. The inverse image of the isolated lifted cone under a continuous injective lift is the singleton circular order. Recovery places the prescribed original order in this lift. Thus `isOpen_singleton_cofinalProductCircularGroupOrder` has the correct direction: isolation of a left order with positive cofinal center implies isolation of its quotient circular order. This argument does not assume that the quotient map is open or possesses a local section.

The inspected `OddReduction.lean` leaves two explicit inputs: nonisolation of circular orders on odd-rank free groups, and cofinality of the positive distinguished center in an isolated odd-rank product order. Opposite cones handle the negative orientation through a verified involutive homeomorphism. The conditional reduction does not prove either dynamical input and does not discharge O00 or M01.

After the coordinator's full imported build succeeded, `lake env lean /tmp/CofinalReviewAudit.lean` completed with exit code 0. The log is `build_logs/implementation-2026-09-20/cofinal-review.log`; the identical audit source is preserved as `CofinalReviewAudit.lean` for reproduction. The audit checked the exact recovery and isolation types, an explicit example with only positivity, cofinality, and isolation hypotheses, and the conditional reduction with its two displayed inputs. The checked final `OddReduction.lean` is identical to the source reviewed above.

The nine audited declarations—carry equality, extension equivalence, positivity correspondence, product-map identity, cone recovery, lift injectivity, lift continuity, isolation transfer, and odd-rank reduction—use only `propext`, `Classical.choice`, and `Quot.sound`. No project axiom or `sorryAx` occurs. The conditional theorem still has its two explicit dynamical assumptions; ordinary axiom output does not turn those assumptions into proofs.
