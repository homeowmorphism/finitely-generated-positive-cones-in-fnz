> Historical AI review of the snapshot identified below. This report is not
> a verification report for the current submission commit. Old namespaces,
> toolchains, and checkpoint statuses are preserved as written. Commit hashes and removed development files refer to the
> private development repository, not to this public snapshot.
> See [README.md](README.md) for current checks and
> [formalization.yaml](formalization.yaml) for review disclosure.

# Invariant-component accumulation review

Reviewer: cones worker. Implementation owner: root coordinator.

The source proof of `CircularRealization.derived_real_orbit_disjoint_baseComponent_of_cyclic` is mathematically sound under its displayed hypotheses. The review found no missing freeness, finite-generation, minimality, or finite-orbit hypothesis.

The theorem assumes a `CircularRealization C` for a circular order on `FreeGroup ι`, a closed nonempty invariant circle set `S` with `0 ∉ S`, and `IsCyclic (R.invariantComponentStabilizer S)`. It concludes that the derived set of the actual real orbit is disjoint from `complementBaseComponent S`. The stabilizer is the actual subgroup of `FreeGroup ι × Multiplicative ℤ` preserving this real component. It is not replaced by its projected image.

The critical proof steps were checked against the upstream definitions:

- `mem_invariantComponentStabilizer_iff` proves the exact equality between the orbit inside the base component and the stabilizer orbit of zero.
- The component is open. Restricting a full-orbit accumulation point to this neighborhood therefore gives a stabilizer-orbit accumulation point, using `AccPt.nhds_inter`.
- `cyclic_real_orbit_derived_fixed` makes that point fixed by every stabilizer element. This theorem permits a nonfaithful action.
- If the point is positive, strict monotonicity places every stabilizer orbit point below it. A point just to its right, still inside the component, lies outside the full orbit closure. The tight realization supplies a gap with actual orbit endpoints. Its left endpoint must lie between the accumulation point and the chosen point. That endpoint is still in the component, contradicting the stabilizer-orbit bound.
- The negative case uses the right gap endpoint and the reverse inequalities. At zero, the stabilizer orbit is a singleton, which has no accumulation point.

The gap argument uses the precise `TightRealization.orbit_gap` contract. Merely knowing that the real action induces the order would not supply the required orbit endpoints. The closed, nonempty invariant set supplies a bounded open component through the periodic circle covering.

This lemma supports the replacement of the unique-minimal-set argument in the last-letter density proof. It does not establish cyclicity from isolation; that remains a separate upstream theorem.

Independent source audit: `lake env lean /private/tmp/InvariantComponentDraftReview.lean` passed with exit code 0. The printed signature has exactly the hypotheses listed above. `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`. The audit copied the coordinator's current scratch source without modifying it. The final import audit, `lake env lean /private/tmp/InvariantComponentArtifactReview.lean`, also passed with exit code 0. It includes an explicit contract-shaped `example`, checks the exported declaration type, and repeats the axiom audit against the built artifact. The artifact audit reports the same three foundational axioms. No implementation files were edited during this review.
