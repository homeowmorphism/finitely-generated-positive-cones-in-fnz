> Historical AI review of the snapshot identified below. This report is not
> a verification report for the current submission commit. Old namespaces,
> toolchains, and checkpoint statuses are preserved as written. Commit hashes and removed development files refer to the
> private development repository, not to this public snapshot.
> See [README.md](README.md) for current checks and
> [formalization.yaml](formalization.yaml) for review disclosure.

# Independent review: noncofinal endpoint action

The proposed endpoint construction is mathematically valid. This review was
requested before the new source modules were released; the declaration and
axiom audit will be added after their direct compilation.

Let `O` be a left order on `FreeGroup ι × Multiplicative ℤ`, realized tightly by
an action `ρ` on the real line. If the marked central generator is not
cofinal, its moving component at the marked point has a finite endpoint `l`.
The central generator fixes `l`.

The key hypothesis at this endpoint is **weak monotonicity**:
`O.order.le g h → ρ g l ≤ ρ h l`. Centrality permits right multiplication by
every integer power of the center in the original order. Apply the original
order realization to those inequalities and take the infimum of the power
orbit. Each acting order isomorphism preserves the corresponding infimum.
This proves weak monotonicity without claiming that the endpoint orbit is
free or realizes the original order by an equivalence.

Weak monotonicity is enough to recover `O` by `O.actionCompletion ρ l`:
totality rules out a strict orbit comparison opposite to `O`, and equal orbit
values are resolved by `O` itself. The existing stronger realization adapter
must not be invoked with an unproved converse inequality at `l`.

Restricting the original action to the free factor and extending it with the
center acting trivially preserves every orbit evaluation at `l`. The original
center fixes `l`, and centrality makes it fix its entire group orbit. This
orbit is unbounded above: a bounded orbit would have an invariant supremum,
which would be a global fixed point of the tight action.

For a finite set of endpoint orbit tests, the finite-edge perturbation can
preserve those tests and produce two actions with opposite strict movement
for one common nontrivial word `k = g⁻¹ * of i * g`. Choose `g` to first leave
the bounded protected trace region and choose `i` different from the last
acted generator. Both perturbations preserve the reaching trajectory; the
chosen generator sends its final point to opposite sides, still beyond all
protected edge outputs and their preimages. This preserves inverse-letter
constraints as well as positive-letter constraints.

After extending both perturbed free-factor actions with trivial center,
complete each using `O` to resolve ties. Every tested original positive is
still positive: strict endpoint displacement is preserved, and zero
displacement is resolved by the original order. The common word `k` has
opposite signs in the two completions. Thus they cannot both equal an
isolated `O`.

No changed-basis trajectory bound, far primitive fixed point, primitive
cofinality assumption, or subgroup-tower hypothesis enters this argument.

Status: mathematical proof-contract review and exact compiled-artifact
declaration/axiom review both passed.

The released source has now been read independently. Its stronger endpoint
`NoncofinalEndpointAction.center_cofinal_of_isolated` assumes only
`[Nontrivial ι] [Countable ι]` and isolation of `O`. It imposes neither parity
nor a sign assumption on the marked center. The final adapter
`isolatedOddRankCenterCofinal` has exactly the supplied
`IsolatedOddRankCenterCofinalGoal` type.

The strengthened perturbation source fixes one word `k` before choosing the
target displacement. Its marker equation is
`σ g (σ k x) = target`, while the reaching-word equation is `σ g x = z`.
Strict monotonicity of `σ g` therefore supplies both motion equivalences.
This verifies that the two completed orders disagree on the same element,
without assuming the original endpoint orbit is free.

After the coordinator rebuilt `NoncofinalEndpointAction`, the independent
command `lake env lean --stdin` imported that module and printed the eight
critical contracts, the supplied goal definition, and seven axiom reports.
It exited 0 (session 42518). All seven audited declarations use exactly
`propext`, `Classical.choice`, and `Quot.sound`. The saved evidence is
`build_logs/implementation-2026-09-21/independent-endpoint-action-review.log`.
There are no remaining mathematical or declaration-shape objections in this
review. The circular separation branch remains a separate obligation.
