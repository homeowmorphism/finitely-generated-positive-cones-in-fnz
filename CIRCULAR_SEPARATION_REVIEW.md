> Historical AI review of the snapshot identified below. This report is not
> a verification report for the current submission commit. Old namespaces,
> toolchains, and checkpoint statuses are preserved as written. Commit hashes and removed development files refer to the
> private development repository, not to this public snapshot.
> See [README.md](README.md) for current checks and
> [formalization.yaml](formalization.yaml) for review disclosure.

# Circular separation: proof repair and checked contracts

Mann–Rivas, Proposition 4.7, first refines two differently headed words using
their finite trajectories and then chooses a perturbation supported near the
resulting interval. Finite adjacency excludes proper-trajectory points only
from the open interval. A proper suffix of one endpoint can still equal the
other endpoint, so closed support avoidance requires an additional argument.
The repository's earlier trace lemmas identify this obstruction exactly.

Primary sources inspected:

- [Mann–Rivas, Proposition 4.7, pp. 1428–1429](https://aif.centre-mersenne.org/item/10.5802/aif.3191.pdf).
- [Matsumoto, Lemma 7.2, p. 1430](https://ems.press/content/serial-article-files/30075).

The new checked repair follows the last-letter insertion idea in the latter
source. After finite tail refinement, two endpoints with different last
letters cannot be suffixes of one another. If their last letters agree,
insert a shortest word ending in the inverse last letter. Its proper suffixes
cannot occur in the interval, by minimality. Retain whichever of the two
subintervals has different first letters. This proves closed avoidance of
every proper suffix of both retained endpoints.

The four implementation files are:

- `External/CircularSuffixSeparation.lean`: the finite word argument, with an
  explicit prescribed-last-letter density hypothesis for nested mixed-head
  intervals. The main declaration is
  `CircularDynamics.exists_closed_suffix_avoiding_pair`.
- `External/CircularIntervalAccumulation.lean`: compactness converts absence
  of actual mixed-color adjacent pairs into an interior accumulation point.
  The main declaration is
  `CircularDynamics.exists_accPt_between_of_no_mixed_adjacent`.
- `External/CircularSuccessorAccumulation.lean`: absence of all full-orbit
  points between two endpoints makes them actual successor labels. The
  checked principal-gap word bound then gives a finite bounded-word cutset.
  Outside it, `CircularRealization.exists_circle_accPt_of_mixed_heads_outside_cutset`
  produces an actual circle accumulation point inside the interval.
- `External/CircularIsolatedSeparation.lean`: the full assembly from global
  last-letter density, actual successor, and isolation. It constructs a
  `CrossingConfig` avoiding protected traces and both complete proper
  trajectories. A finite cutset and the checked closure-separation adapter
  yield pairwise disjoint first-letter closures.

The final declaration is
`CircularRealization.firstLetter_closures_disjoint_of_isolated_of_lastLetter_density`.
Its assumptions are `[Finite ι]`, a `CircularRealization C`, `IsOpen {C}`, an
actual `C.IsSuccessor h`, and

```lean
∀ t : ι × Bool,
  derivedSet (Set.range (fun g => R.action g 0)) ⊆
    closure (lastLetterOrbit (realizationGenerators R) 0 t)
```

There is no finite semigroup generation assumption and no assumed trace
avoidance, component connectivity, or conversion of finite adjacency into
full-orbit adjacency. The displayed global density input is a separate
implementation branch; this file does not claim to prove it.

All four literal source files passed direct `lake env lean` checks at the
pinned environment, without warnings (sessions 14921, 9254, 41247, and
84665). Exact statement and axiom audits also passed. Every audited proof
uses only `propext`, `Classical.choice`, and `Quot.sound`, with the elementary
last-suffix identity using only `propext`. The saved final assembly evidence
is `build_logs/implementation-2026-09-21/independent-isolated-separation-audit.log`
(exit 0, session 65475); the actual successor/accumulation audit is
`build_logs/implementation-2026-09-21/independent-successor-accumulation-audit.log`
(exit 0, session 81734).

Source files are frozen and released to the coordinator for full imported
builds and an independent review of the assembled density branch.
