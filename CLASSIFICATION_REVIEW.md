> Historical AI review of the snapshot identified below. This report is not
> a verification report for the current submission commit. Old namespaces,
> toolchains, and checkpoint statuses are preserved as written. Commit hashes and removed development files refer to the
> private development repository, not to this public snapshot.
> See [README.md](README.md) for current checks and
> [formalization.yaml](formalization.yaml) for review disclosure.

Independent review by `/root/classification_review`, 2026-09-21.

The new M01 declaration has the requested unconditional statement. I found no
mathematical contract defect in the finite normalized-domain, endpoint, invariant
gap-coordinate, or parity chain. This review concerns M01 and that replacement
odd-rank argument. It does not certify the stronger O00/O01 assertions about all
isolated orders, which remain separate obligations.

The exact endpoint checked by Lean is:

```lean
PositiveConesBlueprint.hasFGPositiveCone_iff_even :
  ∀ n : ℕ, 2 ≤ n →
    (HasFGPositiveCone (FreeGroup (Fin n) × Multiplicative ℤ) ↔ Even n)
```

The reverse implication uses the already proved
`PositiveConesBlueprint.evenRank_hasFGPositiveCone`. The forward implication uses
`even_of_hasFGPositiveCone`, whose only arguments are `n`, `2 ≤ n`, and the actual
finite positive-cone hypothesis. In particular, it does not accept
`OddRankObstructionGoal`, `CircularOddRankObstructionGoal`, cofinality, separation,
an assumed component graph, or an assumed gap-connectivity theorem.

The reviewed target definitions in `Interfaces.lean` are unchanged: a strict
positive cone is a `Subsemigroup`, excludes identity, and satisfies totality up
to inversion. `HasFGPositiveCone` uses a finite set and `Subsemigroup.closure`.
There is no commutativity assumption and no substitution of subgroup or monoid
generation. The new branch consumes those exact definitions through
`hasFGPositiveCone_exists_finiteNormalizedDomains`.

I traced the following points in the actual source:

1. `FiniteNormalizedDomains` records open regular domains, nonemptiness, actual
   finite `ConnectedComponents`, pairwise disjoint closures, avoidance of the
   basepoint by each closure, and the exact generator image of the complement of
   the inverse domain's closure. Every field is supplied by the checked FG
   construction. `CircularRealization` is a tight realization of an actual
   circular group order; its existence and successor are supplied, rather than
   assumed at the endpoint.
2. `CircularComponentEndpoints`, `CircularIntervalFamilies`, and
   `CircularComponentConfiguration` extract actual nondegenerate component
   intervals. Regular openness excludes a shared endpoint between components of
   one color; the domain separation field treats different colors. The cyclic
   permutation sorts these actual intervals. It does not assume their order or
   replace them with arbitrary finite labels.
3. `CircularEndpointMaps` derives endpoint orientation from preservation of
   circular order. The component bijections use the actual generator and its
   inverse. The local equation `backward (forward c) = positiveNext c` and
   `graph_endpoint` are proved consequences of those maps. This agrees with the
   component-cycle calculation of MMRT Proposition 2.8.
4. `CircularNormalizedOrbit.closure_letterOrbit_subset_domain` puts each entire
   first-letter orbit closure inside the corresponding **open** domain. Its
   cancellation proof uses the exact image equation, finite unions of the other
   closed domains, and basepoint avoidance. Consequently every domain frontier
   avoids the whole marked orbit closure. There is no premise that every domain
   component contains an orbit point.
5. There is a finite complementary interval containing the basepoint. The
   closure of every other such interval avoids both the basepoint and all open
   domains, hence avoids the entire orbit closure. Connectedness places that
   **closed** interval inside one actual successor gap. This includes intervals
   bordering any additional domain components.
6. `CircularGapCoordinate` defines a coordinate by moving a point from its
   uniquely labelled successor gap back to the identity gap. Disjointness of
   actual gaps proves independence of the chosen label. The action law proves
   invariance under every group element away from the orbit closure. An oriented
   closed segment contained in a gap has strictly increasing coordinates at its
   distinct endpoints; the proof verifies that its pullback avoids the circle
   coordinate cut.
7. `CircularGapConnectivity.gap_connected` applies this coordinate to the right
   endpoints of all finite component intervals. Traversing a nonbase
   complementary interval strictly increases it. `graph_endpoint` identifies
   the arriving endpoint with another departing endpoint by an actual group
   element, preserving the coordinate. Thus the finite permutation
   `graph⁻¹ * circle` has strict increase at every point except the base gap.
   `PingPongGapPotential.isCycleOn_of_increase_off_one` proves that every cycle
   must contain that exceptional point, so there is just one cycle.
8. The checked boundary-permutation parity calculation then gives
   `Even (Fintype.card ι)`. Substitution `ι = Fin n` gives the exact rank `n`,
   with no rank estimate or choice of a different generating set.

The invariant-coordinate step is a substantive replacement for the minimal-set
gap equivalence argument in [MMRT, Section 3.1](https://arxiv.org/abs/1709.02348).
I reread the cached primary text of that section and Proposition 2.8. The Lean
argument uses the complement of the **marked orbit closure**, whose gaps have
unique group labels, and a finite potential argument. It neither identifies
those finer gaps bijectively with the finite complementary intervals nor assumes
that the domains have no extra components. Such a bijection is unnecessary in
the implemented proof. The local component cycles and final parity calculation
retain the source correspondence. The argument proves the FG classification;
it does not by itself establish the cited general isolated-order theorem.

Verification used the original pins: Lean `v4.35.0-rc2` and mathlib
`dec5b2b780537b6eaf7f5e5f000c12f7387fb24d`. I inspected the pinned convex-interval
and finite-permutation APIs used by the new helpers. The coordinator's full
imported checkpoint 7 completed successfully with 9072 jobs. After the
coordinator confirmed completion, my independent `lake env lean --stdin` check
exited 0 (execution session 19798). It imported `PositiveConesBlueprint`, checked
the exact declarations and major helper signatures, and verified these uses:

```lean
example : ∀ n : ℕ, 2 ≤ n →
    (HasFGPositiveCone (FreeGroup (Fin n) × Multiplicative ℤ) ↔ Even n) :=
  hasFGPositiveCone_iff_even

example : HasFGPositiveCone (FreeGroup (Fin 2) × Multiplicative ℤ) :=
  (hasFGPositiveCone_iff_even 2 (by omega)).2 (by decide)

example : ¬ HasFGPositiveCone (FreeGroup (Fin 3) × Multiplicative ℤ) :=
  oddRank_noFGPositiveCone_unconditional 3 (by omega) (by decide)
```

`#print axioms` returned exactly `[propext, Classical.choice, Quot.sound]` for
M01, the unconditional odd-rank FG obstruction, `gap_connected`,
`gapCoordinate_action`, `gapCoordinate_lt_of_segment_subset`,
`closure_letterOrbit_subset_domain`, `graph_endpoint`, and
`even_of_connected_component_configuration`. No additional computational trust
mechanism is used. A source scan found no proof holes, project axioms, unsafe
declarations, or `native_decide` in the accepted project modules; the keyword
matches were explanatory comments.

The coordinator subsequently reported an ownership collision in the older
`CircularDynamicsPrincipalChain.lean` prerequisite and is reconciling that source
with its checked artifact. The evidence above covers checkpoint 7. A fresh full
build after reconciliation remains necessary for final acceptance of the exact
current tree. No source files were modified in this review except this report.

The only issue identified in the assigned scope was documentation lag: the M01
manifest entry and live status prose still described its earlier dependence on
O01. The coordinator is updating these with the replacement route while keeping
the original O00/O01 contracts explicitly open. Those original obligations, full
repository validation, and the final current-tree release audit remain outside
the completion claim of this review.

Post-reconciliation acceptance, 2026-09-21: the coordinator's fresh full imported
checkpoint 8 passed with 9072 jobs
(`build_logs/implementation-2026-09-21/integrated-checkpoint-8.log`). After that
build I reran the complete independent endpoint/helper/type/axiom check described
above against the current artifacts. `lake env lean --stdin` exited 0 (execution
session 10931). All displayed types and all eight critical axiom lists were
unchanged; the rank-two and rank-three applications passed again. This resolves
the earlier checkpoint-7 limitation for the reviewed M01 statement and proof
chain. The coordinator separately checks that the 21 reconciled PrincipalChain
declaration signatures agree with the previous artifact.

I then performed the requested bounded audit of every original source-table and
manifest proof contract. I matched the task families to their actual source
declarations, including helper statements beyond the single representative name
stored in many manifest entries. `lake env lean ManifestAudit.lean` exited 0
(execution session 48022) against checkpoint 8. In particular:

- C00–C05 and T00–T03 have the strict cone and topology contracts, right-coset
  laws, and nonempty positive Schreier generation. The closure induction retains
  an explicit identity alternative and excludes it using strict positivity.
- W00–W02 and G00–G15 include the right-action multiplication law, checked
  presented relators, six Schreier relations, all marked products, the actual
  inverse construction, and the exact `psi_C` word. Product free-group
  certificate identities are proved separately from identities in Gamma2.
- E00–E02 prove the exact identity exclusion and totality goals. H00–H01 retain
  only the intended `BaseConeGoal` premise, discharged at M00.
- D00–D03 include all positive moduli, the index calculation, the odd-modulus
  unit proof via coprimality, and both covering and disjointness of the two
  even-modulus orbits. Optional D04–D05 also have their coordinate/path proofs.
- B00–B06 include both weighted inverse identities and the explicit basis,
  followed by `coverRankEquiv : coverSubgroup d ≃* FreeGroup (Fin (d + 1))`.
- K00–K07 retain the actual subgroup of Gamma's subgroup, its index and checked
  product equivalence, all positive Schreier factors, and the conditional
  construction. The optional bounded finite witness, M02, and the exact M00
  endpoint are present.
- O02 and O03 are correctly conditional statements. M01 now has the stronger
  unconditional implementation reviewed above, using the documented replacement
  route. A00 and A01 have recorded successful checks; A01's Python certificate
  and bounded regression data explicitly state that they are not Lean proofs.

No additional unfinished mathematical obligation was identified beyond the
original O00 and O01. The precise residual claims are:

```lean
LeftOrderOddRankObstructionGoal :=
  ∀ n : ℕ, 2 ≤ n → Odd n →
    ∀ O : LeftGroupOrder (FnZ n),
      ¬ IsOpen ({O} : Set (LeftGroupOrder (FnZ n)))

OddRankObstructionGoal :=
  ∀ n : ℕ, 2 ≤ n → Odd n →
    ∀ P : Subsemigroup (FnZ n), IsPositiveCone P → ¬ FinitelyDetermined P
```

Their existing adapter is proved conditionally. The original external route
still needs its isolated circular-order obstruction and isolated-order central
cofinality inputs, or another proof of those exact stronger conclusions. Neither
follows merely from the FG-specific M01 endpoint. A02 remains the coordinator's
release obligation, including final live documentation and manifest consistency.
At the time of this audit, M01's old pending status and original O01-dependent
proof plan were still visible in those documents. They are stale records to
correct, not additional absent Lean theorems. No manifest or source-table file
was edited by this reviewer.
