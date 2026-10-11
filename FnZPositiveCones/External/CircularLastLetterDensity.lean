module

public import FnZPositiveCones.External.CircularLastLetterDynamics
public import FnZPositiveCones.External.CircularIsolatedSuccessor
public import FnZPositiveCones.External.CircularSuccessorAccumulation
public import FnZPositiveCones.External.CofinalIsolationReverse
public import FnZPositiveCones.External.CyclicConvexSubgroups
public import FnZPositiveCones.External.CircularInvariantComponents
public import FnZPositiveCones.External.CircularDerivedTransfer
public import FnZPositiveCones.External.CircularInvariantAccumulation

@[expose] public section

/-! Isolation forces the actual last-letter accumulation sets to contain every
orbit accumulation point. The argument uses convex component stabilizers,
without assuming a minimal invariant set or excluding finite orbits. -/

namespace FnZPositiveCones.CircularRealization

open CircularDynamics

universe u
variable {ι : Type u} {C : CircularGroupOrder (FreeGroup ι)} (R : CircularRealization C)

/-- A complementary component of a nonempty closed invariant set avoiding
the basepoint has cyclic stabilizer when the circular order is isolated. -/
theorem invariantComponentStabilizer_isCyclic [Finite ι]
    (hi : IsOpen ({C} : Set (CircularGroupOrder (FreeGroup ι))))
    {S : Set StandardCircle} (hS : IsClosed S) (hne : S.Nonempty) (h0 : 0 ∉ S)
    (hinv : ∀ g, R.action g '' S = S) : IsCyclic (R.invariantComponentStabilizer S) := by
  have hfd : FinitelyDetermined (leftOrderCone R.liftOrder).1 :=
    (finiteDetermination_iff_leftOrder_isolated (leftOrderCone R.liftOrder)).mpr
      (by simpa only [coneLeftOrder_leftOrderCone] using
        CofinalIsolationReverse.liftOrder_isolated R hi)
  exact CyclicConvexSubgroups.convex_isCyclic_of_injective_free_hom
    (leftOrderCone R.liftOrder) hfd (R.invariantComponentStabilizer S)
    (R.invariantComponentStabilizer_convex h0 hinv)
    (R.invariantComponentProjection S)
    (R.invariantComponentProjection_injective hS hne h0)

/-- Every last-letter accumulation set is nonempty, by compactness and the
infinite freely marked orbit. -/
theorem lastLetter_derived_nonempty (t : ι × Bool) :
    (derivedSet (lastLetterOrbit (realizationGenerators R) 0 t)).Nonempty := by
  apply lastLetterOrbit_derived_nonempty
  simpa only [realizationGenerators_lift] using R.orbit_injective

/-- The actual last-letter accumulation set is invariant under the entire
free group. -/
theorem lastLetter_derived_invariant (t : ι × Bool) (g : FreeGroup ι) :
    R.action g '' derivedSet (lastLetterOrbit (realizationGenerators R) 0 t) =
      derivedSet (lastLetterOrbit (realizationGenerators R) 0 t) := by
  have hc : ∀ s, Continuous (letterPerm (realizationGenerators R) s) := by
    intro s
    rw [realizationGenerators_letter]
    exact R.action_continuous _
  simpa only [realizationGenerators_lift] using
    lastLetterOrbit_derived_invariant (realizationGenerators R) 0 hc t g

/-- The successor furnished by isolation excludes the basepoint from every
last-letter accumulation set. -/
theorem zero_not_mem_lastLetter_derived [Nontrivial ι]
    (hi : IsOpen ({C} : Set (CircularGroupOrder (FreeGroup ι)))) (t : ι × Bool) :
    (0 : StandardCircle) ∉ derivedSet (lastLetterOrbit (realizationGenerators R) 0 t) := by
  obtain ⟨h, hh⟩ := R.isolated_has_successor hi
  intro hzero
  have hacc := lastLetterOrbit_derived_subset_orbit (realizationGenerators R) 0 t hzero
  simp only [realizationGenerators_lift] at hacc
  apply R.not_accPt_orbit_of_successor hh 1
  simpa only [map_one, Equiv.Perm.one_apply, mem_derivedSet] using hacc

/-- Every nonempty closed invariant set avoiding the marked basepoint
contains the full orbit's accumulation set for an isolated circular order. -/
theorem derived_orbit_subset_closed_invariant [Finite ι]
    (hi : IsOpen ({C} : Set (CircularGroupOrder (FreeGroup ι))))
    {S : Set StandardCircle} (hS : IsClosed S) (hne : S.Nonempty) (h0 : 0 ∉ S)
    (hinv : ∀ g, R.action g '' S = S) :
    derivedSet (Set.range (fun g => R.action g 0)) ⊆ S := by
  let := R.invariantComponentStabilizer_isCyclic hi hS hne h0 hinv
  exact R.circle_orbit_derived_subset_of_baseComponent hS h0 hinv
    (R.derived_real_orbit_disjoint_baseComponent_of_cyclic hS hne h0 hinv)

/-- Each last-letter orbit has exactly the same accumulation set as the
full marked orbit. Isolation is the only dynamical hypothesis. -/
theorem derived_orbit_eq_lastLetter_derived [Finite ι] [Nontrivial ι]
    (hi : IsOpen ({C} : Set (CircularGroupOrder (FreeGroup ι)))) (t : ι × Bool) :
    derivedSet (Set.range (fun g => R.action g 0)) =
      derivedSet (lastLetterOrbit (realizationGenerators R) 0 t) := by
  apply Set.Subset.antisymm
  · exact R.derived_orbit_subset_closed_invariant hi
      (lastLetterOrbit_derived_isClosed (realizationGenerators R) 0 t)
      (R.lastLetter_derived_nonempty t) (R.zero_not_mem_lastLetter_derived hi t)
      (R.lastLetter_derived_invariant t)
  · simpa only [realizationGenerators_lift] using
      lastLetterOrbit_derived_subset_orbit (realizationGenerators R) 0 t

/-- Every actual last-letter orbit accumulates densely on the full orbit's
accumulation set. This supplies the density input for isolated-order
first-letter separation without any positive-generation assumption. -/
theorem derived_orbit_subset_lastLetterClosure [Finite ι] [Nontrivial ι]
    (hi : IsOpen ({C} : Set (CircularGroupOrder (FreeGroup ι)))) (t : ι × Bool) :
    derivedSet (Set.range (fun g => R.action g 0)) ⊆
      closure (lastLetterOrbit (realizationGenerators R) 0 t) := by
  rw [R.derived_orbit_eq_lastLetter_derived hi t]
  exact derivedSet_subset_closure _

end FnZPositiveCones.CircularRealization
