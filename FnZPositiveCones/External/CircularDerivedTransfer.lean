module

public import FnZPositiveCones.External.CircularInvariantComponents
public import Mathlib.Topology.DerivedSet

@[expose] public section

/-! Transfer of actual orbit accumulation through the circle covering map and
through invariant complementary components. -/
namespace FnZPositiveCones
namespace CircularDynamics

/-- An open map lifts accumulation of a set to every point over an accumulation
point. The inverse image set, rather than merely its closure, is used here. -/
theorem IsOpenMap.preimage_derivedSet_subset {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}
    (hf : IsOpenMap f) (S : Set Y) :
    f ⁻¹' derivedSet S ⊆ derivedSet (f ⁻¹' S) := by
  intro x hx
  apply accPt_iff_nhds.mpr
  intro U hU
  obtain ⟨y, ⟨⟨z, hz, hzy⟩, hy⟩, hyx⟩ :=
    accPt_iff_nhds.mp hx (f '' U) (hf.image_mem_nhds hU)
  refine ⟨z, ⟨hz, ?_⟩, ?_⟩
  · change f z ∈ S
    exact hzy.symm ▸ hy
  · intro hzx
    exact hyx (hzy.symm.trans (congrArg f hzx))

end CircularDynamics
namespace CircularRealization
open CircularDynamics
universe u
variable {G : Type u} [Group G] {C : CircularGroupOrder G} (R : CircularRealization C)

/-- Every real lift of an actual circular orbit accumulation point is itself
an accumulation point of the real orbit. -/
theorem real_orbit_accPt_of_circle (x : ℝ)
    (hx : (x : StandardCircle) ∈ derivedSet (Set.range (fun g => R.action g 0))) :
    x ∈ derivedSet (Set.range (fun g => R.realLift.action g 0)) := by
  have hh := IsOpenMap.preimage_derivedSet_subset
    (show IsOpenMap ((↑) : ℝ → StandardCircle) from QuotientAddGroup.isOpenMap_coe)
    (Set.range (fun g => R.action g 0)) hx
  rw [R.preimage_circle_orbit, R.base_zero] at hh
  exact hh

/-- Every element of the actual real action preserves its orbit's accumulation
set. This uses continuity and injectivity of the order automorphism. -/
theorem real_orbit_derived_mapsTo (g : G × Multiplicative ℤ) :
    Set.MapsTo (R.realLift.action g)
      (derivedSet (Set.range (fun h => R.realLift.action h 0)))
      (derivedSet (Set.range (fun h => R.realLift.action h 0))) := by
  intro x hx
  apply derivedSet_mono _ _ ?_
    ((R.realLift.action g).continuous.image_derivedSet (R.realLift.action g).injective
      ⟨x, hx, rfl⟩)
  rintro y ⟨z, ⟨h, rfl⟩, rfl⟩
  exact ⟨g * h, by simp only [map_mul, RelIso.mul_apply]⟩

end CircularRealization
namespace CircularRealization
open CircularDynamics
universe u
variable {ι : Type u} {C : CircularGroupOrder (FreeGroup ι)} (R : CircularRealization C)

/-- A complementary component containing an orbit accumulation point contains
an actual orbit point and is its translate of the base component. -/
theorem exists_translate_baseComponent_of_derived
    {S : Set StandardCircle} (hS : IsClosed S) (h0 : 0 ∉ S)
    (hinv : ∀ g, R.action g '' S = S) {p : ℝ}
    (hp : p ∈ derivedSet (Set.range (fun g => R.realLift.action g 0)))
    (hpS : p ∈ liftedComplement S) :
    ∃ g : FreeGroup ι × Multiplicative ℤ,
      p ∈ R.realLift.action g '' complementBaseComponent S := by
  have hopen := (isOpen_liftedComplement hS).connectedComponentIn (x := p)
  have hpmem := mem_connectedComponentIn hpS
  obtain ⟨q, hq, g, hg⟩ := mem_closure_iff.mp (derivedSet_subset_closure _ hp)
    (connectedComponentIn (liftedComplement S) p) hopen hpmem
  have hzero : (0 : ℝ) ∈ liftedComplement S := by
    simpa only [liftedComplement, Set.mem_preimage, Set.mem_compl_iff,
      AddCircle.coe_zero] using h0
  have himage := (R.realLift.action g).toHomeomorph.image_connectedComponentIn hzero
  change R.realLift.action g '' complementBaseComponent S =
    connectedComponentIn (R.realLift.action g '' liftedComplement S)
      (R.realLift.action g 0) at himage
  rw [R.image_invariant_liftedComplement hinv] at himage
  have hcomp : connectedComponentIn (liftedComplement S) p =
      connectedComponentIn (liftedComplement S) (R.realLift.action g 0) := by
    apply connectedComponentIn_eq
    change R.realLift.action g 0 = q at hg
    rw [hg]
    exact hq
  refine ⟨g, ?_⟩
  rw [himage, ← hcomp]
  exact hpmem

/-- Excluding derived real orbit points from the single base component excludes
them from every complementary component. No cyclicity is assumed here. -/
theorem circle_orbit_derived_subset_of_baseComponent
    {S : Set StandardCircle} (hS : IsClosed S) (h0 : 0 ∉ S)
    (hinv : ∀ g, R.action g '' S = S)
    (hdisj : Disjoint (derivedSet (Set.range (fun g => R.realLift.action g 0)))
      (complementBaseComponent S)) :
    derivedSet (Set.range (fun g => R.action g 0)) ⊆ S := by
  intro x hx
  by_contra hxS
  obtain ⟨p, rfl⟩ := QuotientAddGroup.mk_surjective x
  have hp := R.real_orbit_accPt_of_circle p hx
  obtain ⟨g, q, hq, hqp⟩ := R.exists_translate_baseComponent_of_derived hS h0 hinv hp hxS
  have hqacc := R.real_orbit_derived_mapsTo g⁻¹ hp
  have hinv : R.realLift.action g⁻¹ p = q := by
    rw [← hqp, map_inv]
    exact (R.realLift.action g).symm_apply_apply q
  rw [hinv] at hqacc
  exact Set.disjoint_left.mp hdisj hqacc hq

end CircularRealization
end FnZPositiveCones
