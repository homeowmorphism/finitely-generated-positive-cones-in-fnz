module

public import FnZPositiveCones.External.CircularIsolatedComponents
public import FnZPositiveCones.External.FreeAbelianSubgroup
public import FnZPositiveCones.External.CircularIsolatedDiscrete

@[expose] public section

/-! The cyclic base component and the actual successor of an isolated order. -/
namespace FnZPositiveCones
namespace CircularRealization
open CircularDynamics
universe u
variable {ι : Type u} [Nontrivial ι] {C : CircularGroupOrder (FreeGroup ι)}
variable (R : CircularRealization C)

/-- The real component has finite endpoints around the marked basepoint. -/
theorem baseFreeComponent_eq_Ioo
    (hi : IsOpen ({C} : Set (CircularGroupOrder (FreeGroup ι)))) :
    ∃ a b : ℝ, a < 0 ∧ 0 < b ∧ R.baseFreeComponent = Set.Ioo a b := by
  obtain ⟨q, hq, hq1, hcut, hcut'⟩ :=
    R.exists_period_cut_of_liftedFreeLocus_ne_univ hi R.liftedFreeLocus_ne_univ
  have hJ := R.baseFreeComponent_subset_period hi hq hq1 hcut hcut'
  have hcomp : IsCompact (closure R.baseFreeComponent) :=
    isCompact_Icc.of_isClosed_subset isClosed_closure
      (closure_minimal (hJ.trans Set.Ioo_subset_Icc_self) isClosed_Icc)
  obtain ⟨a, b, hab, hI, _⟩ := open_connected_real_eq_Ioo R.isOpen_baseFreeComponent
    (R.isConnected_baseFreeComponent hi) hcomp
  have hzero : 0 ∈ R.baseFreeComponent := mem_connectedComponentIn (R.zero_mem_liftedFreeLocus hi)
  rw [hI] at hzero
  exact ⟨a, b, hzero.1, hzero.2, hI⟩

/-- The marked free projection of the actual base-component stabilizer. -/
def baseComponentProjection :
    realSetStabilizer R.realLift.action R.baseFreeComponent →* FreeGroup ι :=
  (MonoidHom.fst _ _).comp (realSetStabilizer R.realLift.action R.baseFreeComponent).subtype

/-- No nontrivial central translation preserves this bounded component, so its
free projection is injective. -/
theorem baseComponentProjection_injective
    (hi : IsOpen ({C} : Set (CircularGroupOrder (FreeGroup ι)))) :
    Function.Injective R.baseComponentProjection := by
  apply (injective_iff_map_eq_one R.baseComponentProjection).mpr
  intro g hg
  have hfst : g.val.1 = 1 := hg
  obtain ⟨a, b, ha, hb, hI⟩ := R.baseFreeComponent_eq_Ioo hi
  have hab := ha.trans hb
  have hset : R.realLift.action g.val '' R.baseFreeComponent = R.baseFreeComponent := g.property
  have hset' : R.realLift.action g.val '' Set.Ioo a b = Set.Ioo a b :=
    (congrArg (fun S : Set ℝ => R.realLift.action g.val '' S) hI).symm.trans (hset.trans hI)
  rw [(R.realLift.action g.val).image_Ioo] at hset'
  have hclosure := congrArg closure hset'
  rw [closure_Ioo ((R.realLift.action g.val).strictMono hab).ne, closure_Ioo hab.ne] at hclosure
  have hfix : R.realLift.action g.val a = a :=
    ((Set.Icc_eq_Icc_iff ((R.realLift.action g.val).monotone hab.le)).mp hclosure).1
  have hcentral : g.val = cofinalProductZ (FreeGroup ι) ^ g.val.2.toAdd := by
    apply Prod.ext
    · simpa [cofinalProductZ] using hfst
    · apply Multiplicative.toAdd.injective
      simp [cofinalProductZ]
  rw [hcentral, R.central_zpow_apply] at hfix
  have hn : g.val.2.toAdd = 0 := by exact_mod_cast (show (g.val.2.toAdd : ℝ) = 0 by linarith)
  apply Subtype.ext
  rw [hcentral, hn, zpow_zero]
  rfl

/-- The component stabilizer is cyclic, by the actual injective free projection
and its derived commutativity. No finite-generation assumption enters. -/
theorem baseComponentStabilizer_isCyclic
    (hi : IsOpen ({C} : Set (CircularGroupOrder (FreeGroup ι)))) :
    IsCyclic (realSetStabilizer R.realLift.action R.baseFreeComponent) := by
  let f := R.baseComponentProjection
  have hc : ∀ a b : f.range, Commute a b := by
    intro a b
    obtain ⟨g, rfl⟩ := f.rangeRestrict_surjective a
    obtain ⟨h, rfl⟩ := f.rangeRestrict_surjective b
    exact (R.baseComponentStabilizer_commute hi g h).map f.rangeRestrict
  have hr : IsCyclic f.range := freeSubgroup_isCyclic_of_commute _ hc
  exact (MonoidHom.ofInjective (R.baseComponentProjection_injective hi)).isCyclic.mpr hr

include R in
/-- An isolated circular order on a nonabelian free group has an actual
successor. The proof uses local freeness, its cyclic component stabilizer,
and the tight gap property; finite positive generation is not assumed. -/
theorem isolated_has_successor
    (hi : IsOpen ({C} : Set (CircularGroupOrder (FreeGroup ι)))) :
    ∃ a : FreeGroup ι, C.IsSuccessor a := by
  let H := realSetStabilizer R.realLift.action R.baseFreeComponent
  let : IsCyclic H := R.baseComponentStabilizer_isCyclic hi
  let σ : H →* (ℝ ≃o ℝ) := R.realLift.action.comp H.subtype
  obtain ⟨ε, hε, hgap⟩ := OrderedActions.cyclic_real_orbit_right_gap σ 0
  obtain ⟨a, b, ha, hb, hI⟩ := R.baseFreeComponent_eq_Ioo hi
  let δ := min ε b
  have hδ : 0 < δ := lt_min hε hb
  have hlocal : ∀ g : FreeGroup ι × Multiplicative ℤ,
      ¬ (0 < R.realLift.action g 0 ∧ R.realLift.action g 0 < δ) := by
    intro g hg
    have hgJ : R.realLift.action g 0 ∈ R.baseFreeComponent := by
      rw [hI]
      exact ⟨ha.trans hg.1, hg.2.trans_le (min_le_right _ _)⟩
    have hgH : g ∈ H := (R.image_baseFreeComponent_eq_iff hi g).mpr hgJ
    apply hgap ⟨g, hgH⟩
    change 0 < R.realLift.action g 0 ∧ R.realLift.action g 0 < 0 + ε
    exact ⟨hg.1, by simpa only [zero_add] using hg.2.trans_le (min_le_left ε b)⟩
  obtain ⟨z, hz⟩ := R.realLift.exists_leastPositive_of_right_gap hδ (by
    intro g
    simpa only [R.base_zero, zero_add] using hlocal g)
  refine ⟨z.1, ?_⟩
  have hs := least_positive_gives_circular_successor R.liftOrder R.positive R.cofinal hz
  exact R.quotient_eq ▸ hs

end CircularRealization

/-- The isolated-order successor theorem for countable nonabelian free groups,
with the circular realization constructed internally. -/
theorem CircularGroupOrder.isolated_has_successor {ι : Type*} [Countable ι] [Nontrivial ι]
    (C : CircularGroupOrder (FreeGroup ι))
    (hi : IsOpen ({C} : Set (CircularGroupOrder (FreeGroup ι)))) :
    ∃ a : FreeGroup ι, C.IsSuccessor a := by
  obtain ⟨R⟩ := C.exists_circularRealization
  exact R.isolated_has_successor hi

end FnZPositiveCones
