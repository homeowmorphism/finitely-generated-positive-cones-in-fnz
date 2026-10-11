module

public import FnZPositiveCones.External.OrderedActionsGaps
public import Mathlib.Topology.Algebra.Group.Quotient

@[expose] public section

namespace FnZPositiveCones
namespace CircularRealization
universe u
variable {G : Type u} [Group G] {C : CircularGroupOrder G} (R : CircularRealization C)

/-- Integer central powers act by the corresponding integer translations. -/
theorem central_zpow_apply (n : ℤ) (x : ℝ) :
    R.realLift.action (cofinalProductZ G ^ n) x = x + (n : ℝ) := by
  induction n using Int.induction_on generalizing x with
  | zero => simp
  | succ n ih =>
    rw [zpow_add, map_mul, RelIso.mul_apply, zpow_one, R.central_translation, ih]
    push_cast
    ring
  | pred n ih =>
    have hInv : (R.realLift.action (cofinalProductZ G))⁻¹ x = x - 1 := by
      apply (R.realLift.action (cofinalProductZ G)).injective
      rw [RelIso.apply_inv_self, R.central_translation]
      ring
    rw [zpow_sub, map_mul, RelIso.mul_apply, zpow_one, map_inv, hInv, ih]
    push_cast
    ring

/-- Quotienting any product action forgets exactly the central coordinate. -/
theorem coe_real_action (g : G × Multiplicative ℤ) (x : ℝ) :
    (R.realLift.action g x : AddCircle (1 : ℝ)) = R.action g.1 x := by
  have hg : g = cofinalProductZ G ^ g.2.toAdd * (g.1, 1) := by
    apply Prod.ext
    · simp [cofinalProductZ]
    · apply Multiplicative.toAdd.injective
      simp [cofinalProductZ]
  conv_lhs => rw [hg, map_mul, RelIso.mul_apply, R.central_zpow_apply]
  change ((R.realLift.action (g.1, 1) x + (g.2.toAdd : ℝ) : ℝ) : AddCircle (1 : ℝ)) = _
  rw [AddCircle.coe_add]
  have hn : ((g.2.toAdd : ℝ) : AddCircle (1 : ℝ)) = 0 :=
    (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr ⟨g.2.toAdd, by simp⟩
  rw [hn, add_zero]
  rfl

/-- The real orbit is the full inverse image of the circular orbit. -/
theorem preimage_circle_orbit :
    ((↑) : ℝ → AddCircle (1 : ℝ)) ⁻¹' Set.range (fun g => R.action g 0) =
      Set.range (fun g => R.realLift.action g R.realLift.base) := by
  ext x
  constructor
  · rintro ⟨g, hg⟩
    have he : (R.realLift.action (g, 1) 0 : AddCircle (1 : ℝ)) = (x : AddCircle (1 : ℝ)) :=
      (R.coe_real_action (g, 1) 0).trans hg
    have hz : ((x - R.realLift.action (g, 1) 0 : ℝ) : AddCircle (1 : ℝ)) = 0 := by
      rw [AddCircle.coe_sub, he, sub_self]
    obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hz
    refine ⟨cofinalProductZ G ^ n * (g, 1), ?_⟩
    dsimp only
    rw [map_mul, RelIso.mul_apply, R.central_zpow_apply, R.base_zero]
    simp only [zsmul_eq_mul, mul_one] at hn
    linarith
  · rintro ⟨g, rfl⟩
    refine ⟨g.1, ?_⟩
    rw [R.base_zero]
    exact (R.coe_real_action g 0).symm

/-- The covering projection reflects closure of these invariant orbit sets. -/
theorem preimage_circle_orbit_closure :
    ((↑) : ℝ → AddCircle (1 : ℝ)) ⁻¹' closure (Set.range (fun g => R.action g 0)) =
      closure (Set.range (fun g => R.realLift.action g R.realLift.base)) := by
  rw [QuotientAddGroup.isOpenMap_coe.preimage_closure_eq_closure_preimage
    (AddCircle.continuous_mk' (1 : ℝ)), R.preimage_circle_orbit]



/-- The marked circular action consists of homeomorphisms. -/
noncomputable def actionHomeomorph (g : G) : AddCircle (1 : ℝ) ≃ₜ AddCircle (1 : ℝ) where
  toEquiv := R.action g
  continuous_toFun := R.action_continuous g
  continuous_invFun := by
    convert R.action_continuous g⁻¹ using 1
    rw [map_inv]
    rfl

/-- The actual open gap following the orbit point labelled by g. -/
def circleGap (a g : G) : Set (AddCircle (1 : ℝ)) :=
  R.action g '' (((↑) : ℝ → AddCircle (1 : ℝ)) ''
    Set.Ioo 0 (OrderedActions.representativeOrbit R.realLift R.positive R.cofinal a))

theorem representativeOrbit_pos {a : G} (ha : C.IsSuccessor a) :
    0 < OrderedActions.representativeOrbit R.realLift R.positive R.cofinal a := by
  let := R.liftOrder.order
  have hh := (R.leastPositive_of_successor ha).1
  have hlt : R.realLift.action 1 R.realLift.base < R.realLift.action
      (cofinalProductRepresentative R.liftOrder R.positive R.cofinal a) R.realLift.base := by
    rw [lt_iff_not_ge, ← R.realLift.order_iff]
    exact not_le_of_gt hh
  simpa only [R.base_zero, map_one, RelIso.one_apply, OrderedActions.representativeOrbit] using hlt

theorem circleGap_nonempty {a : G} (ha : C.IsSuccessor a) (g : G) :
    (R.circleGap a g).Nonempty :=
  ((Set.nonempty_Ioo.mpr (R.representativeOrbit_pos ha)).image _).image _

theorem circleGap_isOpen (a g : G) : IsOpen (R.circleGap a g) :=
  (R.actionHomeomorph g).isOpenMap _ (QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo)

theorem circleGap_preconnected (a g : G) : IsPreconnected (R.circleGap a g) :=
  (isPreconnected_Ioo.image _ (AddCircle.continuous_mk' (1 : ℝ)).continuousOn).image _
    (R.action_continuous g).continuousOn

theorem circle_orbitClosure_mapsTo (g : G) :
    Set.MapsTo (R.action g) (closure (Set.range (fun k => R.action k 0)))
      (closure (Set.range (fun k => R.action k 0))) := by
  intro x hx
  apply closure_mono (s := R.action g '' Set.range (fun k => R.action k 0)) ?_
    (mem_closure_image (R.action_continuous g).continuousAt hx)
  rintro _ ⟨_, ⟨h, rfl⟩, rfl⟩
  exact ⟨g * h, by simp only [map_mul, Equiv.Perm.mul_apply]⟩

theorem circleGap_disjoint_orbitClosure {a : G} (ha : C.IsSuccessor a) (g : G) :
    Disjoint (R.circleGap a g) (closure (Set.range (fun k => R.action k 0))) := by
  let := R.liftOrder.order
  have hd : Disjoint
      (Set.Ioo 0 (OrderedActions.representativeOrbit R.realLift R.positive R.cofinal a))
      (closure (Set.range (fun k => R.realLift.action k R.realLift.base))) := by
    apply Disjoint.closure_right _ isOpen_Ioo
    rw [Set.disjoint_left]
    rintro _ ⟨hpos, hlt⟩ ⟨k, rfl⟩
    have hk : R.liftOrder.order.lt 1 k := by
      rw [lt_iff_not_ge, R.realLift.order_iff]
      simpa only [map_one, RelIso.one_apply, R.base_zero] using not_le_of_gt hpos
    have hh := (R.realLift.order_iff _ _).mp ((R.leastPositive_of_successor ha).2 k hk)
    exact hlt.not_ge (by simpa only [R.base_zero, OrderedActions.representativeOrbit] using hh)
  rw [Set.disjoint_left]
  rintro _ ⟨_, ⟨t, ht, rfl⟩, rfl⟩ hx
  have hh := R.circle_orbitClosure_mapsTo g⁻¹ hx
  rw [map_inv] at hh
  change (R.action g).symm (R.action g (t : AddCircle (1 : ℝ))) ∈
    closure (Set.range (fun k => R.action k 0)) at hh
  rw [Equiv.symm_apply_apply] at hh
  have hh' : t ∈ closure (Set.range (fun k => R.realLift.action k R.realLift.base)) := by
    rw [← R.preimage_circle_orbit_closure]
    exact hh
  exact Set.disjoint_left.mp hd ht hh'

/-- Every complementary point lies in an actual translate of the successor gap. -/
theorem exists_mem_circleGap {a : G} (ha : C.IsSuccessor a)
    {x : AddCircle (1 : ℝ)} (hx : x ∉ closure (Set.range (fun g => R.action g 0))) :
    ∃ g : G, x ∈ R.circleGap a g := by
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective x
  have ht : t ∉ closure (Set.range (fun g => R.realLift.action g R.realLift.base)) := by
    rw [← R.preimage_circle_orbit_closure]
    exact hx
  obtain ⟨g, hg, hhi, _⟩ := R.real_gap_is_translate ha ht
  let y := R.realLift.action g⁻¹ t
  have hy : y ∈ Set.Ioo 0
      (OrderedActions.representativeOrbit R.realLift R.positive R.cofinal a) := by
    constructor
    · simpa only [y, map_inv, RelIso.inv_apply_self, R.base_zero, OrderedActions.representativeOrbit] using
        (R.realLift.action g⁻¹).strictMono hg
    · simpa only [y, map_inv, RelIso.inv_apply_self, R.base_zero, OrderedActions.representativeOrbit] using
        (R.realLift.action g⁻¹).strictMono hhi
  refine ⟨g.1, (y : AddCircle (1 : ℝ)), ⟨y, hy, rfl⟩, ?_⟩
  rw [← R.coe_real_action g y]
  dsimp only [y]
  simp only [map_inv, RelIso.apply_inv_self]

theorem circleGap_transport (a g h : G) :
    R.circleGap a (g * h) = R.action g '' R.circleGap a h := by
  simp only [circleGap, map_mul, Equiv.Perm.mul_apply, Set.image_image]



/-- A real interval between the two lifted endpoints projects into the marked gap. -/
theorem mem_circleGap_of_real_interval (a : G) (g : G × Multiplicative ℤ) {t : ℝ}
    (hlo : R.realLift.action g 0 < t)
    (hhi : t < R.realLift.action g
      (OrderedActions.representativeOrbit R.realLift R.positive R.cofinal a)) :
    (t : AddCircle (1 : ℝ)) ∈ R.circleGap a g.1 := by
  let y := R.realLift.action g⁻¹ t
  have hy : y ∈ Set.Ioo 0
      (OrderedActions.representativeOrbit R.realLift R.positive R.cofinal a) := by
    constructor
    · simpa only [y, map_inv, RelIso.inv_apply_self] using
        (R.realLift.action g⁻¹).strictMono hlo
    · simpa only [y, map_inv, RelIso.inv_apply_self] using
        (R.realLift.action g⁻¹).strictMono hhi
  refine ⟨(y : AddCircle (1 : ℝ)), ⟨y, hy, rfl⟩, ?_⟩
  rw [← R.coe_real_action g y]
  dsimp only [y]
  simp only [map_inv, RelIso.apply_inv_self]

/-- Membership can be lifted using the actual integer central coordinate. -/
theorem mem_circleGap_iff_real_interval (a g : G) (t : ℝ) :
    (t : AddCircle (1 : ℝ)) ∈ R.circleGap a g ↔
      ∃ h : G × Multiplicative ℤ, h.1 = g ∧ R.realLift.action h 0 < t ∧
        t < R.realLift.action h
          (OrderedActions.representativeOrbit R.realLift R.positive R.cofinal a) := by
  constructor
  · rintro ⟨_, ⟨v, hv, rfl⟩, he⟩
    have he' : (R.realLift.action (g, 1) v : AddCircle (1 : ℝ)) = (t : AddCircle (1 : ℝ)) :=
      (R.coe_real_action (g, 1) v).trans he
    have hz : ((t - R.realLift.action (g, 1) v : ℝ) : AddCircle (1 : ℝ)) = 0 := by
      rw [AddCircle.coe_sub, he', sub_self]
    obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hz
    have hne : t = R.realLift.action (g, 1) v + (n : ℝ) := by
      simp only [zsmul_eq_mul, mul_one] at hn
      linarith
    refine ⟨cofinalProductZ G ^ n * (g, 1), by simp [cofinalProductZ], ?_, ?_⟩
    · rw [map_mul, RelIso.mul_apply, R.central_zpow_apply, hne]
      have hh := (R.realLift.action (g, 1)).strictMono hv.1
      linarith
    · rw [map_mul, RelIso.mul_apply, R.central_zpow_apply, hne]
      have hh := (R.realLift.action (g, 1)).strictMono hv.2
      linarith
  · rintro ⟨h, rfl, hlo, hhi⟩
    exact R.mem_circleGap_of_real_interval a h hlo hhi

/-- Two actual successor gaps cannot overlap. -/
theorem circleGap_disjoint {a : G} (ha : C.IsSuccessor a) {g h : G} (hne : g ≠ h) :
    Disjoint (R.circleGap a g) (R.circleGap a h) := by
  rw [Set.disjoint_left]
  intro x hx hy
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective x
  obtain ⟨k, hk, hklo, hkhi⟩ := (R.mem_circleGap_iff_real_interval a g t).mp hx
  obtain ⟨l, hl, hllo, hlhi⟩ := (R.mem_circleGap_iff_real_interval a h t).mp hy
  have he : R.realLift.action k 0 = R.realLift.action l 0 := by
    apply le_antisymm
    · by_contra hn
      have hlo := lt_of_not_ge hn
      have hmem := R.mem_circleGap_of_real_interval a l hlo (hklo.trans hlhi)
      have horbit : (R.realLift.action k 0 : AddCircle (1 : ℝ)) ∈
          closure (Set.range (fun j => R.action j 0)) := by
        rw [R.coe_real_action]
        exact subset_closure ⟨k.1, rfl⟩
      exact Set.disjoint_left.mp (R.circleGap_disjoint_orbitClosure ha l.1) hmem horbit
    · by_contra hn
      have hlo := lt_of_not_ge hn
      have hmem := R.mem_circleGap_of_real_interval a k hlo (hllo.trans hkhi)
      have horbit : (R.realLift.action l 0 : AddCircle (1 : ℝ)) ∈
          closure (Set.range (fun j => R.action j 0)) := by
        rw [R.coe_real_action]
        exact subset_closure ⟨l.1, rfl⟩
      exact Set.disjoint_left.mp (R.circleGap_disjoint_orbitClosure ha k.1) hmem horbit
  have hkl : k = l := R.realLift.orbit_injective (by simpa only [R.base_zero] using he)
  exact hne (hk.symm.trans ((congrArg Prod.fst hkl).trans hl))



/-- The marked gaps are exactly connected components of the orbit complement. -/
theorem circleGap_eq_component {a : G} (ha : C.IsSuccessor a) (g : G)
    {x : AddCircle (1 : ℝ)} (hx : x ∈ R.circleGap a g) :
    connectedComponentIn (closure (Set.range (fun k => R.action k 0)))ᶜ x = R.circleGap a g := by
  let F := (closure (Set.range (fun k => R.action k 0)))ᶜ
  have hsub : R.circleGap a g ⊆ F := by
    intro t ht
    exact fun hh => Set.disjoint_left.mp (R.circleGap_disjoint_orbitClosure ha g) ht hh
  apply Set.Subset.antisymm
  · let U : Set (AddCircle (1 : ℝ)) := ⋃ h : G, ⋃ (_ : h ≠ g), R.circleGap a h
    have hU : IsOpen U := isOpen_iUnion (fun h => isOpen_iUnion (fun _ => R.circleGap_isOpen a h))
    have hd : Disjoint (R.circleGap a g) U := by
      rw [Set.disjoint_left]
      intro t ht hu
      obtain ⟨h, hne, hh⟩ := Set.mem_iUnion.mp hu |>.imp fun _ => Set.mem_iUnion.mp
      exact Set.disjoint_left.mp (R.circleGap_disjoint ha hne.symm) ht hh
    have hcover : connectedComponentIn F x ⊆ R.circleGap a g ∪ U := by
      intro t ht
      obtain ⟨h, hh⟩ := R.exists_mem_circleGap ha (connectedComponentIn_subset F x ht)
      by_cases he : h = g
      · exact Or.inl (he ▸ hh)
      · exact Or.inr (Set.mem_iUnion.mpr ⟨h, Set.mem_iUnion.mpr ⟨he, hh⟩⟩)
    exact isPreconnected_connectedComponentIn.subset_left_of_subset_union
      (R.circleGap_isOpen a g) hU hd hcover ⟨x, mem_connectedComponentIn (hsub hx), hx⟩
  · exact (R.circleGap_preconnected a g).subset_connectedComponentIn hx hsub

/-- A circular successor makes the basepoint isolated in the orbit closure. -/
theorem exists_base_isolating_neighborhood {a : G} (ha : C.IsSuccessor a) :
    ∃ U : Set (AddCircle (1 : ℝ)), IsOpen U ∧ 0 ∈ U ∧
      U ∩ closure (Set.range (fun g => R.action g 0)) = {0} := by
  let b := cofinalProductRepresentative R.liftOrder R.positive R.cofinal a
  let r := OrderedActions.representativeOrbit R.realLift R.positive R.cofinal a
  let l := R.realLift.action b⁻¹ 0
  have hr : 0 < r := R.representativeOrbit_pos ha
  have hl : l < 0 := by
    have hh := (R.realLift.action b⁻¹).strictMono hr
    simpa only [l, r, OrderedActions.representativeOrbit, b, map_inv, RelIso.inv_apply_self] using hh
  let U := ((↑) : ℝ → AddCircle (1 : ℝ)) '' Set.Ioo l r
  refine ⟨U, QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo, ⟨0, ⟨hl, hr⟩, rfl⟩, ?_⟩
  ext x
  constructor
  · rintro ⟨⟨t, ht, rfl⟩, hx⟩
    suffices t = 0 by simp only [this, AddCircle.coe_zero, Set.mem_singleton_iff]
    by_contra ht0
    rcases lt_or_gt_of_ne ht0 with htneg | htpos
    · have hmem : (t : AddCircle (1 : ℝ)) ∈ R.circleGap a (b⁻¹).1 := by
        apply R.mem_circleGap_of_real_interval a b⁻¹ ht.1
        simpa only [OrderedActions.representativeOrbit, b, map_inv, RelIso.inv_apply_self] using htneg
      exact Set.disjoint_left.mp (R.circleGap_disjoint_orbitClosure ha (b⁻¹).1) hmem hx
    · have hmem : (t : AddCircle (1 : ℝ)) ∈ R.circleGap a (1 : G × Multiplicative ℤ).1 := by
        apply R.mem_circleGap_of_real_interval a 1
        · simpa only [map_one, RelIso.one_apply] using htpos
        · simpa only [map_one, RelIso.one_apply] using ht.2
      exact Set.disjoint_left.mp (R.circleGap_disjoint_orbitClosure ha 1) hmem hx
  · rintro rfl
    refine ⟨⟨0, ⟨hl, hr⟩, rfl⟩, subset_closure ⟨1, ?_⟩⟩
    simp

/-- Removing the isolated basepoint leaves a compact set of colored orbit limits. -/
theorem isCompact_orbitClosure_without_base {a : G} (ha : C.IsSuccessor a) :
    IsCompact (closure (Set.range (fun g => R.action g 0)) \ {0}) := by
  obtain ⟨U, hU, hzero, he⟩ := R.exists_base_isolating_neighborhood ha
  have hs : closure (Set.range (fun g => R.action g 0)) \ {0} =
      closure (Set.range (fun g => R.action g 0)) ∩ Uᶜ := by
    ext x
    constructor
    · rintro ⟨hx, hx0⟩
      refine ⟨hx, ?_⟩
      intro hxU
      exact hx0 (he ▸ (show x ∈ U ∩ closure (Set.range (fun g => R.action g 0)) from ⟨hxU, hx⟩))
    · rintro ⟨hx, hxU⟩
      exact ⟨hx, fun h => hxU ((Set.mem_singleton_iff.mp h).symm ▸ hzero)⟩
  rw [hs]
  exact (isClosed_closure.inter hU.isClosed_compl).isCompact

end CircularRealization
end FnZPositiveCones
