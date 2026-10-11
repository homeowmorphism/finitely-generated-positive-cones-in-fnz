module

public import FnZPositiveCones.External.CircularIsolatedComponents
public import FnZPositiveCones.External.ConvexExtension

@[expose] public section

/-! Actual complement components of closed invariant circle sets. -/
namespace FnZPositiveCones
namespace CircularDynamics

def liftedComplement (S : Set StandardCircle) : Set ℝ :=
  ((↑) : ℝ → StandardCircle) ⁻¹' Sᶜ

def complementBaseComponent (S : Set StandardCircle) : Set ℝ :=
  connectedComponentIn (liftedComplement S) 0

theorem isOpen_liftedComplement {S : Set StandardCircle} (hS : IsClosed S) :
    IsOpen (liftedComplement S) := hS.isOpen_compl.preimage (AddCircle.continuous_mk' (1 : ℝ))

theorem zero_mem_complementBaseComponent {S : Set StandardCircle} (h0 : 0 ∉ S) :
    (0 : ℝ) ∈ complementBaseComponent S := by
  exact mem_connectedComponentIn (by simpa only [liftedComplement, Set.mem_preimage,
    Set.mem_compl_iff, AddCircle.coe_zero] using h0)

theorem complementBaseComponent_subset (S : Set StandardCircle) :
    complementBaseComponent S ⊆ liftedComplement S := connectedComponentIn_subset _ _

theorem complementBaseComponent_eq_Ioo {S : Set StandardCircle}
    (hS : IsClosed S) (hne : S.Nonempty) (h0 : 0 ∉ S) :
    ∃ a b : ℝ, a < 0 ∧ 0 < b ∧ complementBaseComponent S = Set.Ioo a b := by
  obtain ⟨p, hp⟩ := hne
  let q := circleCoordinate p
  have hqmem := circleCoordinate_mem p
  have hqpos : 0 < q := by
    apply lt_of_le_of_ne hqmem.1
    intro he
    apply h0
    have hp0 : p = 0 := by rw [← coe_circleCoordinate p, ← he]; rfl
    simpa only [hp0] using hp
  have hc : IsConnected (complementBaseComponent S) :=
    isConnected_connectedComponentIn_iff.mpr (by simpa [liftedComplement] using h0)
  have hz := zero_mem_complementBaseComponent h0
  have hcut : q ∉ liftedComplement S := by simpa only [liftedComplement, Set.mem_preimage,
    Set.mem_compl_iff, q, coe_circleCoordinate, not_not] using hp
  have hcut' : q - 1 ∉ liftedComplement S := by
    change ¬((q - 1 : ℝ) : StandardCircle) ∉ S
    simpa only [AddCircle.coe_sub, AddCircle.coe_period, sub_zero, q,
      coe_circleCoordinate, not_not] using hp
  have hb : complementBaseComponent S ⊆ Set.Ioo (q - 1) q := by
    intro x hx
    constructor
    · by_contra h
      exact hcut' (complementBaseComponent_subset S
        (hc.isPreconnected.ordConnected.out hx hz ⟨le_of_not_gt h, by linarith [hqmem.2]⟩))
    · by_contra h
      exact hcut (complementBaseComponent_subset S
        (hc.isPreconnected.ordConnected.out hz hx ⟨hqpos.le, le_of_not_gt h⟩))
  have hcompact : IsCompact (closure (complementBaseComponent S)) :=
    isCompact_Icc.of_isClosed_subset isClosed_closure
      (closure_minimal (hb.trans Set.Ioo_subset_Icc_self) isClosed_Icc)
  obtain ⟨a, b, _, he, _⟩ := open_connected_real_eq_Ioo
    (isOpen_liftedComplement hS).connectedComponentIn hc hcompact
  change complementBaseComponent S = Set.Ioo a b at he
  rw [he] at hz
  exact ⟨a, b, hz.1, hz.2, he⟩

end CircularDynamics
namespace CircularRealization
open CircularDynamics
universe u
variable {ι : Type u} {C : CircularGroupOrder (FreeGroup ι)} (R : CircularRealization C)
variable {S : Set StandardCircle}

theorem mem_invariant_liftedComplement_action
    (hinv : ∀ g, R.action g '' S = S) (g : FreeGroup ι × Multiplicative ℤ) (x : ℝ) :
    R.realLift.action g x ∈ liftedComplement S ↔ x ∈ liftedComplement S := by
  change ((R.realLift.action g x : ℝ) : StandardCircle) ∉ S ↔ (x : StandardCircle) ∉ S
  rw [R.coe_real_action]
  have hm : R.action g.1 (x : StandardCircle) ∈ S ↔ (x : StandardCircle) ∈ S := by
    conv_lhs => rw [← hinv g.1]
    exact (R.action g.1).injective.mem_set_image
  exact not_congr hm

theorem image_invariant_liftedComplement (hinv : ∀ g, R.action g '' S = S)
    (g : FreeGroup ι × Multiplicative ℤ) :
    R.realLift.action g '' liftedComplement S = liftedComplement S := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (R.mem_invariant_liftedComplement_action hinv g y).mpr hy
  · intro hx
    refine ⟨(R.realLift.action g).symm x, ?_, (R.realLift.action g).apply_symm_apply x⟩
    apply (R.mem_invariant_liftedComplement_action hinv g _).mp
    simpa only [(R.realLift.action g).apply_symm_apply] using hx

def invariantComponentStabilizer (S : Set StandardCircle) :
    Subgroup (FreeGroup ι × Multiplicative ℤ) :=
  realSetStabilizer R.realLift.action (complementBaseComponent S)

theorem mem_invariantComponentStabilizer_iff (h0 : 0 ∉ S)
    (hinv : ∀ g, R.action g '' S = S) (g : FreeGroup ι × Multiplicative ℤ) :
    g ∈ R.invariantComponentStabilizer S ↔ R.realLift.action g 0 ∈ complementBaseComponent S := by
  have hz : (0 : ℝ) ∈ liftedComplement S := by simpa [liftedComplement] using h0
  have he := (R.realLift.action g).toHomeomorph.image_connectedComponentIn hz
  change R.realLift.action g '' complementBaseComponent S =
    connectedComponentIn (R.realLift.action g '' liftedComplement S) (R.realLift.action g 0) at he
  rw [R.image_invariant_liftedComplement hinv] at he
  constructor
  · intro hg
    change R.realLift.action g '' complementBaseComponent S = complementBaseComponent S at hg
    rw [← hg]
    exact ⟨0, zero_mem_complementBaseComponent h0, rfl⟩
  · intro hg
    exact he.trans (connectedComponentIn_eq hg).symm

/-- The actual interval stabilizer is convex for the lifted order. -/
theorem invariantComponentStabilizer_convex (h0 : 0 ∉ S)
    (hinv : ∀ g, R.action g '' S = S) :
    ConeConvex (leftOrderCone R.liftOrder) (R.invariantComponentStabilizer S) := by
  have hord : coneLinearOrder (leftOrderCone R.liftOrder) = R.liftOrder.order :=
    congrArg LeftGroupOrder.order (coneLeftOrder_leftOrderCone R.liftOrder)
  unfold ConeConvex
  rw [hord]
  let := R.liftOrder.order
  refine ⟨?_⟩
  intro a ha b hb c hc
  apply (R.mem_invariantComponentStabilizer_iff h0 hinv c).mpr
  have ha' := (R.mem_invariantComponentStabilizer_iff h0 hinv a).mp ha
  have hb' := (R.mem_invariantComponentStabilizer_iff h0 hinv b).mp hb
  have hac := (R.realLift.order_iff a c).mp hc.1
  have hcb := (R.realLift.order_iff c b).mp hc.2
  rw [R.base_zero] at hac hcb
  exact (show IsPreconnected (complementBaseComponent S) from isPreconnected_connectedComponentIn).ordConnected.out ha' hb' ⟨hac, hcb⟩

/-- The marked free projection on the actual interval stabilizer. -/
def invariantComponentProjection (S : Set StandardCircle) :
    R.invariantComponentStabilizer S →* FreeGroup ι :=
  (MonoidHom.fst _ _).comp (R.invariantComponentStabilizer S).subtype

/-- No nonzero central translation can preserve the bounded interval. -/
theorem invariantComponentProjection_injective
    (hS : IsClosed S) (hne : S.Nonempty) (h0 : 0 ∉ S) :
    Function.Injective (R.invariantComponentProjection S) := by
  apply (injective_iff_map_eq_one (R.invariantComponentProjection S)).mpr
  intro g hg
  have hfst : g.val.1 = 1 := hg
  obtain ⟨a, b, ha, hb, hI⟩ := complementBaseComponent_eq_Ioo hS hne h0
  have hab := ha.trans hb
  have hset : R.realLift.action g.val '' complementBaseComponent S = complementBaseComponent S := g.property
  rw [hI, (R.realLift.action g.val).image_Ioo] at hset
  have hclosure := congrArg closure hset
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

end CircularRealization
end FnZPositiveCones
