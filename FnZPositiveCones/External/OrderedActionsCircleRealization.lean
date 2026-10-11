module

public import FnZPositiveCones.External.OrderedActionsCircle
public import FnZPositiveCones.External.CircularDynamicsCompletion

@[expose] public section

namespace FnZPositiveCones.OrderedActions

theorem circle_sbtw_zero_iff {u v : ℝ} (hu : u ∈ Set.Ico (0 : ℝ) 1)
    (hv : v ∈ Set.Ico (0 : ℝ) 1) :
    sbtw (0 : AddCircle (1 : ℝ)) u v ↔ 0 < u ∧ u < v := by
  by_cases hu0 : u = 0
  · subst u
    simp only [AddCircle.coe_zero, sbtw_irrefl_left, lt_self_iff_false, false_and]
  by_cases hv0 : v = 0
  · subst v
    simp only [AddCircle.coe_zero, sbtw_irrefl_left_right, false_iff, not_and]
    exact fun h => not_lt_of_ge hu.1
  have hpu : 0 < u := lt_of_le_of_ne hu.1 (Ne.symm hu0)
  have hpv : 0 < v := lt_of_le_of_ne hv.1 (Ne.symm hv0)
  have hco_u := (toIcoMod_eq_self (show (0 : ℝ) < 1 by norm_num)).mpr
    (show u ∈ Set.Ico 0 (0 + 1) by simpa using hu)
  have hco_v := (toIcoMod_eq_self (show (0 : ℝ) < 1 by norm_num)).mpr
    (show v ∈ Set.Ico 0 (0 + 1) by simpa using hv)
  have hoc_u := (toIocMod_eq_self (show (0 : ℝ) < 1 by norm_num)).mpr
    (show u ∈ Set.Ioc 0 (0 + 1) by exact ⟨hpu, by simpa using hu.2.le⟩)
  have hoc_v := (toIocMod_eq_self (show (0 : ℝ) < 1 by norm_num)).mpr
    (show v ∈ Set.Ioc 0 (0 + 1) by exact ⟨hpv, by simpa using hv.2.le⟩)
  rw [sbtw_iff_btw_not_btw,
    show btw (v : AddCircle (1 : ℝ)) u 0 ↔ btw (0 : AddCircle (1 : ℝ)) v u from btw_cyclic]
  change (btw ((0 : ℝ) : AddCircle (1 : ℝ)) u v ∧
    ¬ btw ((0 : ℝ) : AddCircle (1 : ℝ)) v u) ↔ _
  rw [QuotientAddGroup.btw_coe_iff, QuotientAddGroup.btw_coe_iff,
    hco_u, hco_v, hoc_u, hoc_v]
  simp only [not_le, and_iff_right hpu]
  exact ⟨And.right, fun h => ⟨h.le, h⟩⟩

theorem circleAction_translation_eq_one {G : Type*} [Group G] (ρ : G →* (ℝ ≃o ℝ))
    (hρ : ∀ g : G, ∀ x : ℝ, ρ g (x + 1) = ρ g x + 1) (z : G)
    (hz : ∀ x : ℝ, ρ z x = x + 1) : circleAction ρ hρ z = 1 := by
  ext x
  induction x using QuotientAddGroup.induction_on with | H x =>
    change (ρ z x : AddCircle (1 : ℝ)) = (x : AddCircle (1 : ℝ))
    rw [hz, AddCircle.coe_add, AddCircle.coe_period, add_zero]

universe u
variable {G : Type u} [Group G]
variable {O : LeftGroupOrder (G × Multiplicative ℤ)}
variable (R : TightRealization O) (hbase : R.base = 0)
variable (htrans : ∀ x : ℝ, R.action (cofinalProductZ G) x = x + 1)
variable (hz : O.order.lt 1 (cofinalProductZ G)) (hc : O.IsCofinal (cofinalProductZ G))

noncomputable def productCircleAction : G →* Equiv.Perm (AddCircle (1 : ℝ)) :=
  (circleAction R.action (central_translation_equivariant R.action (cofinalProductZ G)
    htrans cofinalProductZ_central)).comp (MonoidHom.inl G (Multiplicative ℤ))

noncomputable def representativeOrbit (g : G) : ℝ :=
  R.action (cofinalProductRepresentative O hz hc g) 0

include hbase htrans in
theorem representativeOrbit_mem (g : G) : representativeOrbit R hz hc g ∈ Set.Ico (0 : ℝ) 1 := by
  let := O.order
  have hr := O.fundamentalRepresentative_mem hz hc (g, 1)
  constructor
  · have hh := (R.order_iff _ _).mp hr.1
    simpa only [hbase, map_one, realAut_one_apply, representativeOrbit, cofinalProductRepresentative] using hh
  · have hh : R.action (cofinalProductRepresentative O hz hc g) R.base <
        R.action (cofinalProductZ G) R.base := by
      rw [lt_iff_not_ge, ← R.order_iff]
      exact not_le_of_gt hr.2
    simpa only [hbase, htrans, zero_add, representativeOrbit] using hh

theorem productCircleAction_zero (g : G) :
    productCircleAction R htrans g 0 = (representativeOrbit R hz hc g : AddCircle (1 : ℝ)) := by
  let hρ := central_translation_equivariant R.action (cofinalProductZ G) htrans cofinalProductZ_central
  let σ := circleAction R.action hρ
  have hzσ : σ (cofinalProductZ G) = 1 := circleAction_translation_eq_one R.action hρ _ htrans
  have hh : σ (cofinalProductRepresentative O hz hc g) = σ (g, 1) := by
    simp only [cofinalProductRepresentative, LeftGroupOrder.fundamentalRepresentative,
      map_mul, map_zpow, hzσ, one_zpow, one_mul]
  have ha := Equiv.congr_fun hh (0 : AddCircle (1 : ℝ))
  exact ha.symm

include hbase hz hc in
theorem productCircleAction_orbit_injective :
    Function.Injective (fun g => productCircleAction R htrans g 0) := by
  intro g h he
  dsimp only at he
  rw [productCircleAction_zero R htrans hz hc, productCircleAction_zero R htrans hz hc] at he
  have hr := (AddCircle.coe_eq_coe_iff_of_mem_Ico
    (show representativeOrbit R hz hc g ∈ Set.Ico 0 (0 + 1) by simpa using representativeOrbit_mem R hbase htrans hz hc g)
    (show representativeOrbit R hz hc h ∈ Set.Ico 0 (0 + 1) by simpa using representativeOrbit_mem R hbase htrans hz hc h)).mp he
  apply cofinalProductRepresentative_injective O hz hc
  apply R.orbit_injective
  simpa only [hbase, representativeOrbit] using hr

theorem productCircleAction_preserves (g : G) :
    CircularDynamics.PreservesCircular (productCircleAction R htrans g) :=
  circlePerm_btw_iff _ _

noncomputable def productCircleOrder : CircularGroupOrder G :=
  CircularDynamics.circularOrbitOrder (productCircleAction R htrans)
    (productCircleAction_preserves R htrans) 0
    (productCircleAction_orbit_injective R hbase htrans hz hc)

theorem productCircleOrder_sbtw_one (g h : G) :
    (productCircleOrder R hbase htrans hz hc).order.sbtw 1 g h ↔
      (cofinalProductCircularGroupOrder O hz hc).order.sbtw 1 g h := by
  change sbtw (productCircleAction R htrans 1 0) (productCircleAction R htrans g 0)
    (productCircleAction R htrans h 0) ↔ _
  rw [map_one]
  change sbtw (0 : AddCircle (1 : ℝ)) _ _ ↔ _
  rw [productCircleAction_zero R htrans hz hc, productCircleAction_zero R htrans hz hc,
    circle_sbtw_zero_iff (representativeOrbit_mem R hbase htrans hz hc g)
      (representativeOrbit_mem R hbase htrans hz hc h),
    cofinalProductCircularGroupOrder_sbtw_one]
  have hlt (a b : G × Multiplicative ℤ) :
      O.order.lt a b ↔ R.action a 0 < R.action b 0 := by
    let := O.order
    rw [lt_iff_not_ge, R.order_iff, hbase, not_le]
  rw [hlt, hlt, map_one]
  rfl

theorem productCircleOrder_eq :
    productCircleOrder R hbase htrans hz hc = cofinalProductCircularGroupOrder O hz hc := by
  apply CircularGroupOrder.ext
  intro a b c
  rw [← (productCircleOrder R hbase htrans hz hc).mul_sbtw_mul_left a⁻¹ a b c,
    ← (cofinalProductCircularGroupOrder O hz hc).mul_sbtw_mul_left a⁻¹ a b c,
    inv_mul_cancel]
  exact productCircleOrder_sbtw_one R hbase htrans hz hc _ _

end FnZPositiveCones.OrderedActions

namespace FnZPositiveCones
universe u

/-- A circular order together with a tight real lift whose central unit is translation. -/
structure CircularRealization {G : Type u} [Group G] (C : CircularGroupOrder G) where
  liftOrder : LeftGroupOrder (G × Multiplicative ℤ)
  positive : liftOrder.order.lt 1 (cofinalProductZ G)
  cofinal : liftOrder.IsCofinal (cofinalProductZ G)
  realLift : TightRealization liftOrder
  base_zero : realLift.base = 0
  central_translation : ∀ x : ℝ, realLift.action (cofinalProductZ G) x = x + 1
  quotient_eq : cofinalProductCircularGroupOrder liftOrder positive cofinal = C

namespace CircularRealization
variable {G : Type u} [Group G] {C : CircularGroupOrder G} (R : CircularRealization C)

noncomputable def action : G →* Equiv.Perm (AddCircle (1 : ℝ)) :=
  OrderedActions.productCircleAction R.realLift R.central_translation

theorem action_preserves (g : G) : CircularDynamics.PreservesCircular (R.action g) :=
  OrderedActions.productCircleAction_preserves R.realLift R.central_translation g

theorem action_continuous (g : G) : Continuous (R.action g) :=
  OrderedActions.circlePerm_continuous _ _

theorem orbit_injective : Function.Injective (fun g => R.action g 0) :=
  OrderedActions.productCircleAction_orbit_injective R.realLift R.base_zero R.central_translation
    R.positive R.cofinal

theorem orbit_sbtw (a b c : G) :
    C.order.sbtw a b c ↔ sbtw (R.action a 0) (R.action b 0) (R.action c 0) := by
  have he := (OrderedActions.productCircleOrder_eq R.realLift R.base_zero
    R.central_translation R.positive R.cofinal).trans R.quotient_eq
  exact iff_of_eq (congrArg (fun Q : CircularGroupOrder G => Q.order.sbtw a b c) he).symm

end CircularRealization

/-- Every circular order on a countable free group has an actual continuous circle realization,
with a tight normalized real lift and its full comparison correspondence. -/
theorem CircularGroupOrder.exists_circularRealization {ι : Type u} [Countable ι]
    (C : CircularGroupOrder (FreeGroup ι)) : Nonempty (CircularRealization C) := by
  let := C.order
  let ρ : FreeGroup ι →* Equiv.Perm (FreeGroup ι) := MulAction.toPermHom _ _
  have hρ (g : FreeGroup ι) : CircularDynamics.PreservesCircular (ρ g) := by
    intro a b c
    exact C.mul_btw_mul_left g a b c
  have hi : Function.Injective (fun g => ρ g 1) := by
    intro g h he
    change g * 1 = h * 1 at he
    simpa only [mul_one] using he
  let L := CircularDynamics.freeGroupLeftOrderOfCircular C
  let O := CircularDynamics.completionOrder ρ hρ 1 L
  have hz : O.order.lt 1 (cofinalProductZ (FreeGroup ι)) :=
    CircularDynamics.completionOrder_center_positive ρ hρ 1 L
  have hc : O.IsCofinal (cofinalProductZ (FreeGroup ι)) :=
    CircularDynamics.completionOrder_center_cofinal ρ hρ 1 L
  obtain ⟨R⟩ := O.exists_tightRealization
  obtain ⟨S, hb, hs⟩ := R.exists_translation _ hz hc
  refine ⟨⟨O, hz, hc, S, hb, hs, ?_⟩⟩
  change CircularDynamics.completedCircularOrbitOrder ρ hρ 1 L = C
  rw [CircularDynamics.completedCircularOrbitOrder_eq_of_injective ρ hρ 1 L hi]
  apply CircularGroupOrder.ext
  intro a b c
  change sbtw (a * 1) (b * 1) (c * 1) ↔ sbtw a b c
  simp only [mul_one]

end FnZPositiveCones
