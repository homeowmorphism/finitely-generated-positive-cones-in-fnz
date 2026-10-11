module

public import FnZPositiveCones.External.OrderedActionsFill

@[expose] public section

namespace FnZPositiveCones
universe u
variable {G : Type u} [Group G]

/-- A real-line realization with an unbounded free orbit and no extra gaps. -/
structure TightRealization (O : LeftGroupOrder G) where
  action : G →* (ℝ ≃o ℝ)
  base : ℝ
  order_iff : ∀ g h : G, O.order.le g h ↔ action g base ≤ action h base
  unbounded_above : ∀ x : ℝ, ∃ g : G, x < action g base
  unbounded_below : ∀ x : ℝ, ∃ g : G, action g base < x
  orbit_gap : ∀ x : ℝ, x ∉ closure (Set.range (fun g => action g base)) →
    ∃ g h : G, action g base < x ∧ x < action h base ∧
      Disjoint (Set.Ioo (action g base) (action h base))
        (closure (Set.range (fun k => action k base)))

namespace TightRealization
variable {O : LeftGroupOrder G} (R : TightRealization O)

theorem orbit_injective : Function.Injective (fun g => R.action g R.base) := by
  intro g h he
  let := O.order
  exact le_antisymm ((R.order_iff g h).mpr he.le) ((R.order_iff h g).mpr he.ge)

theorem no_global_fixed (x : ℝ) : ∃ g : G, R.action g x ≠ x := by
  rcases le_total R.base x with hx | hx
  · obtain ⟨g, hg⟩ := R.unbounded_above x
    refine ⟨g, fun he => ?_⟩
    have hh := (R.action g).monotone hx
    rw [he] at hh
    exact hg.not_ge hh
  · obtain ⟨g, hg⟩ := R.unbounded_below x
    refine ⟨g, fun he => ?_⟩
    have hh := (R.action g).monotone hx
    rw [he] at hh
    exact hg.not_ge hh

end TightRealization

namespace LeftGroupOrder

theorem exists_positive (O : LeftGroupOrder G) [Nontrivial G] :
    ∃ g : G, O.order.lt 1 g := by
  let := O.order
  obtain ⟨g, hg⟩ := exists_ne (1 : G)
  rcases lt_or_gt_of_ne hg with h | h
  · refine ⟨g⁻¹, ?_⟩
    simpa only [inv_mul_cancel, mul_one] using O.mul_lt_mul_left g⁻¹ h
  · exact ⟨g, h⟩

/-- Left multiplication is an order-automorphism representation. -/
def leftTranslation (O : LeftGroupOrder G) :
    letI := O.order; G →* (G ≃o G) := by
  let := O.order
  exact {
    toFun := fun g => {
      toFun := fun h => g * h
      invFun := fun h => g⁻¹ * h
      left_inv := fun h => inv_mul_cancel_left g h
      right_inv := fun h => mul_inv_cancel_left g h
      map_rel_iff' := by
        intro a b
        constructor
        · intro h
          change g * a ≤ g * b at h
          simpa only [inv_mul_cancel_left] using O.mul_le_mul_left _ _ g⁻¹ h
        · exact O.mul_le_mul_left a b g }
    map_one' := by ext h; exact one_mul h
    map_mul' := by intro g h; ext k; exact mul_assoc g h k }

/-- Every countable nontrivial left-ordered group has a tight realization on ℝ. -/
theorem exists_tightRealization (O : LeftGroupOrder G) [Countable G] [Nontrivial G] :
    Nonempty (TightRealization O) := by
  let := O.order
  obtain ⟨z, hz⟩ := O.exists_positive
  have hzi : z⁻¹ < (1 : G) := by
    simpa only [mul_one, inv_mul_cancel] using O.mul_lt_mul_left z⁻¹ hz
  let : NoMinOrder G := ⟨fun a => ⟨a * z⁻¹, by
    simpa only [mul_one] using O.mul_lt_mul_left a hzi⟩⟩
  let : NoMaxOrder G := ⟨fun a => ⟨a * z, by
    simpa only [mul_one] using O.mul_lt_mul_left a hz⟩⟩
  let e : G ↪o ℝ := OrderedActions.realModel
  let ρ : G →* (ℝ ≃o ℝ) := OrderedActions.realModelHom.comp O.leftTranslation
  have he (g : G) : ρ g (e 1) = e g := by
    change OrderedActions.realModelHom (O.leftTranslation g)
      (OrderedActions.realModel 1) = OrderedActions.realModel g
    rw [OrderedActions.realModelHom_apply]
    change OrderedActions.realModel (g * 1) = _
    rw [mul_one]
  refine ⟨{
    action := ρ
    base := e 1
    order_iff := ?_
    unbounded_above := ?_
    unbounded_below := ?_
    orbit_gap := ?_ }⟩
  · intro g h
    rw [he, he]
    exact e.le_iff_le.symm
  · intro x
    simpa only [he] using OrderedActions.realModel_unbounded_above (A := G) x
  · intro x
    simpa only [he] using OrderedActions.realModel_unbounded_below (A := G) x
  · intro x hx
    simp only [he] at hx ⊢
    obtain ⟨a, b, hab, ha, hb⟩ := OrderedActions.realModel_gap hx
    exact ⟨a, b, ha, hb, OrderedActions.realModel_gap_disjoint hab⟩

end LeftGroupOrder
end FnZPositiveCones
