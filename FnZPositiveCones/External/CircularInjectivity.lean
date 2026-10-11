module

public import FnZPositiveCones.External.CircularCocycle

@[expose] public section

/-! The circular carry cocycle determines the complete circular group order. -/

namespace FnZPositiveCones

universe u
variable {G : Type u} [Group G]

/-- A circular group order is determined by its strict circular comparisons. -/
@[ext] theorem CircularGroupOrder.ext {O P : CircularGroupOrder G}
    (h : ∀ a b c : G, O.order.sbtw a b c ↔ P.order.sbtw a b c) : O = P := by
  have hs : O.order.sbtw = P.order.sbtw := funext fun a => funext fun b =>
    funext fun c => propext (h a b c)
  have hb : O.order.btw = P.order.btw := by
    funext a b c
    apply propext
    rw [@btw_iff_not_sbtw G O.order, @btw_iff_not_sbtw G P.order, h c b a]
  cases O with
  | mk o ho =>
    cases P with
    | mk p hp =>
      congr 1
      cases o
      cases p
      congr 1
      cases ‹CircularPartialOrder G›
      cases ‹CircularPartialOrder G›
      congr 1
      cases ‹CircularPreorder G›
      cases ‹CircularPreorder G›
      cases ‹Btw G›
      cases ‹Btw G›
      cases ‹SBtw G›
      cases ‹SBtw G›
      congr 2

/-- Translating a triple so its first point is the identity recovers its carry
from a cocycle coordinate. -/
theorem CircularGroupOrder.cocycle_eq_carry (O : CircularGroupOrder G) (a b c : G) :
    O.toNormalizedIntCocycle.value (a⁻¹ * b) (b⁻¹ * c) =
      @CircularCarry.value G O.order a b c := by
  change @CircularCarry.value G O.order 1 (a⁻¹ * b)
      ((a⁻¹ * b) * (b⁻¹ * c)) = _
  have he : (a⁻¹ * b) * (b⁻¹ * c) = a⁻¹ * c := by group
  rw [he]
  simpa only [inv_mul_cancel] using O.carry_mul_left a⁻¹ a b c

/-- A distinct triple is strictly positive exactly when its carry is zero. -/
theorem CircularGroupOrder.sbtw_iff_carry_zero (O : CircularGroupOrder G)
    {a b c : G} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    O.order.sbtw a b c ↔ @CircularCarry.value G O.order a b c = 0 := by
  classical
  simp [CircularCarry.value, hab, hbc, hac]

/-- The normalized integer cocycle construction is injective for every group. -/
theorem CircularGroupOrder.toNormalizedIntCocycle_injective :
    Function.Injective (CircularGroupOrder.toNormalizedIntCocycle (G := G)) := by
  intro O P he
  apply CircularGroupOrder.ext
  intro a b c
  by_cases hab : a = b
  · subst b
    exact iff_of_false (@sbtw_irrefl_left G O.order.toCircularPreorder a c)
      (@sbtw_irrefl_left G P.order.toCircularPreorder a c)
  by_cases hbc : b = c
  · subst c
    exact iff_of_false (@sbtw_irrefl_right G O.order.toCircularPreorder a b)
      (@sbtw_irrefl_right G P.order.toCircularPreorder a b)
  by_cases hac : a = c
  · subst c
    exact iff_of_false (@sbtw_irrefl_left_right G O.order.toCircularPreorder a b)
      (@sbtw_irrefl_left_right G P.order.toCircularPreorder a b)
  rw [O.sbtw_iff_carry_zero hab hbc hac, P.sbtw_iff_carry_zero hab hbc hac,
    ← O.cocycle_eq_carry, ← P.cocycle_eq_carry, he]

end FnZPositiveCones
