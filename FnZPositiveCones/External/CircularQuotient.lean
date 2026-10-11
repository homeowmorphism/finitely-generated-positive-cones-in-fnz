module

public import FnZPositiveCones.External.Cofinal

@[expose] public section

/-! Circular orders induced by positive cofinal central elements of left-ordered products. -/

namespace FnZPositiveCones

universe u
variable {G : Type u} [Group G]

namespace LeftGroupOrder

variable (O : LeftGroupOrder G) {z : G}
variable (hz : O.order.lt 1 z) (hc : O.IsCofinal z)

/-- Normalization fixes the half-open fundamental interval. -/
theorem fundamentalRepresentative_eq_self {x : G}
    (hx : O.order.le 1 x ∧ O.order.lt x z) :
    O.fundamentalRepresentative hz hc x = x := by
  have h0 : 0 = O.powerFloor hz hc x :=
    O.fundamentalRepresentative_unique_exponent hz hc x 0 (by simpa using hx)
  simp [fundamentalRepresentative, ← h0]

/-- Replacing the left factor by its representative does not change the product representative. -/
theorem fundamentalRepresentative_rep_mul (a b : G) :
    O.fundamentalRepresentative hz hc (O.fundamentalRepresentative hz hc a * b) =
      O.fundamentalRepresentative hz hc (a * b) := by
  simp only [fundamentalRepresentative, mul_assoc]
  exact O.fundamentalRepresentative_zpow_mul hz hc (a * b) _

variable (hcentral : ∀ g : G, Commute z g)

include hcentral in
/-- Centrality permits normalization of the right factor before multiplying. -/
theorem fundamentalRepresentative_mul_rep (a b : G) :
    O.fundamentalRepresentative hz hc (a * O.fundamentalRepresentative hz hc b) =
      O.fundamentalRepresentative hz hc (a * b) := by
  have he : a * O.fundamentalRepresentative hz hc b =
      z ^ (-O.powerFloor hz hc b) * (a * b) := by
    simp only [fundamentalRepresentative, ← mul_assoc]
    rw [((hcentral a).zpow_left _).eq]
  rw [he, O.fundamentalRepresentative_zpow_mul]

include hcentral in
/-- Both factors may be normalized without changing the product representative. -/
theorem fundamentalRepresentative_rep_mul_rep (a b : G) :
    O.fundamentalRepresentative hz hc
        (O.fundamentalRepresentative hz hc a * O.fundamentalRepresentative hz hc b) =
      O.fundamentalRepresentative hz hc (a * b) := by
  rw [O.fundamentalRepresentative_rep_mul, O.fundamentalRepresentative_mul_rep hz hc hcentral]

/-- A product below the cut at `z` is already its fundamental representative. -/
theorem fundamentalRepresentative_mul_of_lt {a b : G}
    (ha : O.order.le 1 a ∧ O.order.lt a z)
    (hb : O.order.le 1 b ∧ O.order.lt b z) (hab : O.order.lt (a * b) z) :
    O.fundamentalRepresentative hz hc (a * b) = a * b := by
  let := O.order
  apply O.fundamentalRepresentative_eq_self hz hc
  exact ⟨ha.1.trans (by simpa using O.mul_le_mul_left 1 b a hb.1), hab⟩

include hcentral in
/-- On wrapping, normalization lands strictly below the normalized left factor. -/
theorem normalized_wrap_lt {a b : G}
    (hb : O.order.lt b z) : O.order.lt (z⁻¹ * (a * b)) a := by
  have h := O.mul_lt_mul_left z⁻¹ (O.mul_lt_mul_left a hb)
  rw [← (hcentral a).eq] at h
  simpa only [mul_assoc, inv_mul_cancel_left] using h

include hcentral in
/-- A product at or above the cut wraps exactly once. -/
theorem fundamentalRepresentative_mul_of_ge {a b : G}
    (ha : O.order.le 1 a ∧ O.order.lt a z)
    (hb : O.order.le 1 b ∧ O.order.lt b z) (hab : O.order.le z (a * b)) :
    O.fundamentalRepresentative hz hc (a * b) = z⁻¹ * (a * b) := by
  let := O.order
  have hi : O.order.le 1 (z⁻¹ * (a * b)) ∧ O.order.lt (z⁻¹ * (a * b)) z := by
    constructor
    · simpa only [inv_mul_cancel] using O.mul_le_mul_left z (a * b) z⁻¹ hab
    · exact (O.normalized_wrap_lt hcentral hb.2).trans ha.2
  have hk := O.fundamentalRepresentative_unique_exponent hz hc (a * b) 1 (by simpa using hi)
  simp [fundamentalRepresentative, ← hk]

include hcentral in
/-- The representative of an increasing triple remains cyclically increasing after left multiplication. -/
theorem fundamentalRepresentative_mul_cyclic_of_le {a x y w : G}
    (ha : O.order.le 1 a ∧ O.order.lt a z)
    (hx : O.order.le 1 x ∧ O.order.lt x z)
    (hy : O.order.le 1 y ∧ O.order.lt y z)
    (hw : O.order.le 1 w ∧ O.order.lt w z)
    (hxy : O.order.le x y) (hyw : O.order.le y w) :
    let rx := O.fundamentalRepresentative hz hc (a * x)
    let ry := O.fundamentalRepresentative hz hc (a * y)
    let rw := O.fundamentalRepresentative hz hc (a * w)
    (O.order.le rx ry ∧ O.order.le ry rw) ∨
      (O.order.le ry rw ∧ O.order.le rw rx) ∨
      (O.order.le rw rx ∧ O.order.le rx ry) := by
  let := O.order
  dsimp only
  have haxy : a * x ≤ a * y := O.mul_le_mul_left _ _ a hxy
  have hayw : a * y ≤ a * w := O.mul_le_mul_left _ _ a hyw
  have hax : a ≤ a * x := by simpa using O.mul_le_mul_left 1 x a hx.1
  have hay : a ≤ a * y := by simpa using O.mul_le_mul_left 1 y a hy.1
  by_cases hwz : a * w < z
  · have hyz := hayw.trans_lt hwz
    have hxz := haxy.trans_lt hyz
    rw [O.fundamentalRepresentative_mul_of_lt hz hc ha hx hxz,
      O.fundamentalRepresentative_mul_of_lt hz hc ha hy hyz,
      O.fundamentalRepresentative_mul_of_lt hz hc ha hw hwz]
    exact Or.inl ⟨haxy, hayw⟩
  · have hzw : z ≤ a * w := le_of_not_gt hwz
    rw [O.fundamentalRepresentative_mul_of_ge hz hc hcentral ha hw hzw]
    by_cases hyz : a * y < z
    · have hxz := haxy.trans_lt hyz
      rw [O.fundamentalRepresentative_mul_of_lt hz hc ha hx hxz,
        O.fundamentalRepresentative_mul_of_lt hz hc ha hy hyz]
      exact Or.inr (Or.inr ⟨(O.normalized_wrap_lt hcentral hw.2).le.trans hax, haxy⟩)
    · have hzy : z ≤ a * y := le_of_not_gt hyz
      rw [O.fundamentalRepresentative_mul_of_ge hz hc hcentral ha hy hzy]
      by_cases hxz : a * x < z
      · rw [O.fundamentalRepresentative_mul_of_lt hz hc ha hx hxz]
        exact Or.inr (Or.inl ⟨O.mul_le_mul_left _ _ z⁻¹ hayw,
          (O.normalized_wrap_lt hcentral hw.2).le.trans hax⟩)
      · have hzx : z ≤ a * x := le_of_not_gt hxz
        rw [O.fundamentalRepresentative_mul_of_ge hz hc hcentral ha hx hzx]
        exact Or.inl ⟨O.mul_le_mul_left _ _ z⁻¹ haxy, O.mul_le_mul_left _ _ z⁻¹ hayw⟩

end LeftGroupOrder
end FnZPositiveCones

namespace FnZPositiveCones

universe u
variable {G : Type u} [Group G]

/-- The cyclic relation obtained by closing up a linear order. -/
def LeftGroupOrder.CircularLE (O : LeftGroupOrder G) (a b c : G) : Prop :=
  (O.order.le a b ∧ O.order.le b c) ∨
    (O.order.le b c ∧ O.order.le c a) ∨
    (O.order.le c a ∧ O.order.le a b)

/-- Normalized left multiplication preserves the cyclic relation on representatives. -/
theorem LeftGroupOrder.fundamentalRepresentative_mul_circular (O : LeftGroupOrder G) {z : G}
    (hz : O.order.lt 1 z) (hc : O.IsCofinal z) (hcentral : ∀ g : G, Commute z g)
    (a x y w : G)
    (h : O.CircularLE (O.fundamentalRepresentative hz hc x)
      (O.fundamentalRepresentative hz hc y) (O.fundamentalRepresentative hz hc w)) :
    O.CircularLE (O.fundamentalRepresentative hz hc (a * x))
      (O.fundamentalRepresentative hz hc (a * y)) (O.fundamentalRepresentative hz hc (a * w)) := by
  rw [← O.fundamentalRepresentative_rep_mul_rep hz hc hcentral a x,
    ← O.fundamentalRepresentative_rep_mul_rep hz hc hcentral a y,
    ← O.fundamentalRepresentative_rep_mul_rep hz hc hcentral a w]
  rcases h with h | h | h
  · exact O.fundamentalRepresentative_mul_cyclic_of_le hz hc hcentral
      (O.fundamentalRepresentative_mem hz hc a) (O.fundamentalRepresentative_mem hz hc x)
      (O.fundamentalRepresentative_mem hz hc y) (O.fundamentalRepresentative_mem hz hc w) h.1 h.2
  · have h' := O.fundamentalRepresentative_mul_cyclic_of_le hz hc hcentral
      (O.fundamentalRepresentative_mem hz hc a) (O.fundamentalRepresentative_mem hz hc y)
      (O.fundamentalRepresentative_mem hz hc w) (O.fundamentalRepresentative_mem hz hc x) h.1 h.2
    exact h'.rotate.rotate
  · have h' := O.fundamentalRepresentative_mul_cyclic_of_le hz hc hcentral
      (O.fundamentalRepresentative_mem hz hc a) (O.fundamentalRepresentative_mem hz hc w)
      (O.fundamentalRepresentative_mem hz hc x) (O.fundamentalRepresentative_mem hz hc y) h.1 h.2
    exact h'.rotate

/-- A circular order with exactly left-multiplication invariance. -/
structure CircularGroupOrder (G : Type u) [Group G] where
  order : CircularOrder G
  mul_btw_mul_left : ∀ a b c d : G,
    order.btw (a * b) (a * c) (a * d) ↔ order.btw b c d

/-- Strict circular comparisons inherit the same left invariance. -/
theorem CircularGroupOrder.mul_sbtw_mul_left (O : CircularGroupOrder G) (a b c d : G) :
    O.order.sbtw (a * b) (a * c) (a * d) ↔ O.order.sbtw b c d := by
  let := O.order
  rw [sbtw_iff_btw_not_btw, sbtw_iff_btw_not_btw,
    O.mul_btw_mul_left, O.mul_btw_mul_left]

/-- The positive generator of the distinguished cyclic direct factor. -/
def cofinalProductZ (A : Type u) [Group A] : A × Multiplicative ℤ :=
  (1, Multiplicative.ofAdd 1)

theorem cofinalProductZ_central (g : G × Multiplicative ℤ) : Commute (cofinalProductZ G) g := by
  apply Prod.ext
  · simp [cofinalProductZ]
  · exact mul_comm _ _

variable (O : LeftGroupOrder (G × Multiplicative ℤ))
variable (hz : O.order.lt 1 (cofinalProductZ G)) (hc : O.IsCofinal (cofinalProductZ G))

/-- The distinguished representative of a free-factor element in the fundamental interval. -/
noncomputable def cofinalProductRepresentative (g : G) : G × Multiplicative ℤ :=
  O.fundamentalRepresentative hz hc (g, 1)

@[simp] theorem cofinalProductRepresentative_fst (g : G) :
    (cofinalProductRepresentative O hz hc g).1 = g := by
  simp [cofinalProductRepresentative, LeftGroupOrder.fundamentalRepresentative, cofinalProductZ]

theorem cofinalProductRepresentative_injective :
    Function.Injective (cofinalProductRepresentative O hz hc) := by
  intro g h he
  simpa using congrArg Prod.fst he

/-- The circular quotient order on the first factor, constructed from actual representatives. -/
@[instance_reducible] noncomputable def cofinalProductCircularOrder : CircularOrder G := by
  letI := O.order
  letI : LinearOrder G := LinearOrder.lift' (cofinalProductRepresentative O hz hc)
    (cofinalProductRepresentative_injective O hz hc)
  exact LinearOrder.toCircularOrder G

@[simp] theorem cofinalProductCircularOrder_btw (a b c : G) :
    (cofinalProductCircularOrder O hz hc).btw a b c ↔
      O.CircularLE (cofinalProductRepresentative O hz hc a)
        (cofinalProductRepresentative O hz hc b) (cofinalProductRepresentative O hz hc c) := Iff.rfl

/-- Left invariance of the constructed circular quotient, with no right-order hypothesis. -/
theorem cofinalProductCircularOrder_mul_btw_mul_left (a b c d : G) :
    (cofinalProductCircularOrder O hz hc).btw (a * b) (a * c) (a * d) ↔
      (cofinalProductCircularOrder O hz hc).btw b c d := by
  have hforward : ∀ a b c d : G,
      (cofinalProductCircularOrder O hz hc).btw b c d →
      (cofinalProductCircularOrder O hz hc).btw (a * b) (a * c) (a * d) := by
    intro a b c d h
    rw [cofinalProductCircularOrder_btw] at h ⊢
    simpa [cofinalProductRepresentative] using
      O.fundamentalRepresentative_mul_circular hz hc cofinalProductZ_central
        (a, 1) (b, 1) (c, 1) (d, 1) h
  constructor
  · intro h
    simpa only [inv_mul_cancel_left] using hforward a⁻¹ (a * b) (a * c) (a * d) h
  · exact hforward a b c d

/-- The circular order on the quotient by the cyclic direct factor is left invariant. -/
noncomputable def cofinalProductCircularGroupOrder : CircularGroupOrder G where
  order := cofinalProductCircularOrder O hz hc
  mul_btw_mul_left := cofinalProductCircularOrder_mul_btw_mul_left O hz hc

end FnZPositiveCones
