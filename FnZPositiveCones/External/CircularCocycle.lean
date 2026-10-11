module

public import FnZPositiveCones.External.CircularQuotient
public import FnZPositiveCones.External.CocycleExtension

@[expose] public section

/-! The normalized integer carry cocycle of a left-invariant circular order. -/

namespace FnZPositiveCones

universe u

namespace CircularCarry

variable {A : Type u} [CircularOrder A]

/-- Distinct triples have exactly one strict circular orientation. -/
theorem strict_or_reverse {a b c : A} (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a) :
    sbtw a b c ∨ sbtw c b a := by
  rcases btw_total a b c with h | h
  · left
    apply h.sbtw_of_not_btw
    intro hr
    rcases h.antisymm hr with he | he | he
    · exact hab he
    · exact hbc he
    · exact hca he
  · right
    apply h.sbtw_of_not_btw
    intro hr
    rcases hr.antisymm h with he | he | he
    · exact hab he
    · exact hbc he
    · exact hca he

/-- The carry associated with a triple, including all degenerate cases. -/
noncomputable def value (a b c : A) : ℤ := by
  classical
  exact if a = b then 0 else if b = c then 0 else if a = c then 1
    else if sbtw a b c then 0 else 1

/-- The two orientations on a distinct triple give complementary carries. -/
theorem distinct_reverse_sum {a b c : A} (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a) :
    value a b c + value c b a = 1 := by
  classical
  rcases strict_or_reverse hab hbc hca with h | h
  · simp [value, hab, hbc, hca, Ne.symm, h, h.not_sbtw]
  · simp [value, hab, hbc, hca, Ne.symm, h, h.not_sbtw]

/-- On distinct triples the carry is unchanged by cyclic permutation. -/
theorem distinct_cyclic {a b c : A} (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a) :
    value a b c = value b c a := by
  classical
  simp only [value, hab, hbc, hca, (Ne.symm hab), (Ne.symm hca), ↓reduceIte]
  rw [show sbtw a b c ↔ sbtw b c a from ⟨fun h => h.cyclic_left, fun h => h.cyclic_right⟩]

/-- The four-point carry identity on four distinct points. -/
theorem fourpoint_distinct {a b c d : A}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    value a b c + value a c d = value b c d + value a b d := by
  classical
  have h₁ := strict_or_reverse hab hbc (Ne.symm hac)
  have h₂ := strict_or_reverse hac hcd (Ne.symm had)
  have h₃ := strict_or_reverse hbc hcd (Ne.symm hbd)
  have h₄ := strict_or_reverse hab hbd (Ne.symm had)
  rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂ <;>
    rcases h₃ with h₃ | h₃ <;> rcases h₄ with h₄ | h₄ <;>
    simp only [value, hab, hac, had, hbc, hbd, hcd, ↓reduceIte, h₁, h₂, h₃, h₄,
      h₁.not_sbtw, h₂.not_sbtw, h₃.not_sbtw, h₄.not_sbtw] <;>
    first | omega | grind [sbtw_cyclic_left, sbtw_trans_left, sbtw_trans_right, sbtw_asymm]

@[simp] theorem value_self_left (a b : A) : value a a b = 0 := by simp [value]
@[simp] theorem value_self_right (a b : A) : value a b b = 0 := by simp [value]

@[simp] theorem value_return {a b : A} (hab : a ≠ b) : value a b a = 1 := by
  simp [value, hab, (Ne.symm hab)]

/-- The four-point identity, with degeneracies explicitly included. -/
theorem fourpoint (a b c d : A) :
    value a b c + value a c d = value b c d + value a b d := by
  classical
  by_cases hab : a = b
  · subst b; simp
  by_cases hbc : b = c
  · subst c; simp
  by_cases hcd : c = d
  · subst d; simp
  by_cases hac : a = c
  · subst c
    by_cases hbd : b = d
    · subst d; simp [hab, (Ne.symm hab)]
    have hcy := distinct_cyclic (a := d) (b := b) (c := a) (Ne.symm hbd) (Ne.symm hab) hcd
    have hs := distinct_reverse_sum hab hbd (Ne.symm hcd)
    rw [hcy] at hs
    simpa only [value_return hab, value_self_left, add_zero, zero_add, add_comm] using hs.symm
  by_cases had : a = d
  · subst d
    rw [distinct_cyclic hab hbc (Ne.symm hac)]
    simp [hab, hac]
  by_cases hbd : b = d
  · subst d
    have hcy := distinct_cyclic (a := a) (b := c) (c := b) hac (Ne.symm hbc) (Ne.symm hab)
    rw [hcy, value_return hbc, value_self_right, add_zero]
    exact distinct_reverse_sum hab hbc (Ne.symm hac)
  exact fourpoint_distinct hab hac had hbc hbd hcd

theorem value_nonneg_le_one (a b c : A) : 0 ≤ value a b c ∧ value a b c ≤ 1 := by
  classical
  simp only [value]
  split_ifs <;> omega

end CircularCarry

variable {G : Type u} [Group G]

/-- The carry is invariant under every left translation. -/
theorem CircularGroupOrder.carry_mul_left (O : CircularGroupOrder G) (a b c d : G) :
    @CircularCarry.value G O.order (a * b) (a * c) (a * d) =
      @CircularCarry.value G O.order b c d := by
  classical
  simp only [CircularCarry.value, mul_left_cancel_iff, O.mul_sbtw_mul_left]

/-- The usual cut at the identity gives an actual normalized integer two-cocycle. -/
noncomputable def CircularGroupOrder.toNormalizedIntCocycle (O : CircularGroupOrder G) :
    NormalizedIntCocycle G where
  value g h := @CircularCarry.value G O.order 1 g (g * h)
  one_left g := by simp
  one_right g := by simp
  cocycle g h k := by
    let := O.order
    have hv := CircularCarry.fourpoint (1 : G) g (g * h) (g * h * k)
    have he : CircularCarry.value g (g * h) (g * h * k) = CircularCarry.value 1 h (h * k) := by
      simpa only [mul_one, mul_assoc] using O.carry_mul_left g 1 h (h * k)
    rw [he] at hv
    simpa only [mul_assoc] using hv

/-- The constructed cocycle has exactly the range and inverse carry needed for its strict cone. -/
theorem CircularGroupOrder.toNormalizedIntCocycle_isCircular (O : CircularGroupOrder G) :
    O.toNormalizedIntCocycle.IsCircular := by
  let := O.order
  constructor
  · intro g h
    exact @CircularCarry.value_nonneg_le_one G O.order 1 g (g * h)
  · intro g hg
    change @CircularCarry.value G O.order 1 g (g * g⁻¹) = 1
    rw [mul_inv_cancel]
    exact CircularCarry.value_return hg.symm

end FnZPositiveCones
