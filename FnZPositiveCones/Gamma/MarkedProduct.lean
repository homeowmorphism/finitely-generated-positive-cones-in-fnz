module

public import FnZPositiveCones.Gamma.Schreier
public import FnZPositiveCones.Gamma.Certificate

@[expose] public section

/-! Relations and the surjective marked evaluation map, independently of positivity. -/
namespace FnZPositiveCones

theorem gammaA_zero_relation : gammaA 0 = gammaC * gammaA 5 * gammaA 1 := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul, gammaA_coe, gammaC_coe]
  norm_num
  calc
    aGamma * bGamma ^ 2 = (bGamma * aGamma ^ 2 * bGamma) * bGamma ^ 2 := by
      rw [gamma_relation]
    _ = _ := by simp only [pow_succ, pow_zero]; group

theorem gammaA_one_relation : gammaA 1 = gammaA 0 * gammaA 2 := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul, gammaA_coe]
  norm_num
  conv_lhs => rw [gamma_inverse_mul_a]
  simp only [pow_succ, pow_zero]
  group

theorem gammaA_two_relation : gammaA 2 = gammaA 1 * gammaA 3 := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul, gammaA_coe]
  norm_num
  calc
    _ = bGamma⁻¹ * (bGamma⁻¹ * aGamma) * bGamma ^ 4 := by group
    _ = _ := by
      conv_lhs => rw [gamma_inverse_mul_a]
      simp only [pow_succ, pow_zero]
      group

theorem gammaA_three_relation : gammaA 3 = gammaA 2 * gammaA 4 * gammaC := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul, gammaA_coe, gammaC_coe]
  norm_num
  calc
    _ = bGamma ^ (-2 : ℤ) * (bGamma⁻¹ * aGamma) * bGamma ^ 5 := by group
    _ = _ := by
      conv_lhs => rw [gamma_inverse_mul_a]
      simp only [pow_succ, pow_zero]
      group

theorem gammaA_four_relation : gammaA 4 = gammaA 3 * gammaA 5 := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul, gammaA_coe]
  norm_num
  calc
    _ = bGamma ^ (-3 : ℤ) * (bGamma⁻¹ * aGamma) := by group
    _ = _ := by
      conv_lhs => rw [gamma_inverse_mul_a]
      simp only [pow_succ, pow_zero]
      group

theorem gammaA_five_relation : gammaA 5 = gammaA 4 * gammaA 0 := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul, gammaA_coe]
  norm_num
  calc
    _ = bGamma ^ (-4 : ℤ) * (bGamma⁻¹ * aGamma) * bGamma := by group
    _ = _ := by
      conv_lhs => rw [gamma_inverse_mul_a]
      simp only [pow_succ, pow_zero]
      group

theorem gammaX_word : gammaX = gammaA 0 := by
  apply Subtype.ext
  simp

theorem gammaZ_word : gammaZ = gammaA 0 * gammaA 2 * gammaA 4 := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul, gammaA_coe, gammaZ_coe]
  norm_num
  simp only [pow_succ, pow_zero]
  group

theorem gammaY0_word : gammaY0 = gammaA 0 * gammaA 2 ^ 2 * gammaA 4 := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_pow, gammaA_coe, gammaY0_coe]
  norm_num
  simp only [pow_succ, pow_zero]
  group
  simp [pow_two, mul_assoc]

theorem gammaA_two_expansion :
    gammaA 2 = gammaX⁻¹ * gammaY0 * gammaZ⁻¹ * gammaX := by
  rw [gammaX_word, gammaY0_word, gammaZ_word]
  group

theorem gammaA_one_expansion : gammaA 1 = gammaX * gammaA 2 := by
  rw [gammaX_word, gammaA_one_relation]

theorem gammaA_four_expansion : gammaA 4 = (gammaA 2)⁻¹ * gammaX⁻¹ * gammaZ := by
  rw [gammaX_word, gammaZ_word]
  group

theorem gammaA_five_expansion : gammaA 5 = gammaA 4 * gammaX := by
  rw [gammaX_word, gammaA_five_relation]

theorem gammaA_three_expansion : gammaA 3 = (gammaA 1)⁻¹ * gammaA 2 := by
  conv_rhs => rw [gammaA_two_relation]
  group

theorem gammaC_expansion : gammaC = (gammaA 2 * gammaA 4)⁻¹ * gammaA 3 := by
  rw [gammaA_three_relation]
  group

/-- Evaluation of the two free generators at the marked subgroup elements. -/
def gammaFreeEval : FreeGroup (Fin 2) →* gammaH := FreeGroup.lift ![gammaX, gammaY0]

/-- Centrality of `gammaZ` makes evaluation on the direct product multiplicative. -/
def markedProduct_to_H : FnZ 2 →* gammaH :=
  gammaFreeEval.noncommCoprod (zpowersHom gammaH gammaZ)
    (fun w z => (gammaZ_commute (gammaFreeEval w)).symm.zpow_right z.toAdd)

theorem markedProduct_to_H_apply (p : FnZ 2) :
    markedProduct_to_H p = gammaFreeEval p.1 * gammaZ ^ p.2.toAdd := rfl

@[simp] theorem markedProduct_to_H_X : markedProduct_to_H productX = gammaX := by
  simp [markedProduct_to_H, productX, gammaFreeEval]

@[simp] theorem markedProduct_to_H_Y : markedProduct_to_H productY = gammaY0 := by
  simp [markedProduct_to_H, productY, gammaFreeEval]

@[simp] theorem markedProduct_to_H_Z : markedProduct_to_H productZ = gammaZ := by
  change gammaFreeEval 1 * gammaZ ^ (1 : ℤ) = gammaZ
  simp

theorem markedProduct_to_H_surjective : Function.Surjective markedProduct_to_H := by
  rw [← MonoidHom.range_eq_top]
  apply top_unique
  rw [← gammaH_generators]
  apply (Subgroup.closure_le _).2
  have hx : gammaX ∈ markedProduct_to_H.range := ⟨productX, markedProduct_to_H_X⟩
  have hy : gammaY0 ∈ markedProduct_to_H.range := ⟨productY, markedProduct_to_H_Y⟩
  have hz : gammaZ ∈ markedProduct_to_H.range := ⟨productZ, markedProduct_to_H_Z⟩
  have h0 : gammaA 0 ∈ markedProduct_to_H.range := gammaX_word ▸ hx
  have h2 : gammaA 2 ∈ markedProduct_to_H.range := by
    rw [gammaA_two_expansion]
    exact markedProduct_to_H.range.mul_mem
      (markedProduct_to_H.range.mul_mem
        (markedProduct_to_H.range.mul_mem (markedProduct_to_H.range.inv_mem hx) hy)
        (markedProduct_to_H.range.inv_mem hz)) hx
  have h1 : gammaA 1 ∈ markedProduct_to_H.range := by
    rw [gammaA_one_expansion]
    exact markedProduct_to_H.range.mul_mem hx h2
  have h4 : gammaA 4 ∈ markedProduct_to_H.range := by
    rw [gammaA_four_expansion]
    exact markedProduct_to_H.range.mul_mem
      (markedProduct_to_H.range.mul_mem (markedProduct_to_H.range.inv_mem h2)
        (markedProduct_to_H.range.inv_mem hx)) hz
  have h5 : gammaA 5 ∈ markedProduct_to_H.range := by
    rw [gammaA_five_expansion]
    exact markedProduct_to_H.range.mul_mem h4 hx
  have h3 : gammaA 3 ∈ markedProduct_to_H.range := by
    rw [gammaA_three_expansion]
    exact markedProduct_to_H.range.mul_mem (markedProduct_to_H.range.inv_mem h1) h2
  rintro k (⟨s, rfl⟩ | hk)
  · fin_cases s <;> assumption
  · have hk' : k = gammaC := hk
    subst k
    rw [gammaC_expansion]
    exact markedProduct_to_H.range.mul_mem
      (markedProduct_to_H.range.inv_mem (markedProduct_to_H.range.mul_mem h2 h4)) h3

end FnZPositiveCones
