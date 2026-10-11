module

public import FnZPositiveCones.Cover.Modular
public import FnZPositiveCones.Gamma.PositiveCone

@[expose] public section

/-! The second positive Schreier construction, with its marked projection explicit. -/

namespace FnZPositiveCones

variable (f : gammaH →* FreeGroup (Fin 2)) (d : ℕ) [NeZero d]

/-- The second subgroup is a subgroup of the first subgroup, not of the ambient presentation. -/
def secondSubgroup : Subgroup gammaH := (coverSubgroup d).comap f

@[simp] theorem mem_secondSubgroup (w : gammaH) :
    w ∈ secondSubgroup f d ↔ modularRightAction d 0 (f w) = 0 := Iff.rfl

theorem secondSubgroup_index (hf : Function.Surjective f) : (secondSubgroup f d).index = d := by
  exact ((coverSubgroup d).index_comap_of_surjective hf).trans (cover_stabilizer_index d)

theorem secondSubgroup_mul_inv_mem_iff (w v : gammaH) :
    w * v⁻¹ ∈ secondSubgroup f d ↔
      modularRightAction d 0 (f w) = modularRightAction d 0 (f v) := by
  change f (w * v⁻¹) ∈ coverSubgroup d ↔ _
  rw [map_mul, map_inv, modularRightAction_eq_iff_mul_inv_mem]

/-- Representatives in the first subgroup indexed by bounded powers of its marked `C`. -/
def CPowerTransversal (d : ℕ) : Set gammaH := Set.range (fun k : Fin d => gammaC ^ k.val)

omit [NeZero d] in
theorem CPowerTransversal_finite : (CPowerTransversal d).Finite := Set.finite_range _

theorem CPowerTransversal_one_mem : (1 : gammaH) ∈ CPowerTransversal d := by
  exact ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩, by simp⟩

variable (hfC : f gammaC = coverG)

include hfC

theorem C_power_state (k : ℕ) :
    modularRightAction d 0 (f (gammaC ^ k)) = 2 * (k : ZMod d) := by
  simp [hfC]

theorem C_pow_degree_mem : gammaC ^ d ∈ secondSubgroup f d := by
  rw [mem_secondSubgroup, C_power_state f d hfC]
  simp

/-- Oddness supplies both existence and uniqueness of the right-coset representatives. -/
theorem C_power_transversal (hd : Odd d) :
    Subgroup.IsComplement (secondSubgroup f d : Set gammaH) (CPowerTransversal d) := by
  rw [Subgroup.isComplement_iff_existsUnique_mul_inv_mem]
  intro w
  obtain ⟨k, hk⟩ := (doubling_fin_bijective d hd).surjective (modularRightAction d 0 (f w))
  refine ⟨⟨gammaC ^ k.val, ⟨k, rfl⟩⟩, ?_, ?_⟩
  · change w * (gammaC ^ k.val)⁻¹ ∈ secondSubgroup f d
    rw [secondSubgroup_mul_inv_mem_iff, C_power_state f d hfC]
    exact hk.symm
  · rintro ⟨t, ⟨j, rfl⟩⟩ hj
    apply Subtype.ext
    have hj' := (secondSubgroup_mul_inv_mem_iff f d _ _).mp hj
    rw [C_power_state f d hfC] at hj'
    have he : j = k := (doubling_fin_bijective d hd).injective (hj'.symm.trans hk.symm)
    exact congrArg (fun i : Fin d => gammaC ^ i.val) he

omit hfC in
/-- The sandwich computation takes place in the presented group, with integer subtraction. -/
theorem C_A_sandwich (k k' : ℕ) (s : Fin 6) :
    (((gammaC ^ k * gammaA s * (gammaC ^ k')⁻¹ : gammaH) : Gamma2)) =
      bGamma ^ (6 * (k : ℤ) - s.val) * aGamma *
        bGamma ^ (((s.val + 2) % 6 : ℕ) - 6 * (k' : ℤ)) := by
  simp only [Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_inv, gammaC_coe, gammaA_coe]
  push_cast
  group
  push_cast
  group

/-- Every `A` column is strictly positive in the first subgroup's cone. -/
theorem C_A_schreier_positive (hd : Odd d) (k : Fin d) (s : Fin 6) :
    (schreierDelta (G := gammaH) (C_power_transversal f d hfC hd) (gammaC ^ k.val) (gammaA s) : gammaH)
      ∈ gammaPositiveCone := by
  have hrep := rightRep_mem (C_power_transversal f d hfC hd) (gammaC ^ k.val * gammaA s)
  obtain ⟨k', hk'⟩ := hrep
  change (((gammaC ^ k.val * gammaA s *
    (rightRep (C_power_transversal f d hfC hd) (gammaC ^ k.val * gammaA s))⁻¹ : gammaH) :
      Gamma2)) ∈ basePositiveClosure
  rw [← hk', C_A_sandwich]
  exact gamma_sandwich_mem _ _

/-- Before the last representative, the `C` Schreier factor is the identity. -/
theorem C_C_schreier_before (hd : Odd d) (k : Fin d) (hk : k.val + 1 < d) :
    schreierDelta (G := gammaH) (C_power_transversal f d hfC hd) (gammaC ^ k.val) gammaC = 1 := by
  apply Subtype.ext
  change gammaC ^ k.val * gammaC *
    (rightRep (C_power_transversal f d hfC hd) (gammaC ^ k.val * gammaC))⁻¹ = 1
  have hmem : gammaC ^ k.val * gammaC ∈ CPowerTransversal d :=
    ⟨⟨k.val + 1, hk⟩, pow_succ _ _⟩
  rw [rightRep_of_mem _ hmem, mul_inv_cancel]

/-- At the last representative, the factor wraps to the positive power `C^d`. -/
theorem C_C_schreier_wrap (hd : Odd d) (k : Fin d) (hk : k.val + 1 = d) :
    (schreierDelta (G := gammaH) (C_power_transversal f d hfC hd) (gammaC ^ k.val) gammaC : gammaH) =
      gammaC ^ d := by
  change gammaC ^ k.val * gammaC *
    (rightRep (C_power_transversal f d hfC hd) (gammaC ^ k.val * gammaC))⁻¹ = _
  rw [← pow_succ, hk, rightRep_of_mem_subgroup _ (CPowerTransversal_one_mem d)
    (C_pow_degree_mem f d hfC), inv_one, mul_one]

/-- The `C` column is identity or positive, including its only case when `d = 1`. -/
theorem C_C_schreier_positive (hd : Odd d) (k : Fin d) :
    schreierDelta (G := gammaH) (C_power_transversal f d hfC hd) (gammaC ^ k.val) gammaC = 1 ∨
    (schreierDelta (G := gammaH) (C_power_transversal f d hfC hd) (gammaC ^ k.val) gammaC : gammaH)
      ∈ gammaPositiveCone := by
  by_cases hk : k.val + 1 < d
  · exact Or.inl (C_C_schreier_before f d hfC hd k hk)
  · right
    rw [C_C_schreier_wrap f d hfC hd k (by omega)]
    obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne d)
    rw [hr, pow_succ']
    exact semigroup_mul_pow_mem gammaPositiveCone gammaC_mem_positive gammaC_mem_positive r

/-- All Schreier columns meet the positive-generation contract. -/
theorem secondSchreier_positive (hd : Odd d) :
    ∀ t ∈ CPowerTransversal d, ∀ s ∈ gammaGenerators,
      schreierDelta (G := gammaH) (C_power_transversal f d hfC hd) t s = 1 ∨
        (schreierDelta (G := gammaH) (C_power_transversal f d hfC hd) t s : gammaH) ∈ gammaPositiveCone := by
  rintro t ⟨k, rfl⟩ s (⟨i, rfl⟩ | hs)
  · exact Or.inr (C_A_schreier_positive f d hfC hd k i)
  · have hs' : s = gammaC := hs
    subst s
    exact C_C_schreier_positive f d hfC hd k

/-- The cone on the second subgroup, preserving the subgroup tower. -/
def secondPositiveCone : Subsemigroup (secondSubgroup f d) :=
  Subsemigroup.comap (secondSubgroup f d).subtype.toMulHom gammaPositiveCone

/-- Positive Schreier rewriting proves finite semigroup generation of the restricted cone. -/
theorem secondSubgroupFGCone (hd : Odd d) (hbase : BaseConeGoal) :
    IsPositiveCone (secondPositiveCone f d) ∧ SemigroupFG (secondPositiveCone f d) := by
  constructor
  · exact positiveCone_restrict _ (gammaH_positiveCone hbase)
  · exact positiveSchreier_finiteGeneration (C_power_transversal f d hfC hd)
      (CPowerTransversal_one_mem d) (gammaH_positiveCone hbase)
      (gammaH_positive_generators hbase).symm (secondSchreier_positive f d hfC hd)
      (CPowerTransversal_finite d) gammaGenerators_finite

/-- The second subgroup therefore has a finitely generated strict positive cone. -/
theorem secondSubgroup_hasFGPositiveCone (hd : Odd d) (hbase : BaseConeGoal) :
    HasFGPositiveCone (secondSubgroup f d) := by
  obtain ⟨hp, S, hS⟩ := secondSubgroupFGCone f d hfC hd hbase
  exact ⟨S, hS.symm ▸ hp⟩

end FnZPositiveCones
