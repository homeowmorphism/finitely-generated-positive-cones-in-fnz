module

public import FnZPositiveCones.Gamma.Schreier
public import FnZPositiveCones.Cone.Basic

@[expose] public section

/-! Restriction of the base cone, with its external hypothesis kept explicit. -/
namespace FnZPositiveCones

def gammaPositiveCone : Subsemigroup gammaH :=
  Subsemigroup.comap gammaH.subtype.toMulHom basePositiveClosure

theorem gammaH_positiveCone (hbase : BaseConeGoal) : IsPositiveCone gammaPositiveCone :=
  positiveCone_restrict gammaH hbase

theorem gammaA_mem_positive (s : Fin 6) : gammaA s ∈ gammaPositiveCone := by
  change (gammaA s : Gamma2) ∈ basePositiveClosure
  simpa only [gammaA_coe, zpow_natCast] using
    gamma_sandwich_mem (-(s.val : ℤ)) (((s.val + 2) % 6 : ℕ) : ℤ)

theorem gammaC_mem_positive : gammaC ∈ gammaPositiveCone :=
  gamma_positive_power_mem 6 (by decide)

theorem gammaGenerators_positive : gammaGenerators ⊆ gammaPositiveCone := by
  rintro k (⟨s, rfl⟩ | hk)
  · exact gammaA_mem_positive s
  · have hk' : k = gammaC := hk
    subst k
    exact gammaC_mem_positive

theorem gammaSchreier_positive :
    ∀ t ∈ gammaTransversal, ∀ v ∈ ({aGamma, bGamma} : Set Gamma2),
      schreierDelta gammaTransversal_isComplement t v = 1 ∨
        (schreierDelta gammaTransversal_isComplement t v : Gamma2) ∈ basePositiveClosure := by
  rintro t ⟨s, rfl⟩ v (rfl | hv)
  · exact Or.inr (by rw [gammaSchreier_a]; exact gammaA_mem_positive s)
  · have hv' : v = bGamma := hv
    subst v
    rw [gammaSchreier_b]
    split_ifs
    · exact Or.inr gammaC_mem_positive
    · exact Or.inl rfl

/-- The seven specified elements generate the restricted cone as a semigroup. -/
theorem gammaH_positive_generators (hbase : BaseConeGoal) :
    Subsemigroup.closure gammaGenerators = gammaPositiveCone := by
  apply le_antisymm
  · exact Subsemigroup.closure_le.mpr gammaGenerators_positive
  · change Subsemigroup.comap gammaH.subtype.toMulHom basePositiveClosure ≤ _
    rw [positiveSchreier_closure_eq gammaTransversal_isComplement
      gammaTransversal_one_mem hbase rfl gammaSchreier_positive]
    apply Subsemigroup.closure_le.mpr
    rintro k ⟨t, ⟨s, rfl⟩, v, hv, rfl, hne⟩
    rcases hv with rfl | hv
    · rw [gammaSchreier_a]
      exact Subsemigroup.subset_closure (Or.inl ⟨s, rfl⟩)
    · have hv' : v = bGamma := hv
      subst v
      rw [gammaSchreier_b] at *
      split_ifs at * with hs
      · exact Subsemigroup.subset_closure (Or.inr rfl)
      · exact False.elim (hne rfl)

theorem gammaGenerators_finite : gammaGenerators.Finite :=
  (Set.finite_range gammaA).union (Set.finite_singleton gammaC)

theorem gammaH_positive_fg (hbase : BaseConeGoal) : SemigroupFG gammaPositiveCone := by
  classical
  refine ⟨gammaGenerators_finite.toFinset, ?_⟩
  rw [gammaGenerators_finite.coe_toFinset]
  exact gammaH_positive_generators hbase

theorem gammaH_hasFGPositiveCone (hbase : BaseConeGoal) : HasFGPositiveCone gammaH := by
  obtain ⟨S, hS⟩ := gammaH_positive_fg hbase
  exact ⟨S, hS.symm ▸ gammaH_positiveCone hbase⟩

end FnZPositiveCones
