module

public import FnZPositiveCones.Construction.Subgroup

@[expose] public section

/-! The explicit `6*d+1` upper bound for the second positive Schreier generating set. -/

namespace FnZPositiveCones

variable (f : gammaH →* FreeGroup (Fin 2)) (d : ℕ) [NeZero d]
variable (hfC : f gammaC = coverG) (hd : Odd d)

/-- The only nonidentity element needed from the `C` column. -/
def secondCGenerator : secondSubgroup f d := ⟨gammaC ^ d, C_pow_degree_mem f d hfC⟩

/-- The six `A` columns over all `d` representatives, and the single `C` wrap. -/
noncomputable def secondGeneratorFinset : Finset (secondSubgroup f d) := by
  classical
  exact Finset.univ.image (fun p : Fin d × Fin 6 =>
    schreierDelta (C_power_transversal f d hfC hd) (gammaC ^ p.1.val) (gammaA p.2)) ∪
      {secondCGenerator f d hfC}

/-- This is a bound on the explicit finite witness; it asserts no distinctness. -/
theorem secondGeneratorFinset_card_le : (secondGeneratorFinset f d hfC hd).card ≤ 6 * d + 1 := by
  classical
  apply (Finset.card_union_le _ _).trans
  have hi := Finset.card_image_le (s := (Finset.univ : Finset (Fin d × Fin 6)))
    (f := fun p : Fin d × Fin 6 =>
      schreierDelta (C_power_transversal f d hfC hd) (gammaC ^ p.1.val) (gammaA p.2))
  simpa [Finset.card_univ, Fintype.card_prod, mul_comm] using Nat.add_le_add_right hi 1

/-- Every member of the explicit finite witness is positive in the restricted cone. -/
theorem secondGeneratorFinset_positive :
    (secondGeneratorFinset f d hfC hd : Set (secondSubgroup f d)) ⊆
      (secondPositiveCone f d : Set (secondSubgroup f d)) := by
  classical
  intro v hv
  rcases Finset.mem_union.mp hv with hv | hv
  · obtain ⟨⟨k, s⟩, _, rfl⟩ := Finset.mem_image.mp hv
    exact C_A_schreier_positive f d hfC hd k s
  · have hv' : v = secondCGenerator f d hfC := Finset.mem_singleton.mp hv
    subst v
    change gammaC ^ d ∈ gammaPositiveCone
    obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne d)
    rw [hr, pow_succ']
    exact semigroup_mul_pow_mem gammaPositiveCone gammaC_mem_positive gammaC_mem_positive r

/-- The positive Schreier set is contained in the explicit bounded witness. -/
theorem positiveSchreierSet_subset_secondGeneratorFinset :
    positiveSchreierSet (C_power_transversal f d hfC hd) gammaGenerators ⊆
      (secondGeneratorFinset f d hfC hd : Set (secondSubgroup f d)) := by
  classical
  rintro v ⟨t, ⟨k, rfl⟩, s, hs, rfl, hne⟩
  rcases hs with ⟨i, rfl⟩ | hs
  · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨(k, i), Finset.mem_univ _, rfl⟩)
  · have hs' : s = gammaC := hs
    subst s
    by_cases hk : k.val + 1 < d
    · exact (hne (C_C_schreier_before f d hfC hd k hk)).elim
    · apply Finset.mem_union_right
      apply Finset.mem_singleton.mpr
      apply Subtype.ext
      exact C_C_schreier_wrap f d hfC hd k (by omega)

/-- The displayed finite witness generates exactly the second strict positive cone. -/
theorem secondGeneratorFinset_closure (hbase : BaseConeGoal) :
    Subsemigroup.closure (secondGeneratorFinset f d hfC hd : Set (secondSubgroup f d)) =
      secondPositiveCone f d := by
  apply le_antisymm
  · exact Subsemigroup.closure_le.mpr (secondGeneratorFinset_positive f d hfC hd)
  · change Subsemigroup.comap (secondSubgroup f d).subtype.toMulHom gammaPositiveCone ≤ _
    rw [positiveSchreier_closure_eq (C_power_transversal f d hfC hd)
      (CPowerTransversal_one_mem d) (gammaH_positiveCone hbase)
      (gammaH_positive_generators hbase).symm (secondSchreier_positive f d hfC hd)]
    exact Subsemigroup.closure_mono (positiveSchreierSet_subset_secondGeneratorFinset f d hfC hd)

include hfC hd

/-- K06: at most six generators per representative and the single positive wrap factor. -/
theorem secondCone_generator_bound (hbase : BaseConeGoal) :
    ∃ S : Finset (secondSubgroup f d), S.card ≤ 6 * d + 1 ∧
      Subsemigroup.closure (S : Set (secondSubgroup f d)) = secondPositiveCone f d :=
  ⟨secondGeneratorFinset f d hfC hd, secondGeneratorFinset_card_le f d hfC hd,
    secondGeneratorFinset_closure f d hfC hd hbase⟩

theorem secondSubgroup_hasFGPositiveConeWithBound (hbase : BaseConeGoal) :
    HasFGPositiveConeWithBound (secondSubgroup f d) (6 * d + 1) := by
  obtain ⟨S, hcard, hS⟩ := secondCone_generator_bound f d hfC hd hbase
  exact ⟨S, hcard, hS.symm ▸ (secondSubgroupFGCone f d hfC hd hbase).1⟩

end FnZPositiveCones
