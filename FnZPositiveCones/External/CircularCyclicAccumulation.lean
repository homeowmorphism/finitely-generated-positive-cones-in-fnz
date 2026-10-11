module

public import FnZPositiveCones.External.CircularIsolatedDiscrete
public import Mathlib.Topology.DerivedSet
public import Mathlib.Topology.DiscreteSubset

@[expose] public section

/-! Accumulation points of actual cyclic orbits on the line. -/
namespace FnZPositiveCones.OrderedActions

/-- The accumulation points of a strictly increasing integer orbit are fixed
by its generating order automorphism. -/
theorem realAut_zpow_derived_fixed_of_lt (f : ℝ ≃o ℝ) (x : ℝ) (hx : x < f x) :
    derivedSet (Set.range (fun n : ℤ => (f ^ n) x)) ⊆ {y | f y = y} := by
  intro p hp
  have hm := realAut_orbit_strictMono f x hx
  have hstep (n : ℤ) : (f ^ (n + 1)) x = f ((f ^ n) x) := by
    rw [add_comm n 1, zpow_add, zpow_one, realAut_mul_apply]
  have hrange : Set.range (fun n : ℤ => (f ^ n) x) ⊆ {y | y ≤ f y} := by
    rintro y ⟨n, rfl⟩
    have hn := hm (show n < n + 1 by omega)
    dsimp only at hn ⊢
    rw [hstep] at hn
    exact hn.le
  have hple : p ≤ f p := closure_minimal hrange
    (isClosed_le continuous_id f.continuous) (derivedSet_subset_closure _ hp)
  by_contra hne
  have hplt : p < f p := lt_of_le_of_ne hple (Ne.symm hne)
  obtain ⟨c, hpc, hcf⟩ := exists_between hplt
  let U : Set ℝ := Set.Iio c ∩ f ⁻¹' Set.Ioi c
  have hU : U ∈ nhds p :=
    (isOpen_Iio.inter (isOpen_Ioi.preimage f.continuous)).mem_nhds ⟨hpc, hcf⟩
  have hsmall : (Set.range (fun n : ℤ => (f ^ n) x) ∩ U).Subsingleton := by
    rintro a ⟨⟨n, rfl⟩, hn⟩ b ⟨⟨m, rfl⟩, hm'⟩
    rcases lt_trichotomy n m with hnm | rfl | hmn
    · have hle := hm.monotone (show n + 1 ≤ m by omega)
      rw [hstep] at hle
      exact False.elim (not_lt_of_ge hle (hm'.1.trans hn.2))
    · rfl
    · have hle := hm.monotone (show m + 1 ≤ n by omega)
      rw [hstep] at hle
      exact False.elim (not_lt_of_ge hle (hn.1.trans hm'.2))
  exact Set.Infinite.of_accPt (hp.nhds_inter hU) (by
    simpa only [Set.inter_comm] using hsmall.finite)

/-- For any increasing homeomorphism of the line, all accumulation points of
one integer orbit are fixed. There is no global freeness assumption. -/
theorem realAut_zpow_derived_fixed (f : ℝ ≃o ℝ) (x : ℝ) :
    derivedSet (Set.range (fun n : ℤ => (f ^ n) x)) ⊆ {y | f y = y} := by
  rcases lt_trichotomy x (f x) with hx | hx | hx
  · exact realAut_zpow_derived_fixed_of_lt f x hx
  · have hpow (n : ℤ) : (f ^ n) x = x := by
      have hinv : f⁻¹ x = x := by
        apply f.injective
        simpa only [RelIso.apply_inv_self] using hx
      induction n using Int.induction_on with
      | zero => simp
      | succ n ih => simp only [zpow_add, zpow_one, realAut_mul_apply, ih, hx.symm]
      | pred n ih => simp only [zpow_sub, zpow_one, realAut_mul_apply, hinv, ih]
    intro p hp
    have hs : Set.range (fun n : ℤ => (f ^ n) x) = {x} := by
      simp only [hpow, Set.range_const]
    exact False.elim (Set.Infinite.of_accPt hp (hs ▸ Set.finite_singleton x))
  · have hpos : x < f⁻¹ x := by
      change x < f.symm x
      simpa only [f.symm_apply_apply] using f.symm.strictMono hx
    have hsame : Set.range (fun n : ℤ => (f⁻¹ ^ n) x) =
        Set.range (fun n : ℤ => (f ^ n) x) := by
      ext y
      constructor <;> rintro ⟨n, rfl⟩ <;> refine ⟨-n, ?_⟩ <;>
        simp only [inv_zpow, zpow_neg, inv_inv]
    intro p hp
    have hfix : f⁻¹ p = p :=
      realAut_zpow_derived_fixed_of_lt f⁻¹ x hpos (hsame ▸ hp)
    have he := congrArg f hfix
    change f p = p
    simpa only [RelIso.apply_inv_self] using he.symm

/-- An accumulation point of a cyclic group orbit is fixed by every element
of that group, even when the action has a kernel. -/
theorem cyclic_real_orbit_derived_fixed {H : Type*} [Group H] [IsCyclic H]
    (ρ : H →* (ℝ ≃o ℝ)) (x : ℝ) :
    derivedSet (Set.range (fun h => ρ h x)) ⊆ {y | ∀ h, ρ h y = y} := by
  obtain ⟨a, ha⟩ := IsCyclic.exists_generator (α := H)
  have hrange : Set.range (fun h => ρ h x) =
      Set.range (fun n : ℤ => ((ρ a) ^ n) x) := by
    ext y
    constructor
    · rintro ⟨h, rfl⟩
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp (ha h)
      exact ⟨n, by simp only [map_zpow]⟩
    · rintro ⟨n, rfl⟩
      exact ⟨a ^ n, by simp only [map_zpow]⟩
  intro p hp
  have hfix : ρ a p = p := realAut_zpow_derived_fixed (ρ a) x (hrange ▸ hp)
  have hpow (n : ℤ) : ((ρ a) ^ n) p = p := by
    have hinv : (ρ a)⁻¹ p = p := by
      apply (ρ a).injective
      simpa only [RelIso.apply_inv_self] using hfix.symm
    induction n using Int.induction_on with
    | zero => simp
    | succ n ih => simp only [zpow_add, zpow_one, realAut_mul_apply, ih, hfix]
    | pred n ih => simp only [zpow_sub, zpow_one, realAut_mul_apply, hinv, ih]
  intro h
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp (ha h)
  rw [map_zpow, hpow]

end FnZPositiveCones.OrderedActions
