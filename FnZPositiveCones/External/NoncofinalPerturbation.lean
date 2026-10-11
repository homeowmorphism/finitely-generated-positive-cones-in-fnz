module

public import FnZPositiveCones.External.CircularQuotient
public import FnZPositiveCones.External.NoncofinalDynamics

@[expose] public section

/-!
# Checked interval modifications for the noncofinal argument

An order automorphism preserving an order-connected set can be cut off to that
set. If a second automorphism preserves the set and commutes with the original
map, it also commutes with the cut-off map. These are the gluing and centrality
requirements for the local modification in MMRT Proposition 4.12, Claim 4.
-/

namespace FnZPositiveCones
namespace NoncofinalPerturbation

universe u
variable {A : Type u} [LinearOrder A]

noncomputable def cutMap (f : A ≃o A) (I : Set A) (x : A) : A := by
  classical
  exact if x ∈ I then f x else x

theorem cutMap_strictMono (f : A ≃o A) (I : Set A) (hI : Set.OrdConnected I)
    (hf : ∀ x : A, x ∈ I ↔ f x ∈ I) : StrictMono (cutMap f I) := by
  classical
  intro x y hxy
  by_cases hx : x ∈ I <;> by_cases hy : y ∈ I
  · simpa only [cutMap, hx, hy, ↓reduceIte] using f.strictMono hxy
  · simp only [cutMap, hx, hy, ↓reduceIte]
    apply lt_of_not_ge
    intro h
    exact hy (hI.out hx ((hf x).mp hx) ⟨hxy.le, h⟩)
  · simp only [cutMap, hx, hy, ↓reduceIte]
    apply lt_of_not_ge
    intro h
    exact hx (hI.out ((hf y).mp hy) hy ⟨h, hxy.le⟩)
  · simpa only [cutMap, hx, hy, ↓reduceIte] using hxy

/-- An invariant interval allows exact gluing of an order automorphism with the
identity. The inverse is obtained by the same construction with `f.symm`. -/
noncomputable def truncate (f : A ≃o A) (I : Set A) (hI : Set.OrdConnected I)
    (hf : ∀ x : A, x ∈ I ↔ f x ∈ I) : A ≃o A :=
  (cutMap_strictMono f I hI hf).orderIsoOfRightInverse _ (cutMap f.symm I) (by
    classical
    intro x
    by_cases hx : x ∈ I
    · have hi : f.symm x ∈ I := (hf (f.symm x)).mpr (by simpa using hx)
      simp only [cutMap, hx, hi, ↓reduceIte, f.apply_symm_apply]
    · simp only [cutMap, hx, ↓reduceIte])

@[simp] theorem truncate_apply (f : A ≃o A) (I : Set A) (hI : Set.OrdConnected I)
    (hf : ∀ x : A, x ∈ I ↔ f x ∈ I) (x : A) :
    truncate f I hI hf x = cutMap f I x := rfl

theorem truncate_of_mem (f : A ≃o A) (I : Set A) (hI : Set.OrdConnected I)
    (hf : ∀ x : A, x ∈ I ↔ f x ∈ I) {x : A} (hx : x ∈ I) :
    truncate f I hI hf x = f x := by simp [cutMap, hx]

theorem truncate_of_not_mem (f : A ≃o A) (I : Set A) (hI : Set.OrdConnected I)
    (hf : ∀ x : A, x ∈ I ↔ f x ∈ I) {x : A} (hx : x ∉ I) :
    truncate f I hI hf x = x := by simp [cutMap, hx]

/-- A commuting automorphism that preserves the interval still commutes with
the truncated map. This verifies the central relation after local modification. -/
theorem truncate_commute (f q : A ≃o A) (I : Set A) (hI : Set.OrdConnected I)
    (hf : ∀ x : A, x ∈ I ↔ f x ∈ I) (hq : ∀ x : A, x ∈ I ↔ q x ∈ I)
    (hc : Commute f q) : Commute (truncate f I hI hf) q := by
  change truncate f I hI hf * q = q * truncate f I hI hf
  ext x
  change truncate f I hI hf (q x) = q (truncate f I hI hf x)
  by_cases hx : x ∈ I
  · rw [truncate_of_mem _ _ _ _ ((hq x).mp hx), truncate_of_mem _ _ _ _ hx]
    exact congrArg (fun e : A ≃o A => e x) hc.eq
  · have hqx : q x ∉ I := fun h => hx ((hq x).mpr h)
    rw [truncate_of_not_mem _ _ _ _ hqx, truncate_of_not_mem _ _ _ _ hx]

/-- Fixing the endpoints guarantees the interval-invariance needed for gluing. -/
theorem invariant_Ioo_of_fixed (f : A ≃o A) (a b : A)
    (ha : f a = a) (hb : f b = b) (x : A) :
    x ∈ Set.Ioo a b ↔ f x ∈ Set.Ioo a b := by
  have h : (f a < f x ∧ f x < f b) ↔ (a < x ∧ x < b) :=
    and_congr f.lt_iff_lt f.lt_iff_lt
  simpa only [Set.mem_Ioo, ha, hb] using h.symm

/-- Fixed interval endpoints remain fixed by all integer powers. -/
theorem invariant_Ioo_zpow (f : ℝ ≃o ℝ) (l r : ℝ)
    (hl : f l = l) (hr : f r = r) (k : ℤ) (x : ℝ) :
    x ∈ Set.Ioo l r ↔ (f ^ k) x ∈ Set.Ioo l r := by
  apply invariant_Ioo_of_fixed
  · exact NoncofinalDynamics.fixed_zpow (MonoidHom.id _) f hl k
  · exact NoncofinalDynamics.fixed_zpow (MonoidHom.id _) f hr k

/-- On an interval with no fixed points, integer iterates of any point reach
below every other point. A hypothetical finite lower bound would be a fixed point. -/
theorem exists_zpow_lt_of_no_fixed (f : ℝ ≃o ℝ) (l r : ℝ)
    (hfix : ∀ x ∈ Set.Ioo l r, f x ≠ x) {y t : ℝ}
    (hy : y ∈ Set.Ioo l r) (ht : t ∈ Set.Ioo l r) :
    ∃ k : ℤ, (f ^ k) y < t := by
  by_contra hn
  have hb : BddBelow (Set.range (fun k : ℤ => (f ^ k) y)) := by
    refine ⟨t, ?_⟩
    rintro _ ⟨k, rfl⟩
    exact le_of_not_gt (fun hk => hn ⟨k, hk⟩)
  have htl : t ≤ sInf (Set.range (fun k : ℤ => (f ^ k) y)) := by
    apply le_csInf (Set.range_nonempty _)
    rintro _ ⟨k, rfl⟩
    exact le_of_not_gt (fun hk => hn ⟨k, hk⟩)
  have hly : sInf (Set.range (fun k : ℤ => (f ^ k) y)) ≤ y := csInf_le hb ⟨0, by simp⟩
  exact hfix _ ⟨ht.1.trans_le htl, hly.trans_lt hy.2⟩
    (NoncofinalDynamics.orbit_sInf_fixed (MonoidHom.id _) f y hb)

/-- The final local modification of MMRT Claim 4: an interval-supported power
composed with a map entering the interval acquires an interior fixed point.
The existence is proved by the intermediate value theorem. -/
theorem exists_fixed_truncate_zpow_mul (f a : ℝ ≃o ℝ) (l r : ℝ)
    (hl : f l = l) (hr : f r = r)
    (hfix : ∀ x ∈ Set.Ioo l r, f x ≠ x) (ha : a l ∈ Set.Ioo l r) :
    ∃ k : ℤ, ∃ x ∈ Set.Ioo l r,
      (truncate (f ^ k) (Set.Ioo l r) (Set.ordConnected_Ioo)
        (invariant_Ioo_zpow f l r hl hr k) * a) x = x := by
  have hlar : l < a.symm r := a.lt_iff_lt.mp (by simpa using ha.2)
  obtain ⟨t, hlt, ht⟩ := exists_between (lt_min (ha.1.trans ha.2) hlar)
  have htr : t < r := (lt_min_iff.mp ht).1
  have hat : a t ∈ Set.Ioo l r := by
    refine ⟨ha.1.trans (a.strictMono hlt), ?_⟩
    simpa using a.strictMono (lt_min_iff.mp ht).2
  obtain ⟨k, hk⟩ := exists_zpow_lt_of_no_fixed f l r hfix hat ⟨hlt, htr⟩
  let b : ℝ ≃o ℝ := truncate (f ^ k) (Set.Ioo l r) (Set.ordConnected_Ioo)
    (invariant_Ioo_zpow f l r hl hr k) * a
  have hbl : l < b l := by
    change l < truncate (f ^ k) (Set.Ioo l r) Set.ordConnected_Ioo
      (invariant_Ioo_zpow f l r hl hr k) (a l)
    rw [truncate_of_mem _ _ _ _ ha]
    exact ((invariant_Ioo_zpow f l r hl hr k (a l)).mp ha).1
  have hbt : b t < t := by
    change truncate (f ^ k) (Set.Ioo l r) Set.ordConnected_Ioo
      (invariant_Ioo_zpow f l r hl hr k) (a t) < t
    rwa [truncate_of_mem _ _ _ _ hat]
  obtain ⟨x, hx, hbx⟩ := exists_mem_Icc_isFixedPt b.continuous.continuousOn hlt.le hbl.le hbt.le
  refine ⟨k, x, ⟨?_, hx.2.trans_lt htr⟩, hbx⟩
  apply lt_of_le_of_ne hx.1
  intro he
  subst x
  exact hbl.ne' hbx

section FreeGroup
variable {ι : Type u}
variable (ρ : FreeGroup ι × Multiplicative ℤ →* (ℝ ≃o ℝ))

private theorem central_eq_zpow (m : Multiplicative ℤ) :
    (1, m) = cofinalProductZ (FreeGroup ι) ^ m.toAdd := by
  ext <;> simp [cofinalProductZ]

private theorem base_commute_central (g : FreeGroup ι) (m : Multiplicative ℤ) :
    Commute (ρ (g, 1)) (ρ (1, m)) := by
  apply Commute.map
  change (g, (1 : Multiplicative ℤ)) * (1, m) = (1, m) * (g, 1)
  simp

/-- Freeness permits replacing one marked generator by any map commuting with
the distinguished central element. -/
noncomputable def replaceFreeSection (i : ι) (a : ℝ ≃o ℝ) : FreeGroup ι →* (ℝ ≃o ℝ) := by
  classical
  exact FreeGroup.lift (fun j => if j = i then a else ρ (FreeGroup.of j, 1))

theorem replaceFreeSection_commute (i : ι) (a : ℝ ≃o ℝ)
    (ha : Commute a (ρ (cofinalProductZ (FreeGroup ι))))
    (g : FreeGroup ι) (m : Multiplicative ℤ) :
    Commute (replaceFreeSection ρ i a g) (ρ (1, m)) := by
  classical
  have ham : Commute a (ρ (1, m)) := by
    rw [central_eq_zpow m, map_zpow]
    exact ha.zpow_right m.toAdd
  induction g using FreeGroup.induction_on with
  | one => simpa only [map_one] using Commute.one_left (ρ (1, m))
  | of j =>
    by_cases hji : j = i
    · simpa only [replaceFreeSection, FreeGroup.lift_apply_of, hji, ↓reduceIte] using ham
    · simpa only [replaceFreeSection, FreeGroup.lift_apply_of, hji, ↓reduceIte]
        using base_commute_central ρ (FreeGroup.of j) m
  | inv_of j ih => simpa only [map_inv] using ih.inv_left
  | mul g h ihg ihh => simpa only [map_mul] using ihg.mul_left ihh

/-- The modified action remains an actual homomorphism of the full product,
including all commutation relations with the integer factor. -/
noncomputable def replaceGenerator (i : ι) (a : ℝ ≃o ℝ)
    (ha : Commute a (ρ (cofinalProductZ (FreeGroup ι)))) :
    FreeGroup ι × Multiplicative ℤ →* (ℝ ≃o ℝ) :=
  (replaceFreeSection ρ i a).noncommCoprod
    (ρ.comp (MonoidHom.inr (FreeGroup ι) (Multiplicative ℤ)))
    (replaceFreeSection_commute ρ i a ha)

@[simp] theorem replaceGenerator_central (i : ι) (a : ℝ ≃o ℝ)
    (ha : Commute a (ρ (cofinalProductZ (FreeGroup ι)))) (m : Multiplicative ℤ) :
    replaceGenerator ρ i a ha (1, m) = ρ (1, m) := by
  change replaceFreeSection ρ i a 1 * ρ (1, m) = _
  rw [map_one, one_mul]

@[simp] theorem replaceGenerator_chosen (i : ι) (a : ℝ ≃o ℝ)
    (ha : Commute a (ρ (cofinalProductZ (FreeGroup ι)))) :
    replaceGenerator ρ i a ha (FreeGroup.of i, 1) = a := by
  classical
  change replaceFreeSection ρ i a (FreeGroup.of i) * ρ (1, 1) = _
  simp [replaceFreeSection, ← Prod.one_eq_mk]

theorem replaceGenerator_other (i j : ι) (a : ℝ ≃o ℝ)
    (ha : Commute a (ρ (cofinalProductZ (FreeGroup ι)))) (hji : j ≠ i) :
    replaceGenerator ρ i a ha (FreeGroup.of j, 1) = ρ (FreeGroup.of j, 1) := by
  classical
  change replaceFreeSection ρ i a (FreeGroup.of j) * ρ (1, 1) = _
  simp [replaceFreeSection, hji, ← Prod.one_eq_mk]

/-- Multiplying a marked generator by a commuting truncated map preserves the
central relation, as in MMRT's local perturbation. -/
noncomputable def modifyGeneratorOnInterval (i : ι) (f : ℝ ≃o ℝ) (I : Set ℝ)
    (hI : Set.OrdConnected I) (hf : ∀ x : ℝ, x ∈ I ↔ f x ∈ I)
    (hzI : ∀ x : ℝ, x ∈ I ↔ ρ (cofinalProductZ (FreeGroup ι)) x ∈ I)
    (hcomm : Commute f (ρ (cofinalProductZ (FreeGroup ι)))) :
    FreeGroup ι × Multiplicative ℤ →* (ℝ ≃o ℝ) :=
  replaceGenerator ρ i (truncate f I hI hf * ρ (FreeGroup.of i, 1))
    (by
      exact (truncate_commute f _ I hI hf hzI hcomm).mul_left
        (base_commute_central ρ (FreeGroup.of i) (Multiplicative.ofAdd 1)))

/-- The modified generator agrees with the old action whenever its old image
avoids the support interval. -/
theorem modifyGeneratorOnInterval_agrees (i : ι) (f : ℝ ≃o ℝ) (I : Set ℝ)
    (hI : Set.OrdConnected I) (hf : ∀ x : ℝ, x ∈ I ↔ f x ∈ I)
    (hzI : ∀ x : ℝ, x ∈ I ↔ ρ (cofinalProductZ (FreeGroup ι)) x ∈ I)
    (hcomm : Commute f (ρ (cofinalProductZ (FreeGroup ι))))
    (x : ℝ) (hx : ρ (FreeGroup.of i, 1) x ∉ I) :
    modifyGeneratorOnInterval ρ i f I hI hf hzI hcomm (FreeGroup.of i, 1) x =
      ρ (FreeGroup.of i, 1) x := by
  rw [modifyGeneratorOnInterval, replaceGenerator_chosen]
  exact truncate_of_not_mem f I hI hf hx

/-- An actual product-group representation with the chosen generator acquiring
an interior fixed point, while the central action is preserved by construction. -/
theorem modifyGeneratorOnInterval_exists_fixed (i : ι) (f : ℝ ≃o ℝ) (l r : ℝ)
    (hl : f l = l) (hr : f r = r) (hfix : ∀ x ∈ Set.Ioo l r, f x ≠ x)
    (henter : ρ (FreeGroup.of i, 1) l ∈ Set.Ioo l r)
    (hzI : ∀ x : ℝ, x ∈ Set.Ioo l r ↔ ρ (cofinalProductZ (FreeGroup ι)) x ∈ Set.Ioo l r)
    (hcomm : Commute f (ρ (cofinalProductZ (FreeGroup ι)))) :
    ∃ k : ℤ, ∃ x ∈ Set.Ioo l r,
      modifyGeneratorOnInterval ρ i (f ^ k) (Set.Ioo l r) Set.ordConnected_Ioo
        (invariant_Ioo_zpow f l r hl hr k) hzI (hcomm.zpow_left k)
        (FreeGroup.of i, 1) x = x := by
  obtain ⟨k, x, hx, hfixed⟩ := exists_fixed_truncate_zpow_mul f (ρ (FreeGroup.of i, 1))
    l r hl hr hfix henter
  refine ⟨k, x, hx, ?_⟩
  rw [modifyGeneratorOnInterval, replaceGenerator_chosen]
  exact hfixed

end FreeGroup

end NoncofinalPerturbation
end FnZPositiveCones
