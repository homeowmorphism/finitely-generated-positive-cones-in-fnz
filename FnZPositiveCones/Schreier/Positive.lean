module

public import FnZPositiveCones.Interfaces

@[expose] public section

/-!
# Positive Schreier rewriting

Right cosets have the form `K * g`.  The only identity used in the generation
argument is temporary: the final closure is a subsemigroup closure and its
generators exclude the identity.
-/

namespace FnZPositiveCones

universe u
variable {G : Type u} [Group G] {K : Subgroup G} {T : Set G}

/-- The representative of the right coset `K * g`. -/
noncomputable def rightRep (hT : Subgroup.IsComplement (K : Set G) T) (g : G) : G :=
  hT.toRightFun g

theorem rightRep_mem (hT : Subgroup.IsComplement (K : Set G) T) (g : G) :
    rightRep hT g ∈ T :=
  (hT.toRightFun g).property

theorem mul_rightRep_inv_mem (hT : Subgroup.IsComplement (K : Set G) T) (g : G) :
    g * (rightRep hT g)⁻¹ ∈ K :=
  hT.mul_inv_toRightFun_mem g

theorem rightRep_eq_of_mem (hT : Subgroup.IsComplement (K : Set G) T)
    {g t : G} (ht : t ∈ T) (hgt : g * t⁻¹ ∈ K) : rightRep hT g = t := by
  have hu := (Subgroup.isComplement_iff_existsUnique_mul_inv_mem.mp hT) g
  have he : hT.toRightFun g = (⟨t, ht⟩ : T) :=
    hu.unique (mul_rightRep_inv_mem hT g) hgt
  exact congrArg Subtype.val he

@[simp] theorem rightRep_of_mem (hT : Subgroup.IsComplement (K : Set G) T)
    {t : G} (ht : t ∈ T) : rightRep hT t = t :=
  rightRep_eq_of_mem hT ht (by simp)

@[simp] theorem rightRep_one (hT : Subgroup.IsComplement (K : Set G) T)
    (hT1 : (1 : G) ∈ T) : rightRep hT 1 = 1 :=
  rightRep_of_mem hT hT1

theorem rightRep_of_mem_subgroup (hT : Subgroup.IsComplement (K : Set G) T)
    (hT1 : (1 : G) ∈ T) {g : G} (hg : g ∈ K) : rightRep hT g = 1 :=
  rightRep_eq_of_mem hT hT1 (by simpa using hg)

theorem rightRep_eq_iff (hT : Subgroup.IsComplement (K : Set G) T) (g h : G) :
    rightRep hT g = rightRep hT h ↔ g * h⁻¹ ∈ K := by
  constructor
  · intro he
    have hm := K.mul_mem (mul_rightRep_inv_mem hT g)
      (K.inv_mem (mul_rightRep_inv_mem hT h))
    simpa [he, mul_assoc] using hm
  · intro hgh
    apply rightRep_eq_of_mem hT (rightRep_mem hT h)
    have hm := K.mul_mem hgh (mul_rightRep_inv_mem hT h)
    simpa [mul_assoc] using hm

theorem rightRep_mul (hT : Subgroup.IsComplement (K : Set G) T) (g h : G) :
    rightRep hT (rightRep hT g * h) = rightRep hT (g * h) := by
  apply (rightRep_eq_iff hT _ _).2
  have hm := K.inv_mem (mul_rightRep_inv_mem hT g)
  simpa [mul_assoc] using hm

/-- The subgroup-valued Schreier factor. -/
noncomputable def schreierDelta (hT : Subgroup.IsComplement (K : Set G) T)
    (t p : G) : K :=
  ⟨t * p * (rightRep hT (t * p))⁻¹, mul_rightRep_inv_mem hT (t * p)⟩

theorem schreierDelta_mul (hT : Subgroup.IsComplement (K : Set G) T) (t p q : G) :
    schreierDelta hT t (p * q) =
      schreierDelta hT t p * schreierDelta hT (rightRep hT (t * p)) q := by
  apply Subtype.ext
  simp only [schreierDelta, Subgroup.coe_mul]
  rw [rightRep_mul]
  simp [mul_assoc]

@[simp] theorem schreierDelta_one_subgroup
    (hT : Subgroup.IsComplement (K : Set G) T) (hT1 : (1 : G) ∈ T) (p : K) :
    schreierDelta hT 1 (p : G) = p := by
  apply Subtype.ext
  simp [schreierDelta, rightRep_of_mem_subgroup hT hT1 p.property]

/-- Nonidentity factors, as elements of the subgroup rather than the ambient group. -/
def positiveSchreierSet (hT : Subgroup.IsComplement (K : Set G) T) (S : Set G) : Set K :=
  {k | ∃ t ∈ T, ∃ s ∈ S, schreierDelta hT t s = k ∧ k ≠ 1}

/-- Closure induction permits temporary identity factors without adding the identity
to the final semigroup closure. -/
theorem schreierDelta_eq_one_or_mem_closure
    (hT : Subgroup.IsComplement (K : Set G) T) {S : Set G} {p : G}
    (hp : p ∈ Subsemigroup.closure S) :
    ∀ t ∈ T, schreierDelta hT t p = 1 ∨
      schreierDelta hT t p ∈ Subsemigroup.closure (positiveSchreierSet hT S) := by
  classical
  induction hp using Subsemigroup.closure_induction with
  | mem s hs =>
      intro t ht
      by_cases he : schreierDelta hT t s = 1
      · exact Or.inl he
      · exact Or.inr (Subsemigroup.subset_closure ⟨t, ht, s, hs, rfl, he⟩)
  | mul p q hp hq ihp ihq =>
      intro t ht
      rw [schreierDelta_mul]
      rcases ihp t ht with he | he <;>
        rcases ihq (rightRep hT (t * p)) (rightRep_mem hT _) with hf | hf
      · exact Or.inl (by rw [he, hf, one_mul])
      · exact Or.inr (by simpa [he] using hf)
      · exact Or.inr (by simpa [hf] using he)
      · exact Or.inr (Subsemigroup.mul_mem _ he hf)

/-- Positive Schreier rewriting gives equality of **semigroup** closures.
The identity alternative in the induction is ruled out by strict positivity. -/
theorem positiveSchreier_closure_eq
    (hT : Subgroup.IsComplement (K : Set G) T) (hT1 : (1 : G) ∈ T)
    {P : Subsemigroup G} (hP : IsPositiveCone P) {S : Set G}
    (hS : P = Subsemigroup.closure S)
    (hpos : ∀ t ∈ T, ∀ s ∈ S,
      schreierDelta hT t s = 1 ∨ (schreierDelta hT t s : G) ∈ P) :
    Subsemigroup.comap K.subtype.toMulHom P =
      Subsemigroup.closure (positiveSchreierSet hT S) := by
  apply le_antisymm
  · intro p hp
    have hpP : (p : G) ∈ P := hp
    have hpS : (p : G) ∈ Subsemigroup.closure S := hS ▸ hpP
    have hdelta := schreierDelta_eq_one_or_mem_closure hT hpS 1 hT1
    rw [schreierDelta_one_subgroup hT hT1] at hdelta
    rcases hdelta with he | he
    · exact False.elim (hP.1 (by simpa [he] using hpP))
    · exact he
  · apply Subsemigroup.closure_le.mpr
    rintro k ⟨t, ht, s, hs, rfl, hne⟩
    rcases hpos t ht s hs with he | he
    · exact False.elim (hne he)
    · exact he

theorem positiveSchreierSet_finite
    (hT : Subgroup.IsComplement (K : Set G) T) {S : Set G}
    (hTf : T.Finite) (hSf : S.Finite) : (positiveSchreierSet hT S).Finite := by
  apply ((hTf.prod hSf).image fun p : G × G => schreierDelta hT p.1 p.2).subset
  rintro k ⟨t, ht, s, hs, rfl, _⟩
  exact ⟨(t, s), ⟨ht, hs⟩, rfl⟩

theorem positiveSchreierSet_ncard_le
    (hT : Subgroup.IsComplement (K : Set G) T) {S : Set G}
    (hTf : T.Finite) (hSf : S.Finite) :
    (positiveSchreierSet hT S).ncard ≤ T.ncard * S.ncard := by
  let f : G × G → K := fun p => schreierDelta hT p.1 p.2
  have hsub : positiveSchreierSet hT S ⊆ f '' (T ×ˢ S) := by
    rintro k ⟨t, ht, s, hs, rfl, _⟩
    exact ⟨(t, s), ⟨ht, hs⟩, rfl⟩
  calc
    (positiveSchreierSet hT S).ncard ≤ (f '' (T ×ˢ S)).ncard :=
      Set.ncard_le_ncard hsub ((hTf.prod hSf).image f)
    _ ≤ (T ×ˢ S).ncard := Set.ncard_image_le (hTf.prod hSf)
    _ = T.ncard * S.ncard := Set.ncard_prod

/-- A finite transversal and finite positive generating set give semigroup
finite generation of the restricted cone. -/
theorem positiveSchreier_finiteGeneration
    (hT : Subgroup.IsComplement (K : Set G) T) (hT1 : (1 : G) ∈ T)
    {P : Subsemigroup G} (hP : IsPositiveCone P) {S : Set G}
    (hS : P = Subsemigroup.closure S)
    (hpos : ∀ t ∈ T, ∀ s ∈ S,
      schreierDelta hT t s = 1 ∨ (schreierDelta hT t s : G) ∈ P)
    (hTf : T.Finite) (hSf : S.Finite) :
    SemigroupFG (Subsemigroup.comap K.subtype.toMulHom P) := by
  classical
  let hA := positiveSchreierSet_finite hT hTf hSf
  refine ⟨hA.toFinset, ?_⟩
  rw [hA.coe_toFinset]
  exact (positiveSchreier_closure_eq hT hT1 hP hS hpos).symm

/-- A quantitative form of finite positive Schreier generation. -/
theorem positiveSchreier_finiteGeneration_bound
    (hT : Subgroup.IsComplement (K : Set G) T) (hT1 : (1 : G) ∈ T)
    {P : Subsemigroup G} (hP : IsPositiveCone P) {S : Set G}
    (hS : P = Subsemigroup.closure S)
    (hpos : ∀ t ∈ T, ∀ s ∈ S,
      schreierDelta hT t s = 1 ∨ (schreierDelta hT t s : G) ∈ P)
    (hTf : T.Finite) (hSf : S.Finite) :
    ∃ A : Finset K, A.card ≤ T.ncard * S.ncard ∧
      Subsemigroup.closure (A : Set K) = Subsemigroup.comap K.subtype.toMulHom P := by
  classical
  let hA := positiveSchreierSet_finite hT hTf hSf
  refine ⟨hA.toFinset, ?_, ?_⟩
  · rw [← Set.ncard_eq_toFinset_card _ hA]
    exact positiveSchreierSet_ncard_le hT hTf hSf
  · rw [hA.coe_toFinset]
    exact (positiveSchreier_closure_eq hT hT1 hP hS hpos).symm

end FnZPositiveCones
