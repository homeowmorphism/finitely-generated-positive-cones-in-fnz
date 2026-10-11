module

public import FnZPositiveCones.Cone.Topology

@[expose] public section

/-!
# Infinite free rank has no isolated orders

This is the algebraic form of MMRT Lemma 4.13. A finite set of group elements
uses only finitely many free generators. Inverting a generator outside that
set changes any positive cone while preserving the prescribed finite signs.
-/
namespace FnZPositiveCones

universe u v

/-- Local automorphisms reversing some nontrivial element obstruct finite determination. -/
theorem not_finitelyDetermined_of_local_reversals {G : Type u} [Group G]
    (hrev : ∀ S : Finset G, ∃ e : G ≃* G, ∃ g : G,
      g ≠ 1 ∧ e g = g⁻¹ ∧ ∀ s ∈ S, e s = s)
    (P : Subsemigroup G) (hP : IsPositiveCone P) : ¬ FinitelyDetermined P := by
  rintro ⟨S, hSP, hS⟩
  obtain ⟨e, g, hg, heg, hfix⟩ := hrev S
  let Q := Subsemigroup.map e.toMonoidHom.toMulHom P
  have hQ : IsPositiveCone Q := positiveCone_transport e hP
  have heq : Q = P := hS Q hQ (by
    intro s hs
    exact ⟨s, hSP hs, hfix s hs⟩)
  have hmem : ∀ x ∈ P, e x ∈ P := by
    intro x hx
    rw [← heq]
    exact ⟨x, hx, rfl⟩
  rcases (hP.2 g).resolve_left hg with hp | hn
  · exact positiveCone_inv_not_mem hP hp (heg ▸ hmem g hp)
  · have hp : g ∈ P := by simpa [map_inv, heg] using hmem g⁻¹ hn
    exact positiveCone_inv_not_mem hP hp hn

namespace InfiniteFreeRank

variable {ι : Type u}
noncomputable section

local instance : DecidableEq ι := Classical.decEq ι

/-- Invert exactly one free generator. -/
def invertGeneratorHom (i : ι) : FreeGroup ι →* FreeGroup ι := by
  classical
  exact FreeGroup.lift fun j => if j = i then (FreeGroup.of j)⁻¹ else FreeGroup.of j

@[simp] theorem invertGeneratorHom_of (i j : ι) :
    invertGeneratorHom i (FreeGroup.of j) =
      if j = i then (FreeGroup.of j)⁻¹ else FreeGroup.of j := by
  classical
  simp [invertGeneratorHom]

 theorem invertGeneratorHom_squared (i : ι) :
    (invertGeneratorHom i).comp (invertGeneratorHom i) = MonoidHom.id _ := by
  classical
  apply FreeGroup.ext_hom
  intro j
  by_cases hj : j = i <;> simp [hj]

 theorem invertGeneratorHom_involutive (i : ι) :
    Function.Involutive (invertGeneratorHom i) :=
  fun w => DFunLike.congr_fun (invertGeneratorHom_squared i) w

/-- The inverse map is the same generator inversion, with both laws checked. -/
def invertGenerator (i : ι) : FreeGroup ι ≃* FreeGroup ι where
  toFun := invertGeneratorHom i
  invFun := invertGeneratorHom i
  left_inv := invertGeneratorHom_involutive i
  right_inv := invertGeneratorHom_involutive i
  map_mul' := map_mul _

@[simp] theorem invertGenerator_of (i j : ι) :
    invertGenerator i (FreeGroup.of j) =
      if j = i then (FreeGroup.of j)⁻¹ else FreeGroup.of j := invertGeneratorHom_of i j

/-- Each free word is fixed by inversion of all but finitely many generators. -/
theorem word_finite_support (w : FreeGroup ι) :
    ∃ T : Finset ι, ∀ i ∉ T, invertGenerator i w = w := by
  classical
  induction w using FreeGroup.induction_on with
  | one => exact ⟨∅, by simp⟩
  | of j => exact ⟨{j}, by intro i hi; simp_all [eq_comm]⟩
  | inv_of j ih =>
    obtain ⟨T, hT⟩ := ih
    exact ⟨T, by intro i hi; rw [map_inv, hT i hi]⟩
  | mul x y ihx ihy =>
    obtain ⟨T, hT⟩ := ihx
    obtain ⟨U, hU⟩ := ihy
    refine ⟨T ∪ U, ?_⟩
    intro i hi
    have hT' : i ∉ T := fun h => hi (Finset.mem_union_left U h)
    have hU' : i ∉ U := fun h => hi (Finset.mem_union_right T h)
    rw [map_mul, hT i hT', hU i hU']

variable {H : Type v} [Group H]

/-- A finite family of product elements has one common finite support. -/
theorem family_finite_support (S : Finset (FreeGroup ι × H)) :
    ∃ T : Finset ι, ∀ i ∉ T, ∀ s ∈ S,
      ((invertGenerator i).prodCongr (MulEquiv.refl H)) s = s := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨∅, by simp⟩
  | @insert s S hs ih =>
    obtain ⟨T, hT⟩ := word_finite_support s.1
    obtain ⟨U, hU⟩ := ih
    refine ⟨T ∪ U, ?_⟩
    intro i hi t ht
    have hiT : i ∉ T := fun h => hi (Finset.mem_union_left U h)
    have hiU : i ∉ U := fun h => hi (Finset.mem_union_right T h)
    rcases Finset.mem_insert.mp ht with rfl | ht
    · exact Prod.ext (hT i hiT) rfl
    · exact hU i hiU t ht

/-- No strict positive cone on an infinite-rank free group product is finitely determined. -/
theorem not_finitelyDetermined [Infinite ι] (P : Subsemigroup (FreeGroup ι × H))
    (hP : IsPositiveCone P) : ¬ FinitelyDetermined P := by
  apply not_finitelyDetermined_of_local_reversals _ P hP
  intro S
  obtain ⟨T, hT⟩ := family_finite_support S
  obtain ⟨i, hi⟩ := Infinite.exists_notMem_finset T
  refine ⟨(invertGenerator i).prodCongr (MulEquiv.refl H), (FreeGroup.of i, 1), ?_, ?_, hT i hi⟩
  · intro he
    exact FreeGroup.of_ne_one i (congrArg Prod.fst he)
  · apply Prod.ext
    · change invertGenerator i (FreeGroup.of i) = (FreeGroup.of i)⁻¹
      simp
    · change (1 : H) = 1⁻¹
      simp

/-- MMRT Lemma 4.13 in the checked topology of finite inequalities. -/
theorem no_isolated_left_order [Infinite ι] (O : LeftGroupOrder (FreeGroup ι × H)) :
    ¬ IsOpen ({O} : Set (LeftGroupOrder (FreeGroup ι × H))) := by
  intro h
  have hfd : FinitelyDetermined (leftOrderCone O).1 :=
    (finiteDetermination_iff_leftOrder_isolated (leftOrderCone O)).mpr (by simpa using h)
  exact not_finitelyDetermined _ (leftOrderCone O).2 hfd

end
end InfiniteFreeRank
end FnZPositiveCones
