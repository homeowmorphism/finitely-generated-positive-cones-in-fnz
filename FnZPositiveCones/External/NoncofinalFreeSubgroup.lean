module

public import Mathlib.GroupTheory.FreeGroup.CyclicallyReduced
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.GroupTheory.Index

@[expose] public section

/-!
# Finite cores of normal free subgroups

The normal-subgroup obstruction used in MMRT Proposition 4.12 is proved by
tracking the quotient vertices visited by reduced words. No rank estimate or
abstract `IsFreeGroup` instance is used in place of the index assertion.
-/

namespace FnZPositiveCones
namespace NoncofinalFreeSubgroup

open FreeGroup
universe u v
variable {ι : Type u} {Q : Type v} [Group Q]

/-- Quotient vertices visited while reading a word, including both endpoints. -/
def vertices (φ : FreeGroup ι →* Q) : List (ι × Bool) → Set Q
  | [] => {1}
  | a :: w => {1} ∪ (fun q => φ (mk [a]) * q) '' vertices φ w

@[simp] theorem vertices_nil (φ : FreeGroup ι →* Q) : vertices φ [] = {1} := rfl
@[simp] theorem vertices_cons (φ : FreeGroup ι →* Q) (a : ι × Bool) (w) :
    vertices φ (a :: w) = {1} ∪ (fun q => φ (mk [a]) * q) '' vertices φ w := rfl

theorem one_mem_vertices (φ : FreeGroup ι →* Q) (w) : 1 ∈ vertices φ w := by
  cases w <;> simp

theorem endpoint_mem_vertices (φ : FreeGroup ι →* Q) (w) : φ (mk w) ∈ vertices φ w := by
  induction w with
  | nil => exact φ.map_one
  | cons a w ih =>
    right
    exact ⟨φ (mk w), ih, by dsimp only; rw [← _root_.map_mul, mul_mk]; rfl⟩

theorem vertices_finite (φ : FreeGroup ι →* Q) (w) : (vertices φ w).Finite := by
  induction w with
  | nil => exact Set.finite_singleton _
  | cons a w ih => exact (Set.finite_singleton _).union (ih.image _)

theorem vertices_append (φ : FreeGroup ι →* Q) (w t) :
    vertices φ (w ++ t) = vertices φ w ∪ (fun q => φ (mk w) * q) '' vertices φ t := by
  induction w with
  | nil => simp [show (mk [] : FreeGroup ι) = 1 from rfl, Set.singleton_union,
      Set.insert_eq_of_mem (one_mem_vertices φ t)]
  | cons a w ih =>
    rw [List.cons_append, vertices_cons, ih, Set.image_union, vertices_cons,
      ← Set.union_assoc]
    congr 1
    rw [Set.image_image]
    congr 1
    funext q
    rw [← mul_assoc, ← _root_.map_mul, mul_mk]
    rfl

theorem vertices_invRev (φ : FreeGroup ι →* Q) (w) :
    vertices φ (invRev w) = (fun q => (φ (mk w))⁻¹ * q) '' vertices φ w := by
  induction w with
  | nil => simp [show (mk [] : FreeGroup ι) = 1 from rfl]
  | cons a w ih =>
    rw [invRev_cons, vertices_append, ih, vertices_cons, Set.image_union,
      Set.image_image, Set.image_singleton]
    have he : φ (mk (a :: w)) = φ (mk [a]) * φ (mk w) := by
      rw [← _root_.map_mul, mul_mk]; rfl
    have hi : φ (mk (invRev w)) = (φ (mk w))⁻¹ := by rw [← inv_mk, _root_.map_inv]
    have hs : vertices φ (invRev [a]) = {1, (φ (mk [a]))⁻¹} := by
      have hmk : φ (mk [(a.1, !a.2)]) = (φ (mk [a]))⁻¹ := by
        rw [← _root_.map_inv, inv_mk]
        rfl
      simp only [invRev, List.map_cons, List.map_nil, List.reverse_cons,
        List.reverse_nil, List.nil_append, vertices_cons, vertices_nil,
        Set.image_singleton, mul_one, Set.singleton_union]
      rw [hmk, Set.pair_comm]
    rw [he, hi, hs]
    ext q
    simp only [Set.mem_union, Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff,
      mul_inv_rev, mul_one, mul_assoc]
    constructor
    · rintro (⟨r, hr, rfl⟩ | ⟨r, (rfl | rfl), rfl⟩)
      · exact Or.inr ⟨r, hr, by group⟩
      · exact Or.inr ⟨1, one_mem_vertices φ w, by group⟩
      · exact Or.inl (by group)
    · rintro (rfl | ⟨r, hr, rfl⟩)
      · exact Or.inr ⟨(φ (mk [a]))⁻¹, Or.inr rfl, by group⟩
      · exact Or.inl ⟨r, hr, by group⟩

theorem vertices_step_subset (φ : FreeGroup ι →* Q) {w t : List (ι × Bool)}
    (h : Red.Step w t) : vertices φ t ⊆ vertices φ w := by
  cases h with
  | @not l r a b =>
    rw [vertices_append, vertices_append]
    apply Set.union_subset_union_right
    intro q hq
    rcases hq with ⟨s, hs, rfl⟩
    refine ⟨s, ?_, rfl⟩
    have he : φ (mk [(a, b)]) * φ (mk [(a, !b)]) = 1 := by
      rw [← _root_.map_mul, mul_mk]
      have hmk : (mk [(a, b), (a, !b)] : FreeGroup ι) = 1 :=
        Quot.sound (Red.Step.cons_not (L := []))
      simpa using congrArg φ hmk
    right
    refine ⟨φ (mk [(a, !b)]) * s, ?_, ?_⟩
    · right; exact ⟨s, hs, rfl⟩
    · dsimp only; rw [← mul_assoc, he, one_mul]

theorem vertices_red_subset (φ : FreeGroup ι →* Q) {w t : List (ι × Bool)}
    (h : Red w t) : vertices φ t ⊆ vertices φ w := by
  induction h with
  | refl => exact Set.Subset.rfl
  | tail h st ih => exact (vertices_step_subset φ st).trans ih

theorem vertices_reduce_subset [DecidableEq ι] (φ : FreeGroup ι →* Q) (w) :
    vertices φ (reduce w) ⊆ vertices φ w := vertices_red_subset φ reduce.red

/-- All reduced loops contained in a chosen vertex set form a subgroup. -/
def coreSubgroup [DecidableEq ι] (φ : FreeGroup ι →* Q) (S : Set Q) (h1 : 1 ∈ S) :
    Subgroup (FreeGroup ι) where
  carrier := {g | φ g = 1 ∧ vertices φ g.toWord ⊆ S}
  one_mem' := by simpa using h1
  mul_mem' := by
    rintro g h ⟨hg, hgS⟩ ⟨hh, hhS⟩
    refine ⟨by simp [hg, hh], ?_⟩
    rw [toWord_mul]
    apply (vertices_reduce_subset φ _).trans
    rw [vertices_append, mk_toWord, hg]
    simpa using Set.union_subset hgS hhS
  inv_mem' := by
    rintro g ⟨hg, hgS⟩
    refine ⟨by simp [hg], ?_⟩
    rw [toWord_inv, vertices_invRev, mk_toWord, hg]
    simpa using hgS

/-- A finitely generated kernel has a finite reduced-word core. -/
theorem exists_finite_core [DecidableEq ι] (φ : FreeGroup ι →* Q)
    (hfg : φ.ker.FG) :
    ∃ S : Set Q, S.Finite ∧ ∀ g ∈ φ.ker, vertices φ g.toWord ⊆ S := by
  obtain ⟨T, hT⟩ := Subgroup.isMulFG_iff.mp hfg
  let S : Set Q := {1} ∪ ⋃ g ∈ (T : Set (FreeGroup ι)), vertices φ g.toWord
  have hfin : S.Finite := (Set.finite_singleton 1).union
    (T.finite_toSet.biUnion (fun g _ => vertices_finite φ g.toWord))
  have hle : φ.ker ≤ coreSubgroup φ S (Or.inl rfl) := by
    rw [← hT]
    apply (Subgroup.closure_le _).mpr
    intro g hg
    refine ⟨?_, ?_⟩
    · have hg' : g ∈ φ.ker := by
        rw [← hT]
        exact Subgroup.mem_closure_of_mem hg
      exact hg'
    · intro q hq
      exact Or.inr (Set.mem_iUnion.mpr ⟨g, Set.mem_iUnion.mpr ⟨hg, hq⟩⟩)
  exact ⟨S, hfin, fun g hg => (hle hg).2⟩

/-- Four signed letters suffice to avoid any three forbidden boundary letters. -/
theorem exists_signed_letter_avoiding_three [Nontrivial ι] (a b c : ι × Bool) :
    ∃ s : ι × Bool, s ≠ a ∧ s ≠ b ∧ s ≠ c := by
  classical
  obtain ⟨i, j, hij⟩ := exists_pair_ne ι
  let S : Finset (ι × Bool) := {(i, true), (i, false), (j, true), (j, false)}
  let T : Finset (ι × Bool) := {a, b, c}
  have hS : S.card = 4 := by simp [S, hij]
  have hT : T.card ≤ 3 := by
    exact (Finset.card_insert_le _ _).trans (Nat.succ_le_succ
      ((Finset.card_insert_le _ _).trans (by simp)))
  by_contra h
  push Not at h
  have hsub : S ⊆ T := by
    intro s _
    by_cases ha : s = a
    · simp [T, ha]
    by_cases hb : s = b
    · simp [T, hb]
    simp [T, h s ha hb]
  have := Finset.card_le_card hsub
  omega

/-- Reducedness of an inverse word, derived from the checked reduction algorithm. -/
theorem isReduced_invRev [DecidableEq ι] {w : List (ι × Bool)} (hw : IsReduced w) :
    IsReduced (invRev w) := by
  rw [isReduced_iff_reduce_eq, reduce_invRev, hw.reduce_eq]

/-- A bridge letter embeds any reduced word as the initial part of a reduced
conjugate of any nonempty reduced word. -/
theorem exists_reduced_conjugate_prefix [Nontrivial ι] [DecidableEq ι]
    (w t : List (ι × Bool)) (hw : IsReduced w) (ht : IsReduced t) (hne : t ≠ []) :
    ∃ s : ι × Bool, IsReduced (w ++ [s] ++ t ++ invRev [s] ++ invRev w) := by
  classical
  let a : ι × Bool := (w.getLast?).getD (t.head hne)
  let b := t.head hne
  let c := t.getLast hne
  obtain ⟨s, hsa, hsb, hsc⟩ := exists_signed_letter_avoiding_three
    (a.1, !a.2) (b.1, !b.2) c
  have hws : IsReduced (w ++ [s]) := by
    apply List.IsChain.append hw IsReduced.singleton
    intro x hx y hy hxy
    have hy' : y = s := by simpa [eq_comm] using hy
    subst y
    have hx' : x = a := by
      dsimp [a]
      rw [Option.mem_def] at hx
      rw [hx]
      rfl
    subst x
    by_contra hbool
    apply hsa
    apply Prod.ext
    · exact hxy.symm
    · exact Bool.eq_not.mpr (Ne.symm hbool)
  have hst : IsReduced ([s] ++ t) := by
    apply List.IsChain.append IsReduced.singleton ht
    intro x hx y hy hxy
    have hx' : x = s := by simpa [eq_comm] using hx
    have hy' : y = b := by simpa [b, List.head?_eq_some_head hne, eq_comm] using hy
    subst x
    subst y
    by_contra hbool
    apply hsb
    apply Prod.ext
    · exact hxy
    · exact Bool.eq_not.mpr hbool
  have hts : IsReduced (t ++ invRev [s]) := by
    apply List.IsChain.append ht (isReduced_invRev IsReduced.singleton)
    intro x hx y hy hxy
    have hx' : x = c := by simpa [c, List.getLast?_eq_some_getLast hne, eq_comm] using hx
    have hy' : y = (s.1, !s.2) := by simpa [invRev, eq_comm] using hy
    subst x
    subst y
    by_contra hbool
    apply hsc
    apply Prod.ext
    · exact hxy.symm
    · exact (Bool.ne_not.mp hbool).symm
  have hwt : IsReduced (w ++ [s] ++ t) := hws.append_overlap hst (by simp)
  have hlong : IsReduced (w ++ [s] ++ t ++ invRev [s]) :=
    hwt.append_overlap hts hne
  have hlast : IsReduced (invRev [s] ++ invRev w) := by
    simpa only [invRev_append] using isReduced_invRev hws
  exact ⟨s, hlong.append_overlap hlast (by simp [invRev])⟩

/-- Every quotient vertex is visited by a reduced kernel word, provided the
kernel is nontrivial and there are at least two free generators. -/
theorem mem_core_of_surjective [Nontrivial ι] [DecidableEq ι]
    (φ : FreeGroup ι →* Q) (hsurj : Function.Surjective φ) (hne : φ.ker ≠ ⊥)
    (q : Q) : ∃ g ∈ φ.ker, q ∈ vertices φ g.toWord := by
  obtain ⟨g, rfl⟩ := hsurj q
  obtain ⟨⟨h, hh⟩, hhne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hhne' : h ≠ 1 := fun he => hhne (Subtype.ext he)
  obtain ⟨s, hs⟩ := exists_reduced_conjugate_prefix g.toWord h.toWord
    isReduced_toWord isReduced_toWord (toWord_eq_nil_iff.not.mpr hhne')
  let w := g.toWord ++ [s] ++ h.toWord ++ invRev [s] ++ invRev g.toWord
  have hw : φ (mk w) = 1 := by
    dsimp [w]
    simp only [← mul_mk, ← inv_mk, mk_toWord, _root_.map_mul, _root_.map_inv]
    rw [show φ h = 1 from hh]
    group
  refine ⟨mk w, hw, ?_⟩
  rw [toWord_mk, hs.reduce_eq]
  change φ g ∈ vertices φ w
  have hprefix : vertices φ g.toWord ⊆ vertices φ w := by
    dsimp [w]
    rw [List.append_assoc, List.append_assoc, List.append_assoc, vertices_append]
    exact Set.subset_union_left
  exact hprefix (by simpa only [mk_toWord] using endpoint_mem_vertices φ g.toWord)

/-- A surjective homomorphism from a free group on at least two generators with
a nontrivial finitely generated kernel has finite codomain. -/
theorem finite_of_nontrivial_fg_kernel [Nontrivial ι] (φ : FreeGroup ι →* Q)
    (hsurj : Function.Surjective φ) (hfg : φ.ker.FG) (hne : φ.ker ≠ ⊥) : Finite Q := by
  classical
  obtain ⟨S, hS, hcore⟩ := exists_finite_core φ hfg
  have heq : S = Set.univ := by
    apply Set.eq_univ_of_forall
    intro q
    obtain ⟨g, hg, hq⟩ := mem_core_of_surjective φ hsurj hne q
    exact hcore g hg hq
  exact Set.finite_univ_iff.mp (heq ▸ hS)

/-- The normal-subgroup obstruction needed in MMRT Proposition 4.12: a
nontrivial finitely generated normal subgroup of a nonabelian free group has
finite index. The result also applies to an infinite ambient free rank. -/
theorem index_ne_zero_of_fg_normal [Nontrivial ι]
    (K : Subgroup (FreeGroup ι)) [K.Normal] (hfg : K.FG) (hne : K ≠ ⊥) :
    K.index ≠ 0 := by
  let φ := QuotientGroup.mk' K
  have hker : φ.ker = K := QuotientGroup.ker_mk' K
  have : Finite (FreeGroup ι ⧸ K) := finite_of_nontrivial_fg_kernel φ
    (QuotientGroup.mk'_surjective K) (by simpa only [hker] using hfg) (by simpa only [hker] using hne)
  exact K.index_ne_zero_of_finite

/-- Contrapositive form used for an infinite-index convex stabilizer. -/
theorem not_normal_of_fg_nontrivial_index_zero [Nontrivial ι]
    (K : Subgroup (FreeGroup ι)) (hfg : K.FG) (hne : K ≠ ⊥) (hi : K.index = 0) :
    ¬ K.Normal := by
  intro hnormal
  exact index_ne_zero_of_fg_normal K hfg hne hi

/-- The exact finite-rank instance, including rank two. -/
theorem finite_rank_index_ne_zero {n : ℕ} (hn : 2 ≤ n)
    (K : Subgroup (FreeGroup (Fin n))) [K.Normal] (hfg : K.FG) (hne : K ≠ ⊥) :
    K.index ≠ 0 := by
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  exact index_ne_zero_of_fg_normal K hfg hne

end NoncofinalFreeSubgroup
end FnZPositiveCones
