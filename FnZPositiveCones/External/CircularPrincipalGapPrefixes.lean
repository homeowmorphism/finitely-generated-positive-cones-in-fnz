module

public import FnZPositiveCones.External.CircularDynamicsGapWords

@[expose] public section

/-!
# Exact inverse-prefix enumeration of principal successor-gap labels

For a fixed reduced successor word `h`, the labels whose two endpoints have
different initial signed letters (including an identity endpoint) are exactly
the inverses of the `norm h + 1` prefixes. The statement covers the empty word
and does not assume that the alphabet is finite.
-/

namespace FnZPositiveCones.CircularDynamics

universe u
variable {ι : Type u} [DecidableEq ι]

/-- Algebraic endpoint condition for a principal successor gap. The separate
identity cases preserve the two gaps incident to the basepoint. -/
def PrincipalGapLabel (h g : FreeGroup ι) : Prop :=
  g = 1 ∨ g * h = 1 ∨ ∃ s t w z,
    g.toWord = s :: w ∧ (g * h).toWord = t :: z ∧ s ≠ t

/-- The endpoint condition is exactly absence of cancellation in the word for
`g⁻¹*(g*h)`. This is an equality of reduced free words, not a bounded check. -/
theorem principalGapLabel_iff_reduced (h g : FreeGroup ι) :
    PrincipalGapLabel h g ↔
      FreeGroup.IsReduced (FreeGroup.invRev g.toWord ++ (g * h).toWord) := by
  constructor
  · rintro (rfl | hg | ⟨s, t, w, z, hgs, hght, hst⟩)
    · simpa only [FreeGroup.toWord_one, FreeGroup.invRev_empty, List.nil_append, one_mul]
        using (FreeGroup.isReduced_toWord (x := h))
    · simpa only [hg, FreeGroup.toWord_one, List.append_nil, ← FreeGroup.toWord_inv]
        using (FreeGroup.isReduced_toWord (x := g⁻¹))
    · exact different_heads_inv_mul_reduced g (g * h) s t w z hgs hght hst
  · intro hr
    cases hg : g.toWord with
    | nil => exact Or.inl (FreeGroup.toWord_eq_nil_iff.mp hg)
    | cons s w =>
      cases hgh : (g * h).toWord with
      | nil => exact Or.inr (Or.inl (FreeGroup.toWord_eq_nil_iff.mp hgh))
      | cons t z =>
        refine Or.inr (Or.inr ⟨s, t, w, z, hg, hgh, ?_⟩)
        intro he
        subst t
        rw [hg, hgh, FreeGroup.invRev_cons] at hr
        have hr' : FreeGroup.IsReduced
            (FreeGroup.invRev w ++ (s.1, !s.2) :: s :: z) := by
          simpa only [FreeGroup.invRev, List.map_cons, List.map_nil,
            List.reverse_cons, List.reverse_nil, List.nil_append,
            List.append_assoc, List.singleton_append] using hr
        have hs := (List.isChain_append_cons_cons.mp hr').2.1
        have hb : (!s.2) = s.2 := hs rfl
        cases hs2 : s.2 <;> simp [hs2] at hb

/-- The label at a prefix position is the inverse of that exact prefix. -/
def inversePrefix (h : FreeGroup ι) (i : Fin (FreeGroup.norm h + 1)) : FreeGroup ι :=
  (FreeGroup.mk (h.toWord.take i.val))⁻¹

theorem prefix_reduced (h : FreeGroup ι) (n : ℕ) :
    FreeGroup.IsReduced (h.toWord.take n) := (FreeGroup.isReduced_toWord (x := h)).take n

theorem suffix_reduced (h : FreeGroup ι) (n : ℕ) :
    FreeGroup.IsReduced (h.toWord.drop n) := (FreeGroup.isReduced_toWord (x := h)).drop n

/-- Prefix and suffix multiply to the original group element in the exact order. -/
theorem prefix_mul_suffix (h : FreeGroup ι) (n : ℕ) :
    FreeGroup.mk (h.toWord.take n) * FreeGroup.mk (h.toWord.drop n) = h := by
  rw [FreeGroup.mul_mk, List.take_append_drop, FreeGroup.mk_toWord]

@[simp] theorem inversePrefix_mul_successor (h : FreeGroup ι)
    (i : Fin (FreeGroup.norm h + 1)) :
    inversePrefix h i * h = FreeGroup.mk (h.toWord.drop i.val) := by
  calc
    inversePrefix h i * h = (FreeGroup.mk (h.toWord.take i.val))⁻¹ *
        (FreeGroup.mk (h.toWord.take i.val) * FreeGroup.mk (h.toWord.drop i.val)) :=
      congrArg (fun g => (FreeGroup.mk (h.toWord.take i.val))⁻¹ * g)
        (prefix_mul_suffix h i.val).symm
    _ = _ := inv_mul_cancel_left _ _

/-- No prefix position repeats: its reduced word length is its index. -/
@[simp] theorem inversePrefix_norm (h : FreeGroup ι) (i : Fin (FreeGroup.norm h + 1)) :
    FreeGroup.norm (inversePrefix h i) = i.val := by
  have hi : i.val ≤ h.toWord.length := by change i.val ≤ FreeGroup.norm h; omega
  change FreeGroup.norm ((FreeGroup.mk (h.toWord.take i.val))⁻¹) = i.val
  rw [FreeGroup.norm_inv_eq]
  simp only [FreeGroup.norm, FreeGroup.toWord_mk,
    (prefix_reduced h i.val).reduce_eq, List.length_take, Nat.min_eq_left hi]

@[simp] theorem inversePrefix_zero (h : FreeGroup ι) :
    inversePrefix h ⟨0, Nat.zero_lt_succ _⟩ = 1 := by
  change (1 : FreeGroup ι)⁻¹ = 1
  exact inv_one

@[simp] theorem inversePrefix_last (h : FreeGroup ι) :
    inversePrefix h ⟨FreeGroup.norm h, Nat.lt_succ_self _⟩ = h⁻¹ := by
  simp only [inversePrefix, FreeGroup.norm, List.take_length, FreeGroup.mk_toWord]

/-- Consecutive principal labels differ by left multiplication by the inverse
of the next signed successor letter, matching the left-action convention. -/
theorem inversePrefix_successor (h : FreeGroup ι) (n : ℕ) (hn : n < FreeGroup.norm h) :
    inversePrefix h ⟨n + 1, by omega⟩ =
      (FreeGroup.mk [h.toWord[n]])⁻¹ * inversePrefix h ⟨n, by omega⟩ := by
  change (FreeGroup.mk (h.toWord.take (n + 1)))⁻¹ =
    (FreeGroup.mk [h.toWord[n]])⁻¹ * (FreeGroup.mk (h.toWord.take n))⁻¹
  rw [← List.take_concat_get' h.toWord n hn, ← FreeGroup.mul_mk, mul_inv_rev]

/-- Each inverse prefix satisfies the actual endpoint condition. -/
theorem inversePrefix_principal (h : FreeGroup ι) (i : Fin (FreeGroup.norm h + 1)) :
    PrincipalGapLabel h (inversePrefix h i) := by
  apply (principalGapLabel_iff_reduced h _).mpr
  rw [inversePrefix_mul_successor]
  simp only [inversePrefix, FreeGroup.toWord_inv, FreeGroup.toWord_mk,
    (prefix_reduced h i.val).reduce_eq, (suffix_reduced h i.val).reduce_eq,
    FreeGroup.invRev_invRev, List.take_append_drop]
  exact FreeGroup.isReduced_toWord

/-- The exact reduced-word decomposition of a principal label. -/
theorem principalGap_word_decomposition (h g : FreeGroup ι) (hg : PrincipalGapLabel h g) :
    h.toWord = FreeGroup.invRev g.toWord ++ (g * h).toWord := by
  have hr := (principalGapLabel_iff_reduced h g).mp hg
  calc
    h.toWord = (g⁻¹ * (g * h)).toWord := by rw [inv_mul_cancel_left]
    _ = FreeGroup.invRev g.toWord ++ (g * h).toWord := by
      rw [FreeGroup.toWord_mul, FreeGroup.toWord_inv, hr.reduce_eq]

/-- Lengths of both endpoints add to the successor length, including identity endpoints. -/
theorem principalGap_norm_add (h g : FreeGroup ι) (hg : PrincipalGapLabel h g) :
    FreeGroup.norm g + FreeGroup.norm (g * h) = FreeGroup.norm h := by
  have he := congrArg List.length (principalGap_word_decomposition h g hg)
  simpa only [FreeGroup.norm, List.length_append, FreeGroup.invRev_length] using he.symm

theorem principalGap_norm_le (h g : FreeGroup ι) (hg : PrincipalGapLabel h g) :
    FreeGroup.norm g ≤ FreeGroup.norm h := by
  have he := congrArg List.length (principalGap_word_decomposition h g hg)
  simp only [List.length_append, FreeGroup.invRev_length] at he
  change g.toWord.length ≤ h.toWord.length
  omega

/-- Every principal label is the inverse prefix at its own reduced length. -/
theorem principalGap_eq_inversePrefix (h g : FreeGroup ι) (hg : PrincipalGapLabel h g) :
    inversePrefix h ⟨FreeGroup.norm g, by have := principalGap_norm_le h g hg; omega⟩ = g := by
  have he := principalGap_word_decomposition h g hg
  have ht : h.toWord.take (FreeGroup.norm g) = FreeGroup.invRev g.toWord := by
    rw [he]
    change List.take g.toWord.length (FreeGroup.invRev g.toWord ++ (g * h).toWord) = _
    rw [← FreeGroup.invRev_length (L₁ := g.toWord), List.take_left]
  simp only [inversePrefix, ht, ← FreeGroup.inv_mk, FreeGroup.mk_toWord, inv_inv]

/-- Explicit bijection with all prefix positions, including both endpoint cases. -/
def principalGapPrefixEquiv (h : FreeGroup ι) :
    Fin (FreeGroup.norm h + 1) ≃ {g : FreeGroup ι // PrincipalGapLabel h g} where
  toFun i := ⟨inversePrefix h i, inversePrefix_principal h i⟩
  invFun g := ⟨FreeGroup.norm g.1, by have := principalGap_norm_le h g.1 g.2; omega⟩
  left_inv i := by apply Fin.ext; exact inversePrefix_norm h i
  right_inv g := by apply Subtype.ext; exact principalGap_eq_inversePrefix h g.1 g.2

/-- Actual principal labels form a finite set even for an infinite alphabet. -/
theorem finite_principalGapLabels (h : FreeGroup ι) : Set.Finite {g | PrincipalGapLabel h g} := by
  have : Finite {g : FreeGroup ι // PrincipalGapLabel h g} :=
    Finite.of_equiv (Fin (FreeGroup.norm h + 1)) (principalGapPrefixEquiv h)
  exact Set.finite_coe_iff.mp this

/-- Exact cardinality, not just a reduced-length upper bound. -/
theorem card_principalGapLabels (h : FreeGroup ι) :
    Nat.card {g : FreeGroup ι // PrincipalGapLabel h g} = FreeGroup.norm h + 1 := by
  rw [Nat.card_congr (principalGapPrefixEquiv h).symm, Nat.card_fin]

end FnZPositiveCones.CircularDynamics
