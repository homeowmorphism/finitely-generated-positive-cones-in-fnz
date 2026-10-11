module

public import FnZPositiveCones.Construction
public import FnZPositiveCones.Classification

@[expose] public section

/-! The two main results of Su's paper.

The supporting existence proof is in `Construction.lean`; the converse and
classification helpers are in `Classification.lean`.
-/

namespace FnZPositiveCones

/-- Su, Theorem 1.1: every even rank at least two has a finitely generated strict positive cone. -/
theorem evenRank_hasFGPositiveCone :
    ∀ n : ℕ, 2 ≤ n → Even n →
      HasFGPositiveCone (FreeGroup (Fin n) × Multiplicative ℤ) :=
  conditionalEvenRank baseCone

/-- Su, Corollary 1.2: the exact unconditional parity classification of
finitely generated strict positive cones on the marked product groups. -/
theorem hasFGPositiveCone_iff_even :
    ∀ n : ℕ, 2 ≤ n →
      (HasFGPositiveCone (FreeGroup (Fin n) × Multiplicative ℤ) ↔ Even n) := by
  intro n hn
  exact ⟨even_of_hasFGPositiveCone n hn, evenRank_hasFGPositiveCone n hn⟩

end FnZPositiveCones
