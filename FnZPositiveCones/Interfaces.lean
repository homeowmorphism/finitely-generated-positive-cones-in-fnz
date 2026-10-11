module

public import Mathlib

@[expose] public section

/-!
# Target propositions for arXiv:2608.31103v1

This file states specifications only; the proofs live elsewhere in the library.
Each goal's docstring names the theorem that proves it.
It contains no `sorry`, no `axiom`, and no claimed external theorem.
The file elaborates at the pinned mathlib/toolchain (checked 2026-10-11).
-/

namespace FnZPositiveCones

universe u

/-- A strict positive cone for a left order; no commutativity assumption. -/
def IsPositiveCone {G : Type u} [Group G] (P : Subsemigroup G) : Prop :=
  (1 : G) ∉ P ∧ ∀ g : G, g = 1 ∨ g ∈ P ∨ g⁻¹ ∈ P

/-- Finite generation as a semigroup, not as a subgroup or a monoid. -/
def SemigroupFG {G : Type u} [Group G] (P : Subsemigroup G) : Prop :=
  ∃ S : Finset G, Subsemigroup.closure (S : Set G) = P

/-- The main existence property. -/
def HasFGPositiveCone (G : Type u) [Group G] : Prop :=
  ∃ S : Finset G, IsPositiveCone (Subsemigroup.closure (S : Set G))

/-- A quantitative refinement, with an upper bound rather than a minimality claim. -/
def HasFGPositiveConeWithBound (G : Type u) [Group G] (m : ℕ) : Prop :=
  ∃ S : Finset G, S.card ≤ m ∧
    IsPositiveCone (Subsemigroup.closure (S : Set G))

/-- A topology-free interface to finite determination of a cone.
Use it only together with `IsPositiveCone P`. For a positive cone, it is equivalent to
isolation in the space of left orders (`finiteDetermination_iff_isolated`).
Without that hypothesis it can hold vacuously: `⊤` satisfies it with `S = {1}`. -/
def FinitelyDetermined {G : Type u} [Group G] (P : Subsemigroup G) : Prop :=
  ∃ S : Finset G, (S : Set G) ⊆ (P : Set G) ∧
    ∀ Q : Subsemigroup G, IsPositiveCone Q →
      (S : Set G) ⊆ (Q : Set G) → Q = P

/-- The infinite cyclic factor is multiplicative in a direct product of groups. -/
abbrev FnZ (n : ℕ) := FreeGroup (Fin n) × Multiplicative ℤ

/-- The two generators `a` and `b` of `Gamma2`. -/
inductive GammaLetter
  | a
  | b
  deriving DecidableEq

/-- The relation b a² b = a encoded as a relator equal to one. -/
def gammaRelator : FreeGroup GammaLetter :=
  FreeGroup.of GammaLetter.b * FreeGroup.of GammaLetter.a ^ (2 : ℕ) *
    FreeGroup.of GammaLetter.b * (FreeGroup.of GammaLetter.a)⁻¹

/-- The single defining relator of `Gamma2`. -/
def gammaRelations : Set (FreeGroup GammaLetter) := {gammaRelator}

/-- The group Γ₂ = ⟨a, b | b a² b = a⟩. It is isomorphic to the braid group B₃
via a ↦ σ₁σ₂ and b ↦ σ₂⁻¹. -/
abbrev Gamma2 := PresentedGroup gammaRelations

/-- The generator `a` of `Gamma2`. -/
def aGamma : Gamma2 := PresentedGroup.of GammaLetter.a

/-- The generator `b` of `Gamma2`. -/
def bGamma : Gamma2 := PresentedGroup.of GammaLetter.b

/-- The semigroup P₂ = ⟨a, b⟩⁺ of `Gamma2`: all nonempty products of a and b. -/
def basePositiveClosure : Subsemigroup Gamma2 :=
  Subsemigroup.closure ({aGamma, bGamma} : Set Gamma2)

/-- The identity condition of the Dubrovina–Dubrovin/Navas theorem: 1 ∉ ⟨a, b⟩⁺.
Proved as `baseOneNotMem`. -/
def BaseOneNotMemGoal : Prop :=
  (1 : Gamma2) ∉ basePositiveClosure

/-- The totality condition of the Dubrovina–Dubrovin/Navas theorem: every element
other than 1 lies in ⟨a, b⟩⁺ or has its inverse there. Proved as `baseTotal`. -/
def BaseTotalGoal : Prop :=
  ∀ g : Gamma2, g = 1 ∨ g ∈ basePositiveClosure ∨ g⁻¹ ∈ basePositiveClosure

/-- The paper's Theorem 3.1 (Dubrovina–Dubrovin; Navas): ⟨a, b⟩⁺ is a positive cone
of `Gamma2`. By definition it is `BaseOneNotMemGoal ∧ BaseTotalGoal`.
Proved as `baseCone`. -/
def BaseConeGoal : Prop := IsPositiveCone basePositiveClosure

/-- The paper's Theorem 1.1. `evenRank_hasFGPositiveCone` in `Main.lean` proves it,
stated in unfolded form. -/
def EvenRankGoal : Prop :=
  ∀ n : ℕ, 2 ≤ n → Even n → HasFGPositiveCone (FnZ n)

/-- Optional strengthening derived in the blueprint: at most 6(n-1)+1 generators.
Proved as `evenRank_generator_bound`. -/
def BoundedEvenRankGoal : Prop :=
  ∀ n : ℕ, 2 ≤ n → Even n →
    HasFGPositiveConeWithBound (FnZ n) (6 * (n - 1) + 1)

/-- An explicit interface to the odd-rank obstruction after the topology adapter.
Proved as `oddRankObstruction`. -/
def OddRankObstructionGoal : Prop :=
  ∀ n : ℕ, 2 ≤ n → Odd n →
    ∀ P : Subsemigroup (FnZ n), IsPositiveCone P → ¬ FinitelyDetermined P

/-- The paper's Corollary 1.2. `hasFGPositiveCone_iff_even` in `Main.lean` proves it,
stated in unfolded form. -/
def ClassificationGoal : Prop :=
  ∀ n : ℕ, 2 ≤ n → (HasFGPositiveCone (FnZ n) ↔ Even n)

/-- The paper's Lemma 2.1, without topology. Proved as
`finiteGenerationImpliesFiniteDetermination`. -/
def FiniteGenerationImpliesFiniteDeterminationGoal : Prop :=
  ∀ (G : Type u) [Group G] (P : Subsemigroup G),
    IsPositiveCone P → SemigroupFG P → FinitelyDetermined P

/-- Theorem 1.1, assuming the base cone theorem. Proved as `conditionalEvenRank`. -/
def ConditionalEvenRankGoal : Prop := BaseConeGoal → EvenRankGoal

/-- Corollary 1.2, assuming the base cone theorem and the odd-rank obstruction.
Proved as `conditionalClassification`. -/
def ConditionalClassificationGoal : Prop :=
  BaseConeGoal → OddRankObstructionGoal → ClassificationGoal

end FnZPositiveCones
