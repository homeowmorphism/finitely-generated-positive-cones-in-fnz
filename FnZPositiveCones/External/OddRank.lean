module

public import FnZPositiveCones.Cone.Topology

@[expose] public section

/-! The precise topological adapter for the external odd-rank theorem.

The theorem below proves the adapter with its mathematical input explicitly
quantified. `OddRankComplete.lean` supplies the unconditional MMRT theorem.
-/

namespace FnZPositiveCones

/-- The precise left-order-space form of the required MMRT odd-rank statement. -/
def LeftOrderOddRankObstructionGoal : Prop :=
  ∀ n : ℕ, 2 ≤ n → Odd n →
    ∀ O : LeftGroupOrder (FnZ n), ¬ IsOpen ({O} : Set (LeftGroupOrder (FnZ n)))

/-- Transfer non-isolation of odd-rank left orders to the cone interface.
This adapter is conditional on the actual external non-isolation theorem. -/
theorem oddRankObstruction_of_leftOrderObstruction
    (hMMRT : LeftOrderOddRankObstructionGoal) : OddRankObstructionGoal := by
  intro n hn hodd P hP hfd
  exact hMMRT n hn hodd (coneLeftOrder ⟨P, hP⟩)
    ((finiteDetermination_iff_leftOrder_isolated ⟨P, hP⟩).mp hfd)

end FnZPositiveCones
