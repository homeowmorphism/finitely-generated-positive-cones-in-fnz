module

public import FnZPositiveCones.External.CircularIsolatedComplete
public import FnZPositiveCones.External.NoncofinalEndpointAction

@[expose] public section

/-! The full odd-rank non-isolation theorem and its strict-cone adapter.

The circular obstruction and central cofinality are proved for isolated orders
without a finite semigroup generation hypothesis. The exact cone/order
homeomorphism transfers their conclusion to finite determination.
-/

namespace FnZPositiveCones

/-- MMRT Theorem 1.1, odd-rank direction: every left order on the product
of an odd-rank nonabelian free group with the integers is non-isolated. -/
theorem mmrt_no_isolated_order_odd : LeftOrderOddRankObstructionGoal := by
  intro n hn hodd O hi
  have hfd : FinitelyDetermined (leftOrderCone O).1 :=
    (finiteDetermination_iff_leftOrder_isolated (leftOrderCone O)).mpr (by simpa using hi)
  exact oddRankObstruction_of_circular_of_cofinal circularOddRankObstruction
    NoncofinalEndpointAction.isolatedOddRankCenterCofinal n hn hodd
    (leftOrderCone O).1 (leftOrderCone O).2 hfd

/-- No strict positive cone on an odd-rank product is finitely determined. -/
theorem oddRankObstruction : OddRankObstructionGoal :=
  oddRankObstruction_of_leftOrderObstruction mmrt_no_isolated_order_odd

end FnZPositiveCones
