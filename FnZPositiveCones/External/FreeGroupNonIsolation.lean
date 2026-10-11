module

public import FnZPositiveCones.External.FreeGroupOrbitPerturbation
public import FnZPositiveCones.External.OrderedActionsStabilizer

@[expose] public section

/-! No left order on a nonabelian countable free group is isolated. -/
namespace FnZPositiveCones.FreeGroupNonIsolation
universe u
variable {ι : Type u} [Nontrivial ι] [Countable ι]

/-- Finite comparisons can always be preserved by two different orders.
The realization and the required finite-trace perturbation are constructed. -/
theorem not_isolated (O : LeftGroupOrder (FreeGroup ι)) :
    ¬ IsOpen ({O} : Set (LeftGroupOrder (FreeGroup ι))) := by
  obtain ⟨R⟩ := O.exists_tightRealization
  exact O.not_isolated_of_finite_trace_stabilizers R.action R.base R.order_iff
    (FreeGroupOrbitPerturbation.exists_finite_trace_stabilizer R.action R.base R.unbounded_above)

/-- A strict positive cone on a nonabelian countable free group is never
finitely determined. Finite generation is not assumed. -/
theorem not_finitelyDetermined (P : PositiveCone (FreeGroup ι)) :
    ¬ FinitelyDetermined P.1 := by
  intro hfd
  exact not_isolated (coneLeftOrder P)
    ((finiteDetermination_iff_leftOrder_isolated P).mp hfd)

end FnZPositiveCones.FreeGroupNonIsolation
