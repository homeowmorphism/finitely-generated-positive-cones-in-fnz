module

public import FnZPositiveCones.External.CircularIsolatedSeparation
public import FnZPositiveCones.External.CircularLastLetterDensity
public import FnZPositiveCones.External.CircularIsolatedReduction

@[expose] public section

/-!
Unconditional isolated circular-order separation and the odd-rank obstruction.
Actual last-letter density and successors discharge both geometric inputs to
the checked finite-trace separation argument. The normalized-domain endpoint
calculation then supplies the parity conclusion.
-/

namespace FnZPositiveCones
open CircularDynamics
universe u

/-- Distinct first-letter orbit closures are separated for every realization
of an isolated circular order on a finite-rank nonabelian free group. -/
theorem CircularRealization.firstLetter_closures_disjoint_of_isolated
    {ι : Type u} [Finite ι] [Nontrivial ι]
    {C : CircularGroupOrder (FreeGroup ι)} (R : CircularRealization C)
    (hi : IsOpen ({C} : Set (CircularGroupOrder (FreeGroup ι))))
    (s t : ι × Bool) (hst : s ≠ t) :
    Disjoint (closure (letterOrbit (realizationGenerators R) 0 s))
      (closure (letterOrbit (realizationGenerators R) 0 t)) := by
  obtain ⟨h, hh⟩ := R.isolated_has_successor hi
  exact R.firstLetter_closures_disjoint_of_isolated_of_lastLetter_density hi hh
    (R.derived_orbit_subset_lastLetterClosure hi) s t hst

/-- Mann–Rivas Proposition 4.7's separation conclusion, with realization,
last-letter density, and closed proper-trace avoidance all proved. -/
theorem isolatedCircularSeparation : IsolatedCircularSeparationGoal := by
  intro n hn C hi
  let : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  obtain ⟨R⟩ := C.exists_circularRealization
  exact ⟨R, R.firstLetter_closures_disjoint_of_isolated hi⟩

/-- The actual finite normalized domains and their connected endpoint graph
force even rank for every isolated circular order on a nonabelian free group. -/
theorem CircularRealization.even_card_of_isolated
    {ι : Type u} [Fintype ι] [Nontrivial ι]
    {C : CircularGroupOrder (FreeGroup ι)} (R : CircularRealization C)
    (hi : IsOpen ({C} : Set (CircularGroupOrder (FreeGroup ι)))) :
    Even (Fintype.card ι) :=
  R.even_card_of_isolated_of_separated hi
    (R.firstLetter_closures_disjoint_of_isolated hi)

/-- MMRT's general circular odd-rank obstruction, with no finite positive
semigroup generation premise or external dynamical assumption. -/
theorem circularOddRankObstruction : CircularOddRankObstructionGoal :=
  circularOddRankObstruction_of_isolated_separation isolatedCircularSeparation

end FnZPositiveCones
