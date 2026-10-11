module

public import FnZPositiveCones.External.CircularIsolatedSuccessor
public import FnZPositiveCones.External.CircularGapConnectivity
public import FnZPositiveCones.External.OddReduction

@[expose] public section

/-! Separation-to-parity adapter for isolated circular orders. The unconditional
separation theorem is supplied by `CircularIsolatedComplete.lean`. -/
namespace FnZPositiveCones
open CircularDynamics
universe u

/-- Isolation supplies the successor; separation supplies the already checked
normalized-domain construction. The endpoint argument then forces even rank. -/
theorem CircularRealization.even_card_of_isolated_of_separated
    {ι : Type u} [Fintype ι] [Nontrivial ι]
    {C : CircularGroupOrder (FreeGroup ι)} (R : CircularRealization C)
    (hi : IsOpen ({C} : Set (CircularGroupOrder (FreeGroup ι))))
    (hsep : ∀ s t, s ≠ t →
      Disjoint (closure (letterOrbit (realizationGenerators R) 0 s))
        (closure (letterOrbit (realizationGenerators R) 0 t))) : Even (Fintype.card ι) := by
  classical
  obtain ⟨a, ha⟩ := R.isolated_has_successor hi
  exact (finiteNormalizedDomains R a ha hsep).intervalData.even_card ha

/-- The separation interface is a proposition, not a postulate. -/
def IsolatedCircularSeparationGoal : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ C : CircularGroupOrder (FreeGroup (Fin n)),
    IsOpen ({C} : Set (CircularGroupOrder (FreeGroup (Fin n)))) →
    ∃ R : CircularRealization C, ∀ s t, s ≠ t →
      Disjoint (closure (letterOrbit (realizationGenerators R) 0 s))
        (closure (letterOrbit (realizationGenerators R) 0 t))

/-- The general circular obstruction now needs only the explicitly named
separation input; realization, discreteness, domains, connectivity and parity
are proved locally. -/
theorem circularOddRankObstruction_of_isolated_separation
    (hsep : IsolatedCircularSeparationGoal) : CircularOddRankObstructionGoal := by
  intro n hn hodd C hi
  let := Fin.nontrivial_iff_two_le.mpr hn
  obtain ⟨R, hR⟩ := hsep n hn C hi
  have he : Even n := by simpa only [Fintype.card_fin] using R.even_card_of_isolated_of_separated hi hR
  exact (Nat.not_even_iff_odd.mpr hodd) he

end FnZPositiveCones
