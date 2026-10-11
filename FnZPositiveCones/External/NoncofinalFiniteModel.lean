module

public import FnZPositiveCones.External.NoncofinalFreeTowerModel
public import FnZPositiveCones.External.InfiniteRank

@[expose] public section

namespace FnZPositiveCones
universe u v

/-- Finite positive generation rules out an infinite free basis, by the
checked local generator-reversal argument. -/
theorem finite_free_basis_of_semigroupFG {ι : Type u} {H : Type v} [Group H]
    (P : PositiveCone (FreeGroup ι × H)) (hfg : SemigroupFG P.1) : Finite ι := by
  rcases finite_or_infinite ι with hf | hi
  · exact hf
  · let := hi
    exact False.elim (InfiniteFreeRank.not_finitelyDetermined P.1 P.2
      (semigroupFG_finitelyDetermined P.2 hfg))

namespace NoncofinalFreeTowerModel

/-- The constructed Nielsen–Schreier model has a finite actual basis; an
infinite-rank model is excluded by its inherited finite positive generation. -/
theorem Model.finite_basis {ι : Type u}
    {P : PositiveCone (FreeGroup ι × Multiplicative ℤ)} (M : Model P) : Finite (Basis M.H) :=
  finite_free_basis_of_semigroupFG (modelCone P M.H M.center_mem) M.cone_fg

end NoncofinalFreeTowerModel
end FnZPositiveCones
