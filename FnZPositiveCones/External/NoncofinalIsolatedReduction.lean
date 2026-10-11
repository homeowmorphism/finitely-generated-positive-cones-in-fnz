module

public import FnZPositiveCones.External.NoncofinalIsolatedTower
public import FnZPositiveCones.External.IsolatedQuotientCone
public import FnZPositiveCones.External.FreeGroupNonIsolation

@[expose] public section

/-! The nontrivial-projection step for isolated noncofinal orders, with no
finite-positive-generation hypothesis. -/

namespace FnZPositiveCones.NoncofinalIsolatedReduction

open NoncofinalSubgroupProduct NoncofinalFreeTowerModel

universe u
variable {ι : Type u} [Nontrivial ι] [Countable ι]

/-- MMRT Claim 2's nontrivial projection follows from quotient isolation and
the independently checked nonisolation of nonabelian free groups. -/
theorem bounded_projection_ne_bot
    (P : PositiveCone (FreeGroup ι × Multiplicative ℤ)) (hfd : FinitelyDetermined P.1) :
    projection ((coneLeftOrder P).centralBoundedSubgroup
      (cofinalProductZ (FreeGroup ι)) cofinalProductZ_central) ≠ ⊥ := by
  intro hbot
  obtain ⟨Q, hQ⟩ :=
    IsolatedQuotientCone.exists_finitelyDetermined_free_cone_of_bounded_projection_eq_bot
      P hfd hbot
  exact FreeGroupNonIsolation.not_finitelyDetermined Q hQ

/-- The isolated convex-jump reduction now has no undischarged subgroup
hypothesis. The resulting primitive may still depend on the real bound. -/
theorem exists_model_with_primitive_fixed_above
    (P : PositiveCone (FreeGroup ι × Multiplicative ℤ)) (hfd : FinitelyDetermined P.1)
    (hnon : ¬ (coneLeftOrder P).IsCofinal (cofinalProductZ (FreeGroup ι))) :
    ∃ M : NoncofinalIsolatedTower.Model P, Nontrivial (Basis M.H) ∧
      Nonempty (TightRealization (coneLeftOrder (modelCone P M.H M.center_mem))) ∧
      ∀ R : TightRealization (coneLeftOrder (modelCone P M.H M.center_mem)), ∀ b : ℝ,
        ∃ a : FreeGroup (Basis M.H), NoncofinalPrimitiveEntry.IsPrimitive a ∧
          ∃ y : ℝ, b < y ∧ R.action (a, 1) y = y := by
  obtain ⟨M⟩ := NoncofinalIsolatedTower.exists_model P hfd hnon
  have hne := bounded_projection_ne_bot P hfd
  exact ⟨M, M.basis_nontrivial hfd hne, M.exists_tightRealization,
    fun R b => M.primitive_fixed_above hfd hne R b⟩

end FnZPositiveCones.NoncofinalIsolatedReduction
