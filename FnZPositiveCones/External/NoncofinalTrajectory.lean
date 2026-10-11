module

public import FnZPositiveCones.External.NoncofinalDynamics
public import FnZPositiveCones.External.OrderedActionsCompletion
public import FnZPositiveCones.External.NoncofinalEnvelope
public import FnZPositiveCones.External.OrderedActionsSemiconjugacy

@[expose] public section

/-!
# Finite orbit trajectories for the noncofinal perturbation

A finite set of free-group words only evaluates marked generators on a bounded
set of points. Agreement of generators on a sufficiently long left ray thus
preserves all specified orbit values, including words with inverse letters.
-/

namespace FnZPositiveCones
namespace NoncofinalTrajectory

universe u
variable {ι : Type u}

/-- Each fixed free word and basepoint admits a bound controlling its complete
trajectory under arbitrary changes of the marked generators. -/
theorem exists_freeWord_bound (ρ : FreeGroup ι →* (ℝ ≃o ℝ)) (g : FreeGroup ι) (x : ℝ) :
    ∃ b : ℝ, ∀ σ : FreeGroup ι →* (ℝ ≃o ℝ),
      (∀ i : ι, ∀ y : ℝ, y ≤ b → σ (FreeGroup.of i) y = ρ (FreeGroup.of i) y) →
      σ g x = ρ g x := by
  induction g using FreeGroup.induction_on generalizing x with
  | one =>
    exact ⟨x, fun σ _ => by simp only [map_one, RelIso.one_apply]⟩
  | of i => exact ⟨x, fun σ h => h i x le_rfl⟩
  | inv_of i _ =>
    refine ⟨ρ (FreeGroup.of i)⁻¹ x, ?_⟩
    intro σ h
    apply (σ (FreeGroup.of i)).injective
    rw [← NoncofinalDynamics.act_mul, mul_inv_cancel, NoncofinalDynamics.act_one,
      h i _ le_rfl, ← NoncofinalDynamics.act_mul, mul_inv_cancel, NoncofinalDynamics.act_one]
  | mul g h ihg ihh =>
    obtain ⟨b, hb⟩ := ihh x
    obtain ⟨c, hc⟩ := ihg (ρ h x)
    refine ⟨max b c, ?_⟩
    intro σ hagree
    rw [NoncofinalDynamics.act_mul, NoncofinalDynamics.act_mul,
      hb σ (fun i y hy => hagree i y (hy.trans (le_max_left _ _)))]
    exact hc σ (fun i y hy => hagree i y (hy.trans (le_max_right _ _)))

/-- One product-group word has a finite trajectory bound when the central factor
is preserved exactly. -/
theorem exists_productWord_bound (ρ : FreeGroup ι × Multiplicative ℤ →* (ℝ ≃o ℝ))
    (g : FreeGroup ι × Multiplicative ℤ) (x : ℝ) :
    ∃ b : ℝ, ∀ σ : FreeGroup ι × Multiplicative ℤ →* (ℝ ≃o ℝ),
      (∀ m : Multiplicative ℤ, σ (1, m) = ρ (1, m)) →
      (∀ i : ι, ∀ y : ℝ, y ≤ b → σ (FreeGroup.of i, 1) y = ρ (FreeGroup.of i, 1) y) →
      σ g x = ρ g x := by
  obtain ⟨b, hb⟩ := exists_freeWord_bound
    (ρ.comp (MonoidHom.inl (FreeGroup ι) (Multiplicative ℤ))) g.1 (ρ (1, g.2) x)
  refine ⟨b, ?_⟩
  intro σ hz hagree
  have h := hb (σ.comp (MonoidHom.inl (FreeGroup ι) (Multiplicative ℤ))) hagree
  have he : g = (g.1, 1) * (1, g.2) := by simp
  rw [he, NoncofinalDynamics.act_mul, NoncofinalDynamics.act_mul, hz]
  exact h

/-- One common bound controls all words in a finite sign test. -/
theorem exists_finiteTrajectory_bound (ρ : FreeGroup ι × Multiplicative ℤ →* (ℝ ≃o ℝ))
    (F : Finset (FreeGroup ι × Multiplicative ℤ)) (x : ℝ) :
    ∃ b : ℝ, ∀ σ : FreeGroup ι × Multiplicative ℤ →* (ℝ ≃o ℝ),
      (∀ m : Multiplicative ℤ, σ (1, m) = ρ (1, m)) →
      (∀ i : ι, ∀ y : ℝ, y ≤ b → σ (FreeGroup.of i, 1) y = ρ (FreeGroup.of i, 1) y) →
      ∀ g ∈ F, σ g x = ρ g x := by
  classical
  choose b hb using (fun g => exists_productWord_bound ρ g x)
  obtain ⟨B, hB⟩ := (F.finite_toSet.image b).bddAbove
  refine ⟨B, ?_⟩
  intro σ hz hagree g hg
  apply hb g σ hz
  intro i y hy
  exact hagree i y (hy.trans (hB ⟨g, hg, rfl⟩))

open NoncofinalEnvelope NoncofinalPerturbation

private theorem positiveTailAction_agrees_below
    (ρ : FreeGroup ι × Multiplicative ℤ →* (ℝ ≃o ℝ)) (i : ι) (p : ℝ)
    (hi : ρ (FreeGroup.of i, 1) p = p) (hz : ρ (cofinalProductZ (FreeGroup ι)) p = p)
    (j : ι) (y : ℝ) (hy : y ≤ p) :
    positiveTailAction ρ i p hi hz (FreeGroup.of j, 1) y = ρ (FreeGroup.of j, 1) y := by
  by_cases hj : j = i
  · subst j
    rw [positiveTailAction, replaceGenerator_chosen]
    exact splice_of_le _ _ _ _ _ hy
  · rw [positiveTailAction, replaceGenerator_other _ _ _ _ _ hj]

private theorem negativeTailAction_agrees_below
    (ρ : FreeGroup ι × Multiplicative ℤ →* (ℝ ≃o ℝ)) (i : ι) (p : ℝ)
    (hi : ρ (FreeGroup.of i, 1) p = p) (hz : ρ (cofinalProductZ (FreeGroup ι)) p = p)
    (j : ι) (y : ℝ) (hy : y ≤ p) :
    negativeTailAction ρ i p hi hz (FreeGroup.of j, 1) y = ρ (FreeGroup.of j, 1) y := by
  by_cases hj : j = i
  · subst j
    rw [negativeTailAction, replaceGenerator_chosen]
    exact splice_of_le _ _ _ _ _ hy
  · rw [negativeTailAction, replaceGenerator_other _ _ _ _ _ hj]

/-- A concrete case of MMRT's first perturbation argument: if marked free
generators have common fixed points with the center arbitrarily far to the
right, every finite sign test admits a different left order satisfying it.

The hypothesis explicitly refers to the fixed marking. No assertion about
arbitrary primitive elements or the remaining crossing argument is hidden here. -/
theorem not_isolated_of_unbounded_generator_fixedPoints
    (O : LeftGroupOrder (FreeGroup ι × Multiplicative ℤ))
    (ρ : FreeGroup ι × Multiplicative ℤ →* (ℝ ≃o ℝ)) (x : ℝ)
    (hreal : ∀ g h, O.order.le g h ↔ ρ g x ≤ ρ h x)
    (hglobal : ∀ y : ℝ, ∃ g, ρ g y ≠ y)
    (hx : ρ (cofinalProductZ (FreeGroup ι)) x ≠ x)
    (hfar : ∀ b : ℝ, ∃ i : ι, ∃ p : ℝ, b < p ∧
      ρ (FreeGroup.of i, 1) p = p ∧ ρ (cofinalProductZ (FreeGroup ι)) p = p) :
    ¬ IsOpen ({O} : Set (LeftGroupOrder (FreeGroup ι × Multiplicative ℤ))) := by
  intro hiso
  have hfd : FinitelyDetermined (leftOrderCone O).1 :=
    (finiteDetermination_iff_leftOrder_isolated (leftOrderCone O)).mpr (by simpa using hiso)
  obtain ⟨F, hFP, hdet⟩ := hfd
  obtain ⟨b, hb⟩ := exists_finiteTrajectory_bound ρ F x
  obtain ⟨i, p, hbp, hi, hz⟩ := hfar b
  let σ := positiveTailAction ρ i p hi hz
  let τ := negativeTailAction ρ i p hi hz
  have hsagree : ∀ g ∈ F, σ g x = ρ g x := by
    apply hb σ (positiveTailAction_central ρ i p hi hz)
    intro j y hy
    exact positiveTailAction_agrees_below ρ i p hi hz j y (hy.trans hbp.le)
  have htagree : ∀ g ∈ F, τ g x = ρ g x := by
    apply hb τ (negativeTailAction_central ρ i p hi hz)
    intro j y hy
    exact negativeTailAction_agrees_below ρ i p hi hz j y (hy.trans hbp.le)
  have heq (α : FreeGroup ι × Multiplicative ℤ →* (ℝ ≃o ℝ))
      (hα : ∀ g ∈ F, α g x = ρ g x) : O.actionCompletion α x = O := by
    have hs := O.actionCompletion_signs ρ α x hreal F hα
    have hcone : (leftOrderCone (O.actionCompletion α x)).1 = (leftOrderCone O).1 :=
      hdet _ (leftOrderCone (O.actionCompletion α x)).2
        (fun g hg => (hs g hg).mpr (hFP hg))
    have he : leftOrderCone (O.actionCompletion α x) = leftOrderCone O := Subtype.ext hcone
    simpa using congrArg coneLeftOrder he
  have hsunbound : ∀ r : ℝ, ∃ g, r < σ g x :=
    orbit_unbounded_above σ (positiveTailAction_no_global_fixed ρ i p hi hz hglobal) x
  have htunbound : ∀ r : ℝ, ∃ g, r < τ g x :=
    orbit_unbounded_above τ (negativeTailAction_no_global_fixed ρ i p hi hz hglobal) x
  have hne := O.actionCompletions_ne_of_opposite_tail σ τ x x p p (FreeGroup.of i, 1)
    hsunbound htunbound (positiveTailAction_orbit_strict ρ i p hi hz x hx)
    (negativeTailAction_orbit_strict ρ i p hi hz x hx)
  exact hne ((heq σ hsagree).trans (heq τ htagree).symm)

end NoncofinalTrajectory
end FnZPositiveCones
