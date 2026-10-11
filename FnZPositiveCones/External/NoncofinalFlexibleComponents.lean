module

public import FnZPositiveCones.External.NoncofinalComponentPerturbation
public import FnZPositiveCones.External.NoncofinalTrajectory
public import FnZPositiveCones.External.NoncofinalFixedPoints

@[expose] public section

/-!
# Finite-sign deformation from an original-generator component entry

The finite trajectory bound is enlarged to protect old generator images.
A second unchanged generator prevents global fixed points outside the
protected ray. Two envelope modifications then give distinct completed orders.
The existence of the required marked-generator entry is not assumed implicitly.
-/

namespace FnZPositiveCones.NoncofinalFlexibleComponents

open NoncofinalPerturbation NoncofinalEnvelope NoncofinalComponentPerturbation

universe u
variable {ι : Type u}

/-- An unchanged generator without fixed points outside a protected ray prevents
new global fixed points; on the ray all original generator values are retained. -/
theorem replaceGenerator_no_global_fixed_of_other
    (ρ : FreeGroup ι × Multiplicative ℤ →* (ℝ ≃o ℝ)) (i j : ι) (hji : j ≠ i)
    (a : ℝ ≃o ℝ) (ha : Commute a (ρ (cofinalProductZ (FreeGroup ι)))) (b : ℝ)
    (hagree : ∀ x : ℝ, x ≤ b → a x = ρ (FreeGroup.of i, 1) x)
    (hother : ∀ x : ℝ, b < x → ρ (FreeGroup.of j, 1) x ≠ x)
    (hglobal : ∀ x : ℝ, ∃ g, ρ g x ≠ x) :
    ∀ x : ℝ, ∃ g, replaceGenerator ρ i a ha g x ≠ x := by
  intro x
  by_cases hxb : x ≤ b
  · by_contra hn
    push Not at hn
    have hgen (k : ι) : ρ (FreeGroup.of k, 1) x = x := by
      by_cases hki : k = i
      · subst k
        have h := hn (FreeGroup.of i, 1)
        rw [replaceGenerator_chosen, hagree x hxb] at h
        exact h
      · simpa only [replaceGenerator_other ρ i k a ha hki] using hn (FreeGroup.of k, 1)
    have hz : ρ (cofinalProductZ (FreeGroup ι)) x = x := by
      simpa only [cofinalProductZ, replaceGenerator_central] using hn (cofinalProductZ (FreeGroup ι))
    obtain ⟨g, hg⟩ := hglobal x
    exact hg (fixed_of_generators ρ x hgen hz g)
  · refine ⟨(FreeGroup.of j, 1), ?_⟩
    rw [replaceGenerator_other ρ i j a ha hji]
    exact hother x (lt_of_not_ge hxb)

private theorem positiveTail_agrees
    (ρ : FreeGroup ι × Multiplicative ℤ →* (ℝ ≃o ℝ)) (i : ι) (p : ℝ)
    (hi : ρ (FreeGroup.of i, 1) p = p) (hz : ρ (cofinalProductZ (FreeGroup ι)) p = p)
    (j : ι) (y : ℝ) (hy : y ≤ p) :
    positiveTailAction ρ i p hi hz (FreeGroup.of j, 1) y = ρ (FreeGroup.of j, 1) y := by
  by_cases hj : j = i
  · subst j
    rw [positiveTailAction, replaceGenerator_chosen]
    exact splice_of_le _ _ _ _ _ hy
  · rw [positiveTailAction, replaceGenerator_other _ _ _ _ _ hj]

private theorem negativeTail_agrees
    (ρ : FreeGroup ι × Multiplicative ℤ →* (ℝ ≃o ℝ)) (i : ι) (p : ℝ)
    (hi : ρ (FreeGroup.of i, 1) p = p) (hz : ρ (cofinalProductZ (FreeGroup ι)) p = p)
    (j : ι) (y : ℝ) (hy : y ≤ p) :
    negativeTailAction ρ i p hi hz (FreeGroup.of j, 1) y = ρ (FreeGroup.of j, 1) y := by
  by_cases hj : j = i
  · subst j
    rw [negativeTailAction, replaceGenerator_chosen]
    exact splice_of_le _ _ _ _ _ hy
  · rw [negativeTailAction, replaceGenerator_other _ _ _ _ _ hj]

/-- Two actual tail actions yield a different completed order while preserving
all finite tests controlled by the original trajectory bound. -/
theorem distinct_completion_of_common_fixed
    (O : LeftGroupOrder (FreeGroup ι × Multiplicative ℤ))
    (ρ σ : FreeGroup ι × Multiplicative ℤ →* (ℝ ≃o ℝ)) (x b : ℝ)
    (F : Finset (FreeGroup ι × Multiplicative ℤ))
    (hreal : ∀ g h, O.order.le g h ↔ ρ g x ≤ ρ h x)
    (hb : ∀ τ : FreeGroup ι × Multiplicative ℤ →* (ℝ ≃o ℝ),
      (∀ m : Multiplicative ℤ, τ (1, m) = ρ (1, m)) →
      (∀ i : ι, ∀ y : ℝ, y ≤ b → τ (FreeGroup.of i, 1) y = ρ (FreeGroup.of i, 1) y) →
      ∀ g ∈ F, τ g x = ρ g x)
    (hcenter : ∀ m : Multiplicative ℤ, σ (1, m) = ρ (1, m))
    (hagree : ∀ i : ι, ∀ y : ℝ, y ≤ b → σ (FreeGroup.of i, 1) y = ρ (FreeGroup.of i, 1) y)
    (hglobal : ∀ y : ℝ, ∃ g, σ g y ≠ y)
    (hx : σ (cofinalProductZ (FreeGroup ι)) x ≠ x)
    (i : ι) (p : ℝ) (hbp : b ≤ p)
    (hi : σ (FreeGroup.of i, 1) p = p) (hz : σ (cofinalProductZ (FreeGroup ι)) p = p) :
    ∃ τ : FreeGroup ι × Multiplicative ℤ →* (ℝ ≃o ℝ), O.actionCompletion τ x ≠ O ∧
      (∀ g ∈ F, τ g x = ρ g x) ∧
      ∀ g ∈ F, (g ∈ (leftOrderCone (O.actionCompletion τ x)).1 ↔ g ∈ (leftOrderCone O).1) := by
  let α := positiveTailAction σ i p hi hz
  let β := negativeTailAction σ i p hi hz
  have hα : ∀ g ∈ F, α g x = ρ g x := by
    apply hb α
    · intro m
      exact (positiveTailAction_central σ i p hi hz m).trans (hcenter m)
    · intro j y hy
      exact (positiveTail_agrees σ i p hi hz j y (hy.trans hbp)).trans (hagree j y hy)
  have hβ : ∀ g ∈ F, β g x = ρ g x := by
    apply hb β
    · intro m
      exact (negativeTailAction_central σ i p hi hz m).trans (hcenter m)
    · intro j y hy
      exact (negativeTail_agrees σ i p hi hz j y (hy.trans hbp)).trans (hagree j y hy)
  have hne := O.actionCompletions_ne_of_opposite_tail α β x x p p (FreeGroup.of i, 1)
    (orbit_unbounded_above α (positiveTailAction_no_global_fixed σ i p hi hz hglobal) x)
    (orbit_unbounded_above β (negativeTailAction_no_global_fixed σ i p hi hz hglobal) x)
    (positiveTailAction_orbit_strict σ i p hi hz x hx)
    (negativeTailAction_orbit_strict σ i p hi hz x hx)
  by_cases hαO : O.actionCompletion α x = O
  · refine ⟨β, ?_, hβ, O.actionCompletion_signs ρ β x hreal F hβ⟩
    intro hβO
    exact hne (hαO.trans hβO.symm)
  · exact ⟨α, hαO, hα, O.actionCompletion_signs ρ α x hreal F hα⟩

/-- For each original marked generator, a concrete bound protects all finite
word tests and their old generator images. An entry beyond it produces a
checked distinct completed order, provided another unchanged generator has
no fixed point outside the originally prescribed protected ray. -/
theorem exists_component_deformation_bound
    (O : LeftGroupOrder (FreeGroup ι × Multiplicative ℤ))
    (ρ : FreeGroup ι × Multiplicative ℤ →* (ℝ ≃o ℝ)) (x : ℝ)
    (hreal : ∀ g h, O.order.le g h ↔ ρ g x ≤ ρ h x)
    (hglobal : ∀ y : ℝ, ∃ g, ρ g y ≠ y)
    (hx : ρ (cofinalProductZ (FreeGroup ι)) x ≠ x)
    (F : Finset (FreeGroup ι × Multiplicative ℤ)) (b₀ : ℝ) (i : ι) :
    ∃ B : ℝ, ∀ (j : ι), j ≠ i →
      (∀ y : ℝ, b₀ < y → ρ (FreeGroup.of j, 1) y ≠ y) →
      ∀ (f : ℝ ≃o ℝ) (l t : ℝ) (_ht : f t ≠ t), B < l → l < t →
        Set.Ioc l t ⊆ motionComponent f t → motionComponent f t ⊆ Set.Ioi l →
        ρ (FreeGroup.of i, 1) l ∈ motionComponent f t →
        Commute f (ρ (cofinalProductZ (FreeGroup ι))) →
        (∀ y : ℝ, y ∈ motionComponent f t ↔
          ρ (cofinalProductZ (FreeGroup ι)) y ∈ motionComponent f t) →
        ρ (cofinalProductZ (FreeGroup ι)) l = l →
        ∃ τ : FreeGroup ι × Multiplicative ℤ →* (ℝ ≃o ℝ), O.actionCompletion τ x ≠ O ∧
          (∀ g ∈ F, τ g x = ρ g x) ∧
          ∀ g ∈ F, (g ∈ (leftOrderCone (O.actionCompletion τ x)).1 ↔ g ∈ (leftOrderCone O).1) := by
  obtain ⟨b, hb⟩ := NoncofinalTrajectory.exists_finiteTrajectory_bound ρ F x
  let c := max b b₀
  let a := ρ (FreeGroup.of i, 1)
  refine ⟨max c (a c), ?_⟩
  intro j hji hother f l t ht hBl hlt hleft hlower hentry hfq hqJ hql
  have hcl : c < l := (le_max_left c (a c)).trans_lt hBl
  have hacl : a c < l := (le_max_right c (a c)).trans_lt hBl
  have haq : Commute a (ρ (cofinalProductZ (FreeGroup ι))) :=
    (cofinalProductZ_central (FreeGroup.of i, 1)).symm.map ρ
  obtain ⟨k, hcomm, ⟨y, hly, hnewfix⟩, hagree⟩ := exists_component_perturbation f a
    (ρ (cofinalProductZ (FreeGroup ι))) l t ht hlt hleft hlower hentry hfq haq hqJ
  let anew := componentTwist f t ht k * a
  let σ := replaceGenerator ρ i anew hcomm
  have hprotected : ∀ y : ℝ, y ≤ c → anew y = a y := by
    intro y hy
    apply hagree y
    intro hyJ
    exact (hlower hyJ).not_ge ((a.monotone hy).trans hacl.le)
  have hσcenter : ∀ m : Multiplicative ℤ, σ (1, m) = ρ (1, m) :=
    replaceGenerator_central ρ i anew hcomm
  have hσagree : ∀ j : ι, ∀ y : ℝ, y ≤ c → σ (FreeGroup.of j, 1) y = ρ (FreeGroup.of j, 1) y := by
    intro j y hy
    by_cases hji : j = i
    · subst j
      simp only [σ, replaceGenerator_chosen]
      exact hprotected y hy
    · exact congrArg (fun e : ℝ ≃o ℝ => e y) (replaceGenerator_other ρ i j anew hcomm hji)
  have hσglobal : ∀ y : ℝ, ∃ g, σ g y ≠ y :=
    replaceGenerator_no_global_fixed_of_other ρ i j hji anew hcomm c hprotected
      (fun y hy => hother y ((le_max_right b b₀).trans_lt hy)) hglobal
  have hσy : σ (FreeGroup.of i, 1) y = y := by
    simp only [σ, replaceGenerator_chosen]
    exact hnewfix
  have hσql : σ (cofinalProductZ (FreeGroup ι)) l = l := by
    rw [show σ (cofinalProductZ (FreeGroup ι)) = ρ (cofinalProductZ (FreeGroup ι)) from hσcenter _]
    exact hql
  obtain ⟨p, hyp, hip, hqp⟩ := NoncofinalDynamics.exists_common_fixed_ge σ
    (cofinalProductZ (FreeGroup ι)) cofinalProductZ_central ⟨l, hσql⟩ hσglobal
    (FreeGroup.of i, 1) y hσy
  have hxp : σ (cofinalProductZ (FreeGroup ι)) x ≠ x := by
    rwa [show σ (cofinalProductZ (FreeGroup ι)) = ρ (cofinalProductZ (FreeGroup ι)) from hσcenter _]
  exact distinct_completion_of_common_fixed O ρ σ x b F hreal hb hσcenter
    (fun j y hy => hσagree j y (hy.trans (le_max_left b b₀))) hσglobal hxp i p
    ((le_max_left b b₀).trans (hcl.le.trans (hly.le.trans hyp))) hip hqp

/-- A finite original marking admits one bound chosen before the entering
marked generator. This maximum includes the protected old images for every
original generator and is independent of which original generator enters. -/
theorem exists_uniform_component_deformation_bound [Finite ι]
    (O : LeftGroupOrder (FreeGroup ι × Multiplicative ℤ))
    (ρ : FreeGroup ι × Multiplicative ℤ →* (ℝ ≃o ℝ)) (x : ℝ)
    (hreal : ∀ g h, O.order.le g h ↔ ρ g x ≤ ρ h x)
    (hglobal : ∀ y : ℝ, ∃ g, ρ g y ≠ y)
    (hx : ρ (cofinalProductZ (FreeGroup ι)) x ≠ x)
    (F : Finset (FreeGroup ι × Multiplicative ℤ)) (b₀ : ℝ) :
    ∃ B : ℝ, ∀ (i j : ι), j ≠ i →
      (∀ y : ℝ, b₀ < y → ρ (FreeGroup.of j, 1) y ≠ y) →
      ∀ (f : ℝ ≃o ℝ) (l t : ℝ) (_ht : f t ≠ t), B < l → l < t →
        Set.Ioc l t ⊆ motionComponent f t → motionComponent f t ⊆ Set.Ioi l →
        ρ (FreeGroup.of i, 1) l ∈ motionComponent f t →
        Commute f (ρ (cofinalProductZ (FreeGroup ι))) →
        (∀ y : ℝ, y ∈ motionComponent f t ↔
          ρ (cofinalProductZ (FreeGroup ι)) y ∈ motionComponent f t) →
        ρ (cofinalProductZ (FreeGroup ι)) l = l →
        ∃ τ : FreeGroup ι × Multiplicative ℤ →* (ℝ ≃o ℝ), O.actionCompletion τ x ≠ O ∧
          (∀ g ∈ F, τ g x = ρ g x) ∧
          ∀ g ∈ F, (g ∈ (leftOrderCone (O.actionCompletion τ x)).1 ↔ g ∈ (leftOrderCone O).1) := by
  classical
  choose B hB using (fun i : ι =>
    exists_component_deformation_bound O ρ x hreal hglobal hx F b₀ i)
  obtain ⟨b, hb⟩ := (Set.finite_range B).bddAbove
  refine ⟨b, ?_⟩
  intro i j hji hother f l t ht hbl hlt hleft hlower hentry hfq hqJ hql
  exact hB i j hji hother f l t ht ((hb ⟨i, rfl⟩).trans_lt hbl)
    hlt hleft hlower hentry hfq hqJ hql

end FnZPositiveCones.NoncofinalFlexibleComponents
