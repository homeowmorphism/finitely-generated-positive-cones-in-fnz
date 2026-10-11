module

public import FnZPositiveCones.External.OrderedActionsCollapse
public import FnZPositiveCones.External.NoncofinalPrimitiveEntry

@[expose] public section

namespace FnZPositiveCones.OrderedActions
universe u
variable {G : Type u} [Group G]

/-- Fibers of a continuous monotone surjection of the line are nonempty compact intervals. -/
theorem factor_fiber_compact (p : ℝ → ℝ) (hm : Monotone p) (hc : Continuous p)
    (hs : Function.Surjective p) (y : ℝ) :
    IsCompact (p ⁻¹' {y}) ∧ (p ⁻¹' {y}).Nonempty := by
  obtain ⟨l, hl⟩ := hs (y - 1)
  obtain ⟨r, hr⟩ := hs (y + 1)
  have hsub : p ⁻¹' {y} ⊆ Set.Icc l r := by
    intro x hx
    have hx' : p x = y := hx
    constructor
    · by_contra h
      have hh := hm (le_of_not_ge h)
      rw [hl, hx'] at hh
      linarith
    · by_contra h
      have hh := hm (le_of_not_ge h)
      rw [hr, hx'] at hh
      linarith
  refine ⟨isCompact_Icc.of_isClosed_subset (isClosed_singleton.preimage hc) hsub, ?_⟩
  obtain ⟨x, hx⟩ := hs y
  exact ⟨x, hx⟩

/-- A fixed point in a monotone factor lifts to an actual fixed point upstairs. -/
theorem lift_fixedPoint_of_factor (ρ σ : G →* (ℝ ≃o ℝ)) (p : ℝ → ℝ)
    (hm : Monotone p) (hc : Continuous p) (hs : Function.Surjective p)
    (he : ∀ g x, p (ρ g x) = σ g (p x)) (g : G) (y : ℝ) (hy : σ g y = y) :
    ∃ x : ℝ, p x = y ∧ ρ g x = x := by
  obtain ⟨hcompact, hnonempty⟩ := factor_fiber_compact p hm hc hs y
  obtain ⟨x, hx⟩ := hcompact.exists_isLeast hnonempty
  have hx' : p x = y := hx.1
  have hf : p (ρ g x) = y := by rw [he, hx', hy]
  have hi : p (ρ g⁻¹ x) = y := by
    rw [he, hx']
    have hh := congrArg (σ g⁻¹) hy
    simpa only [map_inv, RelIso.inv_apply_self] using hh.symm
  refine ⟨x, hx', le_antisymm ?_ (hx.2 hf)⟩
  have hh := (ρ g).monotone (hx.2 hi)
  simpa only [map_inv, RelIso.apply_inv_self] using hh

/-- Central triviality removes the integer coordinate of a product action. -/
theorem action_eq_free_coordinate (σ : (G × Multiplicative ℤ) →* (ℝ ≃o ℝ))
    (hz : σ (cofinalProductZ G) = 1) (g : G × Multiplicative ℤ) :
    σ g = σ (g.1, 1) := by
  have hg : g = cofinalProductZ G ^ g.2.toAdd * (g.1, 1) := by
    apply Prod.ext
    · simp [cofinalProductZ]
    · apply Multiplicative.toAdd.injective
      simp [cofinalProductZ]
  conv_lhs => rw [hg, map_mul, map_zpow, hz, one_zpow, one_mul]

/-- Minimality of the product factor is minimality of its free-factor action. -/
theorem free_factor_minimal (σ : (G × Multiplicative ℤ) →* (ℝ ≃o ℝ))
    (hz : σ (cofinalProductZ G) = 1)
    (hmin : ∀ x, DenseRange (fun g => σ g x)) :
    ∀ x, DenseRange (fun g : G => σ (g, 1) x) := by
  intro x
  have hr : Set.range (fun g : G × Multiplicative ℤ => σ g x) =
      Set.range (fun g : G => σ (g, 1) x) := by
    ext y
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨g.1, by dsimp only; rw [action_eq_free_coordinate σ hz g]⟩
    · rintro ⟨g, rfl⟩
      exact ⟨(g, 1), rfl⟩
  simpa only [DenseRange, hr] using hmin x

/-- Absence of fixed points of primitive elements survives taking the factor. -/
theorem primitive_no_fixed_factor {ι : Type u}
    (ρ σ : (FreeGroup ι × Multiplicative ℤ) →* (ℝ ≃o ℝ)) (p : ℝ → ℝ)
    (hm : Monotone p) (hc : Continuous p) (hs : Function.Surjective p)
    (he : ∀ g x, p (ρ g x) = σ g (p x))
    (hn : ∀ a : FreeGroup ι, NoncofinalPrimitiveEntry.IsPrimitive a →
      ∀ x : ℝ, ρ (a, 1) x ≠ x) :
    ∀ a : FreeGroup ι, NoncofinalPrimitiveEntry.IsPrimitive a →
      ∀ x : ℝ, σ (a, 1) x ≠ x := by
  intro a ha y hy
  obtain ⟨x, _, hx⟩ := lift_fixedPoint_of_factor ρ σ p hm hc hs he (a, 1) y hy
  exact hn a ha x hx

end FnZPositiveCones.OrderedActions
