module

public import FnZPositiveCones.External.NoncofinalDynamics
public import FnZPositiveCones.External.CircularQuotient

@[expose] public section

/-! Common fixed points for the primitive-generator perturbation in MMRT Claim 4. -/

namespace FnZPositiveCones
namespace NoncofinalDynamics

universe u
variable {G : Type u} [Group G] (ρ : G →* (ℝ ≃o ℝ))

/-- A point fixed by `a` can be moved rightward to a common fixed point of `a`
and the center. The central orbit is bounded by a higher central fixed point,
and its supremum is fixed by both maps. -/
theorem exists_common_fixed_ge (z : G) (hcentral : ∀ g : G, Commute z g)
    (hfix : ∃ y : ℝ, ρ z y = y) (hglobal : ∀ y : ℝ, ∃ g : G, ρ g y ≠ y)
    (a : G) (p : ℝ) (ha : ρ a p = p) :
    ∃ q : ℝ, p ≤ q ∧ ρ a q = q ∧ ρ z q = q := by
  obtain ⟨r, hr, hpr⟩ :=
    (not_bddAbove_iff.mp (central_fixedPoints_not_bddAbove ρ z hcentral hfix hglobal)) p
  let S : Set ℝ := Set.range (fun k : ℤ => ρ (z ^ k) p)
  have hS : S.Nonempty := Set.range_nonempty _
  have hb : BddAbove S := by
    refine ⟨r, ?_⟩
    rintro _ ⟨k, rfl⟩
    have h := (ρ (z ^ k)).strictMono hpr
    rw [fixed_zpow ρ z hr k] at h
    exact h.le
  have hpoint : ∀ y ∈ S, ρ a y = y := by
    rintro _ ⟨k, rfl⟩
    rw [commute_zpow_apply ρ z hcentral, ha]
  have himage : ρ a '' S = S := by
    ext y
    constructor
    · rintro ⟨w, hw, rfl⟩
      simpa only [hpoint w hw] using hw
    · intro hy
      exact ⟨y, hy, hpoint y hy⟩
  refine ⟨sSup S, le_csSup hb ⟨0, by simp⟩, ?_, orbit_sSup_fixed ρ z p hb⟩
  rw [(ρ a).map_csSup' hS hb, himage]

/-- Unbounded fixed points of marked generators produce unbounded common fixed
points with the center. The rank and marking may be arbitrary. -/
theorem unbounded_common_generator_fixedPoints {ι : Type u}
    (ρ : FreeGroup ι × Multiplicative ℤ →* (ℝ ≃o ℝ))
    (hfix : ∃ y : ℝ, ρ (cofinalProductZ (FreeGroup ι)) y = y)
    (hglobal : ∀ y : ℝ, ∃ g, ρ g y ≠ y)
    (hfar : ∀ b : ℝ, ∃ i : ι, ∃ p : ℝ, b < p ∧ ρ (FreeGroup.of i, 1) p = p) :
    ∀ b : ℝ, ∃ i : ι, ∃ p : ℝ, b < p ∧
      ρ (FreeGroup.of i, 1) p = p ∧ ρ (cofinalProductZ (FreeGroup ι)) p = p := by
  intro b
  obtain ⟨i, p, hbp, hp⟩ := hfar b
  obtain ⟨q, hpq, haq, hzq⟩ := exists_common_fixed_ge ρ _ cofinalProductZ_central
    hfix hglobal (FreeGroup.of i, 1) p hp
  exact ⟨i, q, hbp.trans_le hpq, haq, hzq⟩

end NoncofinalDynamics
end FnZPositiveCones
