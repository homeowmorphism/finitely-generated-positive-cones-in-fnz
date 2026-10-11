module

public import FnZPositiveCones.External.OrderedActionsSemiconjugacy
public import FnZPositiveCones.External.NoncofinalMinimalAction
public import Mathlib.Topology.Order.MonotoneContinuity

@[expose] public section

namespace FnZPositiveCones
universe u
variable {G : Type u} [Group G]

namespace LeftGroupOrder

/-- A monotone orbit map recovers the original order when ties are resolved
with that same order. The orbit may have a nontrivial stabilizer. -/
theorem actionCompletion_eq_of_monotone (O : LeftGroupOrder G)
    (ρ : G →* (ℝ ≃o ℝ)) (x : ℝ)
    (hmono : ∀ a b, O.order.le a b → ρ a x ≤ ρ b x) :
    O.actionCompletion ρ x = O := by
  apply ext_order
  apply LinearOrder.ext
  intro a b
  rw [actionCompletion_le]
  constructor
  · rintro (h | ⟨_, h⟩)
    · by_contra hn
      let := O.order
      exact h.not_ge (hmono b a (le_of_not_ge hn))
    · exact h
  · intro h
    rcases lt_or_eq_of_le (hmono a b h) with hlt | he
    · exact Or.inl hlt
    · exact Or.inr ⟨he, h⟩

end LeftGroupOrder

namespace TightRealization
variable {O : LeftGroupOrder G} (R : TightRealization O)
    (σ : G →* (ℝ ≃o ℝ)) (y : ℝ)

/-- A dense target orbit makes the equivariant cut map continuous. -/
theorem continuous_orbitCutMap (he : O.actionCompletion σ y = O)
    (hd : DenseRange (fun g => σ g y)) : Continuous (R.orbitCutMap σ y) := by
  apply (R.orbitCutMap_monotone σ y he).continuous_of_denseRange
  apply hd.mono
  rintro _ ⟨g, rfl⟩
  exact ⟨R.action g R.base, R.orbitCutMap_orbit σ y he g⟩

/-- The cut map onto a dense target orbit is an actual surjective semiconjugacy. -/
theorem surjective_orbitCutMap (he : O.actionCompletion σ y = O)
    (hd : DenseRange (fun g => σ g y)) : Function.Surjective (R.orbitCutMap σ y) := by
  apply (R.continuous_orbitCutMap σ y he hd).surjective
  · apply R.orbitCutMap_tendsto_atTop σ y he
    intro t
    exact hd.exists_mem_open isOpen_Ioi Set.nonempty_Ioi
  · apply R.orbitCutMap_tendsto_atBot σ y he
    intro t
    exact hd.exists_mem_open isOpen_Iio Set.nonempty_Iio

end TightRealization

namespace NoncofinalMinimalAction

/-- A central element fixing a point of a dense orbit acts trivially everywhere. -/
theorem central_eq_one_of_fixed_dense (ρ : G →* (ℝ ≃o ℝ)) (z : G)
    (hz : ∀ g, z * g = g * z) (x : ℝ) (hfix : ρ z x = x)
    (hd : DenseRange (fun g => ρ g x)) : ρ z = 1 := by
  apply OrderIso.ext
  apply hd.equalizer (ρ z).continuous continuous_id
  funext g
  change ρ z (ρ g x) = ρ g x
  rw [← RelIso.mul_apply, ← map_mul, hz, map_mul, RelIso.mul_apply, hfix]

/-- The maximal convex quotient can be realized by a continuous, monotone,
surjective factor of the given tight action. -/
theorem exists_minimal_factor [Countable G] (O : LeftGroupOrder G) (R : TightRealization O)
    (C : Subgroup G) (hC : letI := O.order; Set.OrdConnected (C : Set G)) (hne : C ≠ ⊤)
    (hmax : ∀ S : Subgroup G, (letI := O.order; Set.OrdConnected (S : Set G)) →
      C < S → S = ⊤) (hnormal : ¬ C.Normal) :
    ∃ σ : G →* (ℝ ≃o ℝ), ∃ y : ℝ, ∃ p : ℝ → ℝ,
      Monotone p ∧ Continuous p ∧ Function.Surjective p ∧
      (∀ g t, p (R.action g t) = σ g (p t)) ∧
      p R.base = y ∧ (∀ g, g ∈ C ↔ σ g y = y) ∧
      (∀ t, DenseRange (fun g => σ g t)) ∧
      (∃ f g u v w, NoncofinalCrossings.Crossing (σ f) (σ g) u v w) := by
  obtain ⟨σ, y, hs, hm, hd, hc⟩ := exists_minimal_real_action O C hC hne hmax hnormal
  have he := O.actionCompletion_eq_of_monotone σ y hm
  refine ⟨σ, y, R.orbitCutMap σ y, R.orbitCutMap_monotone σ y he,
    R.continuous_orbitCutMap σ y he (hd y), R.surjective_orbitCutMap σ y he (hd y),
    R.orbitCutMap_equivariant σ y he, ?_, hs, hd, hc⟩
  simpa only [map_one, RelIso.one_apply] using R.orbitCutMap_orbit σ y he 1

end NoncofinalMinimalAction
end FnZPositiveCones
