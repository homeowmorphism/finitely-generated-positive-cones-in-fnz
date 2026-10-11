module

public import FnZPositiveCones.External.OrderedActionsCompletion

@[expose] public section

/-!
# Orbit comparison and tail perturbations

Completing a nonfree orbit gives a weakly monotone orbit map. Opposite strict
tails therefore give distinct completed orders whenever both orbits are unbounded
above: a common upper bound in the purported shared order tests both tails at once.
This avoids assuming a continuous semiconjugacy for a possibly nonfree orbit.
-/

namespace FnZPositiveCones

universe u
variable {G : Type u} [Group G]

namespace LeftGroupOrder

/-- The non-strict lexicographic formula for completion of an action orbit. -/
theorem actionCompletion_le (O : LeftGroupOrder G) (ρ : G →* (ℝ ≃o ℝ))
    (x : ℝ) (g h : G) :
    (O.actionCompletion ρ x).order.le g h ↔
      ρ g x < ρ h x ∨ (ρ g x = ρ h x ∧ O.order.le g h) := by
  let := O.order
  change toLex (ρ g x, g) ≤ toLex (ρ h x, h) ↔ _
  exact Prod.Lex.le_iff

/-- The actual orbit map is weakly increasing for its completed order. -/
theorem orbit_le_of_actionCompletion_le (O : LeftGroupOrder G) (ρ : G →* (ℝ ≃o ℝ))
    (x : ℝ) {g h : G} (hgh : (O.actionCompletion ρ x).order.le g h) :
    ρ g x ≤ ρ h x := by
  rcases (actionCompletion_le O ρ x g h).mp hgh with hlt | ⟨he, _⟩
  · exact hlt.le
  · exact he.le

/-- Two unbounded orbits with opposite strict tail motion induce different completed orders.
No injectivity or trivial-stabilizer assumption is made about either perturbed orbit. -/
theorem actionCompletions_ne_of_opposite_tail (O : LeftGroupOrder G)
    (ρ σ : G →* (ℝ ≃o ℝ)) (x y p q : ℝ) (a : G)
    (hρ : ∀ r : ℝ, ∃ g : G, r < ρ g x)
    (hσ : ∀ r : ℝ, ∃ g : G, r < σ g y)
    (hpos : ∀ g, p < ρ g x → ρ g x < ρ a (ρ g x))
    (hneg : ∀ g, q < σ g y → σ a (σ g y) < σ g y) :
    O.actionCompletion ρ x ≠ O.actionCompletion σ y := by
  intro he
  let := (O.actionCompletion ρ x).order
  obtain ⟨gρ, hgρ⟩ := hρ p
  obtain ⟨gσ, hgσ⟩ := hσ q
  let g := max gρ gσ
  have hp : p < ρ g x := hgρ.trans_le
    (orbit_le_of_actionCompletion_le O ρ x (le_max_left gρ gσ))
  have hq : q < σ g y := by
    apply hgσ.trans_le
    apply orbit_le_of_actionCompletion_le O σ y
    rw [← he]
    exact le_max_right gρ gσ
  have hlt : (O.actionCompletion ρ x).order.lt g (a * g) := by
    apply (actionCompletion_lt O ρ x g (a * g)).mpr
    exact Or.inl (by simpa only [map_mul, RelIso.mul_apply] using hpos g hp)
  have hgt : (O.actionCompletion σ y).order.lt (a * g) g := by
    apply (actionCompletion_lt O σ y (a * g) g).mpr
    exact Or.inl (by simpa only [map_mul, RelIso.mul_apply] using hneg g hq)
  rw [← he] at hgt
  exact (lt_asymm hlt hgt)

/-- At least one of the two concrete perturbations changes the original order. -/
theorem actionCompletion_ne_original_of_opposite_tail (O : LeftGroupOrder G)
    (ρ σ : G →* (ℝ ≃o ℝ)) (x y p q : ℝ) (a : G)
    (hρ : ∀ r : ℝ, ∃ g : G, r < ρ g x)
    (hσ : ∀ r : ℝ, ∃ g : G, r < σ g y)
    (hpos : ∀ g, p < ρ g x → ρ g x < ρ a (ρ g x))
    (hneg : ∀ g, q < σ g y → σ a (σ g y) < σ g y) :
    O.actionCompletion ρ x ≠ O ∨ O.actionCompletion σ y ≠ O := by
  by_contra h
  push Not at h
  exact actionCompletions_ne_of_opposite_tail O ρ σ x y p q a hρ hσ hpos hneg
    (h.1.trans h.2.symm)

end LeftGroupOrder

namespace TightRealization

variable {O : LeftGroupOrder G} (R : TightRealization O)
  (σ : G →* (ℝ ≃o ℝ)) (y : ℝ)

/-- Images of orbit points lying to the left of a specified cut in the tight realization. -/
def orbitCutImage (t : ℝ) : Set ℝ :=
  {z | ∃ g : G, R.action g R.base ≤ t ∧ z = σ g y}

/-- The weak monotone cut map; continuity is not asserted for a nonfree target orbit. -/
noncomputable def orbitCutMap (t : ℝ) : ℝ := sSup (R.orbitCutImage σ y t)

theorem orbitCutImage_nonempty (t : ℝ) : (R.orbitCutImage σ y t).Nonempty := by
  obtain ⟨g, hg⟩ := R.unbounded_below t
  exact ⟨σ g y, g, hg.le, rfl⟩

theorem target_orbit_monotone (he : O.actionCompletion σ y = O) {g h : G}
    (hgh : R.action g R.base ≤ R.action h R.base) : σ g y ≤ σ h y := by
  apply LeftGroupOrder.orbit_le_of_actionCompletion_le O σ y
  rw [he]
  exact (R.order_iff g h).mpr hgh

theorem orbitCutImage_bddAbove (he : O.actionCompletion σ y = O) (t : ℝ) :
    BddAbove (R.orbitCutImage σ y t) := by
  obtain ⟨h, hh⟩ := R.unbounded_above t
  refine ⟨σ h y, ?_⟩
  rintro _ ⟨g, hg, rfl⟩
  exact R.target_orbit_monotone σ y he (hg.trans hh.le)

theorem orbitCutMap_monotone (he : O.actionCompletion σ y = O) :
    Monotone (R.orbitCutMap σ y) := by
  intro t u htu
  apply csSup_le_csSup (R.orbitCutImage_bddAbove σ y he u) (R.orbitCutImage_nonempty σ y t)
  rintro z ⟨g, hg, hz⟩
  exact ⟨g, hg.trans htu, hz⟩

/-- Every original orbit point is sent to its actual target orbit point, including ties. -/
theorem orbitCutMap_orbit (he : O.actionCompletion σ y = O) (g : G) :
    R.orbitCutMap σ y (R.action g R.base) = σ g y := by
  apply le_antisymm
  · apply csSup_le (R.orbitCutImage_nonempty σ y _)
    rintro _ ⟨h, hh, rfl⟩
    exact R.target_orbit_monotone σ y he hh
  · exact le_csSup (R.orbitCutImage_bddAbove σ y he _) ⟨g, le_rfl, rfl⟩

/-- Group translation transports the whole lower cut by the corresponding target automorphism. -/
theorem orbitCutImage_equivariant (k : G) (t : ℝ) :
    R.orbitCutImage σ y (R.action k t) = (σ k) '' R.orbitCutImage σ y t := by
  ext z
  constructor
  · rintro ⟨g, hg, rfl⟩
    refine ⟨σ (k⁻¹ * g) y, ⟨k⁻¹ * g, ?_, rfl⟩, ?_⟩
    · have hh := (R.action k⁻¹).monotone hg
      have hh' : R.action (k⁻¹ * g) R.base ≤ R.action k⁻¹ (R.action k t) := by
        simpa only [map_mul, RelIso.mul_apply] using hh
      simpa only [map_inv, RelIso.inv_apply_self] using hh' 
    · rw [← RelIso.mul_apply, ← map_mul, mul_inv_cancel_left]
  · rintro ⟨z, ⟨g, hg, rfl⟩, rfl⟩
    refine ⟨k * g, ?_, ?_⟩
    · simpa only [map_mul, RelIso.mul_apply] using (R.action k).monotone hg
    · simp only [map_mul, RelIso.mul_apply]

/-- The cut map intertwines the actions, even when its target orbit has stabilizers. -/
theorem orbitCutMap_equivariant (he : O.actionCompletion σ y = O) (k : G) (t : ℝ) :
    R.orbitCutMap σ y (R.action k t) = σ k (R.orbitCutMap σ y t) := by
  change sSup (R.orbitCutImage σ y (R.action k t)) = σ k (sSup (R.orbitCutImage σ y t))
  rw [orbitCutImage_equivariant]
  exact ((σ k).map_csSup' (R.orbitCutImage_nonempty σ y t)
    (R.orbitCutImage_bddAbove σ y he t)).symm

theorem orbitCutMap_tendsto_atTop (he : O.actionCompletion σ y = O)
    (hunbounded : ∀ r : ℝ, ∃ g : G, r < σ g y) :
    Filter.Tendsto (R.orbitCutMap σ y) Filter.atTop Filter.atTop := by
  apply (R.orbitCutMap_monotone σ y he).tendsto_atTop_atTop
  intro r
  obtain ⟨g, hg⟩ := hunbounded r
  exact ⟨R.action g R.base, by simpa only [R.orbitCutMap_orbit σ y he] using hg.le⟩

theorem orbitCutMap_tendsto_atBot (he : O.actionCompletion σ y = O)
    (hunbounded : ∀ r : ℝ, ∃ g : G, σ g y < r) :
    Filter.Tendsto (R.orbitCutMap σ y) Filter.atBot Filter.atBot := by
  apply (R.orbitCutMap_monotone σ y he).tendsto_atBot_atBot
  intro r
  obtain ⟨g, hg⟩ := hunbounded r
  exact ⟨R.action g R.base, by simpa only [R.orbitCutMap_orbit σ y he] using hg.le⟩

end TightRealization

end FnZPositiveCones
