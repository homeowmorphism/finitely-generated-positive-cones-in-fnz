module

public import FnZPositiveCones.Interfaces

@[expose] public section

/-! Elementary strict positive cones in arbitrary groups (C01–C04). -/

namespace FnZPositiveCones

universe u v

variable {G : Type u} {H : Type v} [Group G] [Group H]
variable {P Q : Subsemigroup G} {g : G}

/-- A positive element is different from the identity. -/
theorem positiveCone_ne_one (hP : IsPositiveCone P) (hg : g ∈ P) : g ≠ 1 := by
  rintro rfl
  exact hP.1 hg

/-- An element and its inverse cannot both be strictly positive. -/
theorem positiveCone_inv_not_mem (hP : IsPositiveCone P) (hg : g ∈ P) : g⁻¹ ∉ P := by
  intro hi
  exact hP.1 (by simpa using P.mul_mem hg hi)

/-- Strict positive cones are maximal among strict positive cones. -/
theorem positiveCone_rigidity (hP : IsPositiveCone P) (hQ : IsPositiveCone Q)
    (hPQ : P ≤ Q) : P = Q := by
  apply le_antisymm hPQ
  intro g hg
  rcases hP.2 g with rfl | hp | hi
  · exact (hQ.1 hg).elim
  · exact hp
  · exact (positiveCone_inv_not_mem hQ hg (hPQ hi)).elim

/-- Restriction along a subgroup inclusion preserves strict positive cones. -/
theorem positiveCone_restrict (K : Subgroup G) (hP : IsPositiveCone P) :
    IsPositiveCone (Subsemigroup.comap K.subtype.toMulHom P) := by
  refine ⟨hP.1, ?_⟩
  intro g
  rcases hP.2 (g : G) with h | h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

/-- Transport a strict positive cone through a group isomorphism. -/
theorem positiveCone_transport (e : G ≃* H) (hP : IsPositiveCone P) :
    IsPositiveCone (Subsemigroup.map e.toMonoidHom.toMulHom P) := by
  constructor
  · rintro ⟨g, hg, he⟩
    exact positiveCone_ne_one hP hg (e.injective (he.trans e.map_one.symm))
  · intro h
    obtain ⟨g, rfl⟩ := e.surjective h
    rcases hP.2 g with rfl | hg | hg
    · exact Or.inl e.map_one
    · exact Or.inr (Or.inl ⟨g, hg, rfl⟩)
    · exact Or.inr (Or.inr ⟨g⁻¹, hg, e.map_inv g⟩)

/-- Transport of finite semigroup generation uses the image of the generators. -/
theorem semigroupFG_transport (e : G ≃* H) (hfg : SemigroupFG P) :
    SemigroupFG (Subsemigroup.map e.toMonoidHom.toMulHom P) := by
  classical
  obtain ⟨S, rfl⟩ := hfg
  refine ⟨S.image e, ?_⟩
  rw [Finset.coe_image, MulHom.map_mclosure]
  rfl

/-- Existence of a finitely generated strict positive cone is invariant under isomorphism. -/
theorem hasFGPositiveCone_transport (e : G ≃* H) (h : HasFGPositiveCone G) :
    HasFGPositiveCone H := by
  classical
  obtain ⟨S, hS⟩ := h
  refine ⟨S.image e, ?_⟩
  rw [Finset.coe_image]
  have h := positiveCone_transport e hS
  rw [MulHom.map_mclosure] at h
  exact h

/-- The cardinal upper bound is preserved when the generators are transported. -/
theorem hasFGPositiveConeWithBound_transport (e : G ≃* H) {m : ℕ}
    (h : HasFGPositiveConeWithBound G m) : HasFGPositiveConeWithBound H m := by
  classical
  obtain ⟨S, hcard, hS⟩ := h
  refine ⟨S.image e, (Finset.card_image_le).trans hcard, ?_⟩
  rw [Finset.coe_image]
  have h := positiveCone_transport e hS
  rw [MulHom.map_mclosure] at h
  exact h

/-- Positive generators determine a finitely generated cone among all positive cones. -/
theorem semigroupFG_finitelyDetermined (hP : IsPositiveCone P) (hfg : SemigroupFG P) :
    FinitelyDetermined P := by
  obtain ⟨S, rfl⟩ := hfg
  refine ⟨S, Subsemigroup.subset_closure, ?_⟩
  intro Q hQ hSQ
  exact (positiveCone_rigidity hP hQ (Subsemigroup.closure_le.mpr hSQ)).symm

/-- The generic finite determination obligation, with no additional hypotheses. -/
theorem finiteGenerationImpliesFiniteDetermination :
    FiniteGenerationImpliesFiniteDeterminationGoal.{u} := by
  intro G _ P hP hfg
  exact semigroupFG_finitelyDetermined hP hfg

end FnZPositiveCones
