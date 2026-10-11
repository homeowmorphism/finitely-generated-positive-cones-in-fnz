module

public import FnZPositiveCones.Cone.Opposite

@[expose] public section

namespace FnZPositiveCones
universe u
variable {G : Type u} [Group G]

/-- Reversing nonempty products reverses their order and inverts every factor. -/
theorem oppositeSubsemigroup_closure (S : Set G) :
    oppositeSubsemigroup (Subsemigroup.closure S) =
      Subsemigroup.closure (Inv.inv '' S) := by
  apply le_antisymm
  · have hs : Subsemigroup.closure S ≤
        oppositeSubsemigroup (Subsemigroup.closure (Inv.inv '' S)) := by
      apply Subsemigroup.closure_le.mpr
      intro g hg
      exact Subsemigroup.subset_closure ⟨g, hg, rfl⟩
    intro g hg
    have hh := hs hg
    simpa only [mem_oppositeSubsemigroup, inv_inv] using hh
  · apply Subsemigroup.closure_le.mpr
    rintro _ ⟨g, hg, rfl⟩
    change (g⁻¹)⁻¹ ∈ Subsemigroup.closure S
    rw [inv_inv]
    exact Subsemigroup.subset_closure hg

theorem semigroupFG_opposite {P : Subsemigroup G} (hfg : SemigroupFG P) :
    SemigroupFG (oppositeSubsemigroup P) := by
  classical
  obtain ⟨S, hS⟩ := hfg
  refine ⟨S.image Inv.inv, ?_⟩
  rw [Finset.coe_image, ← oppositeSubsemigroup_closure, hS]

end FnZPositiveCones
