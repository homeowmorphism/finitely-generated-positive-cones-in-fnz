module

public import FnZPositiveCones.External.OrderedActionsRealization

@[expose] public section

namespace FnZPositiveCones
universe u
variable {G : Type u} [Group G]
namespace LeftGroupOrder

theorem ext_order {O Q : LeftGroupOrder G} (h : O.order = Q.order) : O = Q := by
  cases O
  cases Q
  cases h
  rfl

/-- Order an action orbit and resolve its stabilizer using an existing left order. -/
noncomputable def actionCompletion (O : LeftGroupOrder G) (ρ : G →* (ℝ ≃o ℝ))
    (x : ℝ) : LeftGroupOrder G := by
  letI := O.order
  let f : G → ℝ ×ₗ G := fun g => toLex (ρ g x, g)
  have hf : Function.Injective f := fun g h he => congrArg (fun a => (ofLex a).2) he
  refine ⟨LinearOrder.lift' f hf, ?_⟩
  intro g h k hgh
  change f g ≤ f h at hgh
  change f (k * g) ≤ f (k * h)
  simp only [f, Prod.Lex.le_iff, ofLex_toLex, map_mul] at hgh ⊢
  rcases hgh with hlt | ⟨he, hle⟩
  · exact Or.inl ((ρ k).strictMono hlt)
  · exact Or.inr ⟨congrArg (ρ k) he, O.mul_le_mul_left g h k hle⟩

@[simp] theorem actionCompletion_lt (O : LeftGroupOrder G) (ρ : G →* (ℝ ≃o ℝ))
    (x : ℝ) (g h : G) :
    (O.actionCompletion ρ x).order.lt g h ↔
      ρ g x < ρ h x ∨ (ρ g x = ρ h x ∧ O.order.lt g h) := by
  let := O.order
  change toLex (ρ g x, g) < toLex (ρ h x, h) ↔ _
  exact Prod.Lex.lt_iff

theorem actionCompletion_mem_cone (O : LeftGroupOrder G) (ρ : G →* (ℝ ≃o ℝ))
    (x : ℝ) (g : G) :
    g ∈ (leftOrderCone (O.actionCompletion ρ x)).1 ↔
      x < ρ g x ∨ (x = ρ g x ∧ O.order.lt 1 g) := by
  rw [mem_leftOrderCone, actionCompletion_lt, map_one]
  rfl

/-- If the original orbit realizes the order, the completion recovers it exactly. -/
theorem actionCompletion_eq (O : LeftGroupOrder G) (ρ : G →* (ℝ ≃o ℝ))
    (x : ℝ) (hreal : ∀ g h, O.order.le g h ↔ ρ g x ≤ ρ h x) :
    O.actionCompletion ρ x = O := by
  apply ext_order
  apply LinearOrder.ext_lt
  intro g h
  let := O.order
  rw [actionCompletion_lt]
  have hlt : ρ g x < ρ h x ↔ g < h := by
    rw [lt_iff_not_ge, ← hreal, not_le]
  rw [hlt]
  exact ⟨fun h => h.elim id And.right, Or.inl⟩

/-- Agreement on finitely many original orbit comparisons preserves their cone signs. -/
theorem actionCompletion_signs (O : LeftGroupOrder G) (ρ σ : G →* (ℝ ≃o ℝ))
    (x : ℝ) (hreal : ∀ g h, O.order.le g h ↔ ρ g x ≤ ρ h x)
    (F : Finset G) (hagree : ∀ g ∈ F, σ g x = ρ g x) :
    ∀ g ∈ F, (g ∈ (leftOrderCone (O.actionCompletion σ x)).1 ↔
      g ∈ (leftOrderCone O).1) := by
  intro g hg
  rw [actionCompletion_mem_cone, hagree g hg]
  have hh := congrArg (fun L => g ∈ (leftOrderCone L).1) (O.actionCompletion_eq ρ x hreal)
  rw [actionCompletion_mem_cone] at hh
  exact iff_of_eq hh

end LeftGroupOrder
end FnZPositiveCones
