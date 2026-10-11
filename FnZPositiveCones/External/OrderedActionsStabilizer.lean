module

public import FnZPositiveCones.External.OrderedActionsCompletion
public import FnZPositiveCones.Cone.Opposite

@[expose] public section

/-! A nontrivial orbit stabilizer allows two different completions of the same action. -/

namespace FnZPositiveCones.LeftGroupOrder

universe u
variable {G : Type u} [Group G]

/-- Reversing the order used on the orbit stabilizer changes the completed
order whenever that stabilizer contains a nonidentity element. -/
theorem actionCompletions_ne_of_nontrivial_stabilizer
    (O : LeftGroupOrder G) (ρ : G →* (ℝ ≃o ℝ)) (x : ℝ)
    (k : G) (hk : k ≠ 1) (hfix : ρ k x = x) :
    O.actionCompletion ρ x ≠
      (coneLeftOrder (leftOrderCone O).opposite).actionCompletion ρ x := by
  intro he
  have htest := iff_of_eq (congrArg (fun Q : LeftGroupOrder G => Q.order.lt 1 k) he)
  have hsign : k ∈ (leftOrderCone O).1 ↔ k⁻¹ ∈ (leftOrderCone O).1 := by
    simpa only [actionCompletion_lt, map_one, RelIso.one_apply, hfix,
      lt_self_iff_false, true_and, false_or, coneLeftOrder_lt, inv_one, one_mul,
      PositiveCone.mem_opposite, mem_leftOrderCone] using htest
  rcases (leftOrderCone O).mem_or_mem_opposite hk with hpos | hneg
  · exact positiveCone_inv_not_mem (leftOrderCone O).2 hpos (hsign.mp hpos)
  · exact positiveCone_inv_not_mem (leftOrderCone O).2 (hsign.mpr hneg) hneg

/-- Strict motion at the basepoint is positive in every completion, regardless
of the order selected to resolve the orbit stabilizer. -/
theorem mem_actionCompletion_of_strict_motion
    (T : LeftGroupOrder G) (σ : G →* (ℝ ≃o ℝ)) (x : ℝ) {g : G}
    (hg : x < σ g x) : g ∈ (leftOrderCone (T.actionCompletion σ x)).1 :=
  (actionCompletion_mem_cone T σ x g).mpr (Or.inl hg)

/-- If every finite collection of original orbit values can be preserved by
an action with a nontrivial basepoint stabilizer, the original order is not
isolated. No finite semigroup generation hypothesis is used. -/
theorem not_isolated_of_finite_trace_stabilizers
    (O : LeftGroupOrder G) (ρ : G →* (ℝ ≃o ℝ)) (x : ℝ)
    (hreal : ∀ g h, O.order.le g h ↔ ρ g x ≤ ρ h x)
    (hpert : ∀ F : Finset G, ∃ σ : G →* (ℝ ≃o ℝ),
      (∀ g ∈ F, σ g x = ρ g x) ∧ ∃ k, k ≠ 1 ∧ σ k x = x) :
    ¬ IsOpen ({O} : Set (LeftGroupOrder G)) := by
  intro hiso
  have hfd : FinitelyDetermined (leftOrderCone O).1 :=
    (finiteDetermination_iff_leftOrder_isolated (leftOrderCone O)).mpr (by simpa using hiso)
  obtain ⟨F, hFP, hdet⟩ := hfd
  obtain ⟨σ, hagree, k, hk, hfix⟩ := hpert F
  have hpositive : ∀ g ∈ F, x < σ g x := by
    intro g hg
    rw [hagree g hg]
    have hgt : O.order.lt 1 g := hFP hg
    let := O.order
    have hnot : ¬ ρ g x ≤ ρ 1 x :=
      fun h => (not_le_of_gt hgt) ((hreal g 1).mpr h)
    simpa only [map_one, RelIso.one_apply] using lt_of_not_ge hnot
  have heq (T : LeftGroupOrder G) : T.actionCompletion σ x = O := by
    have hcone : leftOrderCone (T.actionCompletion σ x) = leftOrderCone O := by
      apply Subtype.ext
      apply hdet _ (leftOrderCone (T.actionCompletion σ x)).2
      exact fun g hg => mem_actionCompletion_of_strict_motion T σ x (hpositive g hg)
    simpa only [coneLeftOrder_leftOrderCone] using congrArg coneLeftOrder hcone
  exact actionCompletions_ne_of_nontrivial_stabilizer O σ x k hk hfix
    ((heq O).trans (heq (coneLeftOrder (leftOrderCone O).opposite)).symm)

end FnZPositiveCones.LeftGroupOrder
