module

public import FnZPositiveCones.External.CircularDynamicsSuccessor

@[expose] public section

/-! Actual adjacent orbit gaps and reduced first-letter colors. -/
namespace FnZPositiveCones
namespace CircularDynamics
universe u
variable {ι : Type u} [DecidableEq ι]

/-- If reduced words have distinct first signed letters, inversion of the first
word followed by the second has no cancellation at their join. -/
theorem different_heads_inv_mul_reduced (u v : FreeGroup ι)
    (s t : ι × Bool) (w z : List (ι × Bool))
    (hu : u.toWord = s :: w) (hv : v.toWord = t :: z) (hst : s ≠ t) :
    FreeGroup.IsReduced (FreeGroup.invRev u.toWord ++ v.toWord) := by
  have hi : FreeGroup.IsReduced (FreeGroup.invRev (s :: w)) := by
    simpa only [FreeGroup.toWord_inv, hu] using (FreeGroup.isReduced_toWord (x := u⁻¹))
  have hj : FreeGroup.IsReduced (t :: z) := by
    simpa only [hv] using (FreeGroup.isReduced_toWord (x := v))
  rw [hu, hv, FreeGroup.invRev_cons]
  have hi' : FreeGroup.IsReduced (FreeGroup.invRev w ++ [(s.1, !s.2)]) := by
    simpa [FreeGroup.invRev] using hi
  change FreeGroup.IsReduced ((FreeGroup.invRev w ++ [(s.1, !s.2)]) ++ t :: z)
  rw [List.append_assoc]
  apply List.isChain_append_cons_cons.mpr
  refine ⟨hi', ?_, hj⟩
  change s.1 = t.1 → (!s.2) = t.2
  rcases s with ⟨i, b⟩
  rcases t with ⟨j, c⟩
  intro hij
  change i = j at hij
  subst j
  cases b <;> cases c <;> simp_all

/-- The exact reduced length of the right difference of differently colored
endpoints is the sum of their two lengths. -/
theorem different_heads_norm_inv_mul (u v : FreeGroup ι)
    (s t : ι × Bool) (w z : List (ι × Bool))
    (hu : u.toWord = s :: w) (hv : v.toWord = t :: z) (hst : s ≠ t) :
    FreeGroup.norm (u⁻¹ * v) = FreeGroup.norm u + FreeGroup.norm v := by
  have hr := different_heads_inv_mul_reduced u v s t w z hu hv hst
  simp only [FreeGroup.norm, FreeGroup.toWord_mul, FreeGroup.toWord_inv,
    hr.reduce_eq, List.length_append, FreeGroup.invRev_length]

/-- For a genuine successor gap, distinct initial colors bound both endpoints
by the fixed successor word. No finite-trace adjacency is used here. -/
theorem successor_different_heads_length (u v h : FreeGroup ι)
    (hnext : v = u * h) (s t : ι × Bool) (w z : List (ι × Bool))
    (hu : u.toWord = s :: w) (hv : v.toWord = t :: z) (hst : s ≠ t) :
    FreeGroup.norm u + FreeGroup.norm v = FreeGroup.norm h := by
  have he : u⁻¹ * v = h := by rw [hnext]; group
  rw [← he]
  exact (different_heads_norm_inv_mul u v s t w z hu hv hst).symm

/-- There are only finitely many genuine fixed-successor gaps with different
nonempty first-letter colors. This alone makes no assertion about colors
meeting at a non-orbit limit point. -/
theorem finite_successor_different_heads [Finite ι] (h : FreeGroup ι) :
    Set.Finite {p : FreeGroup ι × FreeGroup ι | p.2 = p.1 * h ∧
      ∃ s t w z, p.1.toWord = s :: w ∧ p.2.toWord = t :: z ∧ s ≠ t} := by
  apply ((finite_freeGroup_norm_ball (ι := ι) (FreeGroup.norm h)).prod
    (finite_freeGroup_norm_ball (ι := ι) (FreeGroup.norm h))).subset
  rintro ⟨u, v⟩ ⟨hnext, s, t, w, z, hu, hv, hst⟩
  have he := successor_different_heads_length u v h hnext s t w z hu hv hst
  constructor
  · change FreeGroup.norm u ≤ FreeGroup.norm h
    omega
  · change FreeGroup.norm v ≤ FreeGroup.norm h
    omega

end CircularDynamics
end FnZPositiveCones
