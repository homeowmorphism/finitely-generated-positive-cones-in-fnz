module

public import FnZPositiveCones.External.PingPongCombinatorics

@[expose] public section

/-! A strict real potential off one gap forces finite boundary connectivity. -/
namespace FnZPositiveCones.PingPong
universe u
variable {I : Type u} [Fintype I]

/-- Every cycle of a finite permutation must contain the exceptional point if
a real function increases strictly at every other step. -/
theorem isCycleOn_of_increase_off_one (p : Equiv.Perm I) (V : I → ℝ) (b : I)
    (hV : ∀ i, i ≠ b → V i < V (p i)) : p.IsCycleOn Set.univ := by
  have hreach (i : I) : p.SameCycle i b := by
    by_contra hn
    have hne (n : ℕ) : (p ^ n) i ≠ b := fun he => hn ⟨n, by simpa only [zpow_natCast] using he⟩
    have hm : StrictMono (fun n : ℕ => V ((p ^ n) i)) := by
      apply strictMono_nat_of_lt_succ
      intro n
      simpa only [pow_succ', Equiv.Perm.mul_apply] using hV ((p ^ n) i) (hne n)
    have hp : 0 < orderOf p := orderOf_pos p
    have hh := hm hp
    simpa only [pow_zero, pow_orderOf_eq_one, Equiv.Perm.one_apply, lt_self_iff_false] using hh
  exact ⟨p.bijOn (by simp), fun i _ j _ => (hreach i).trans (hreach j).symm⟩

/-- The endpoint incidence relation is connected if its next-step permutation
has a strict potential everywhere except at the basepoint gap. -/
theorem gap_connected_of_increase_off_one (circle graph : Equiv.Perm I)
    (V : I → ℝ) (b : I)
    (hV : ∀ i, i ≠ b → V i < V ((graph⁻¹ * circle) i)) :
    ∀ i j, Relation.EqvGen (GapStep circle graph) i j := by
  let p := graph⁻¹ * circle
  have hp := isCycleOn_of_increase_off_one p V b hV
  have hstep (i : I) : GapStep circle graph i (p i) := by
    change circle i = graph (graph⁻¹ (circle i))
    exact (graph.apply_symm_apply _).symm
  intro i j
  obtain ⟨n, hn⟩ := hp.exists_pow_eq' Set.finite_univ (Set.mem_univ i) (Set.mem_univ j)
  rw [← hn]
  clear hn
  induction n with
  | zero => simpa only [pow_zero, Equiv.Perm.one_apply] using (Relation.EqvGen.refl i : Relation.EqvGen (GapStep circle graph) i i)
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply]
    exact Relation.EqvGen.trans _ _ _ ih (Relation.EqvGen.rel _ _ (hstep _))

end FnZPositiveCones.PingPong
