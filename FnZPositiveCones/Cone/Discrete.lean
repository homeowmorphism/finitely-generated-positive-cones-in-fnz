module

public import FnZPositiveCones.Cone.Topology

@[expose] public section

namespace FnZPositiveCones
universe u
variable {G : Type u} [Group G]

/-- A finitely generated strict cone in a nontrivial group has a least positive element. -/
theorem semigroupFG_has_least_positive [Nontrivial G] (P : PositiveCone G)
    (hfg : SemigroupFG P.1) :
    ∃ a : G, a ∈ P.1 ∧ ∀ g ∈ P.1, (coneLeftOrder P).order.le a g := by
  classical
  let := (coneLeftOrder P).order
  obtain ⟨S, hS⟩ := hfg
  have hp : ∃ g, g ∈ P.1 := by
    obtain ⟨g, hg⟩ := exists_ne (1 : G)
    rcases P.2.2 g with he | h | h
    · exact (hg he).elim
    · exact ⟨g, h⟩
    · exact ⟨g⁻¹, h⟩
  have hne : S.Nonempty := by
    by_contra h
    have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    obtain ⟨g, hg⟩ := hp
    rw [← hS, he] at hg
    simp only [Finset.coe_empty, Subsemigroup.closure_empty] at hg
    exact hg
  let a := S.min' hne
  have ha : a ∈ S := Finset.min'_mem S hne
  have hSP : ∀ s ∈ S, s ∈ P.1 := fun s hs => by
    rw [← hS]
    exact Subsemigroup.subset_closure hs
  refine ⟨a, hSP a ha, ?_⟩
  intro g hg
  rw [← hS] at hg
  induction hg using Subsemigroup.closure_induction with
  | mem x hx => exact Finset.min'_le S x hx
  | mul x y hx hy ihx ihy =>
      have hpy : y ∈ P.1 := by rwa [hS] at hy
      have hpos : (1 : G) < y := by simpa only [coneLeftOrder_lt, inv_one, one_mul] using hpy
      exact ihx.trans (by simpa only [mul_one] using
        ((coneLeftOrder P).mul_lt_mul_left x hpos).le)

/-- Positivity and the exact least-positive comparison, without commutative order assumptions. -/
def LeftGroupOrder.IsLeastPositive (O : LeftGroupOrder G) (a : G) : Prop :=
  O.order.lt 1 a ∧ ∀ g : G, O.order.lt 1 g → O.order.le a g

theorem semigroupFG_isLeastPositive [Nontrivial G] (P : PositiveCone G)
    (hfg : SemigroupFG P.1) : ∃ a : G, (coneLeftOrder P).IsLeastPositive a := by
  obtain ⟨a, ha, hleast⟩ := semigroupFG_has_least_positive P hfg
  refine ⟨a, ?_, ?_⟩
  · simpa only [coneLeftOrder_lt, inv_one, one_mul] using ha
  · intro g hg
    exact hleast g (by simpa only [coneLeftOrder_lt, inv_one, one_mul] using hg)

/-- Every adjacent pair is a left translate of the same least-positive step. -/
theorem LeftGroupOrder.covBy_iff_of_isLeastPositive (O : LeftGroupOrder G) {a : G}
    (ha : O.IsLeastPositive a) (g h : G) :
    letI := O.order; g ⋖ h ↔ h = g * a := by
  let := O.order
  have hga : g < g * a := by simpa only [mul_one] using O.mul_lt_mul_left g ha.1
  have hbound {b : G} (hgb : g < b) : g * a ≤ b := by
    have hb := ha.2 (g⁻¹ * b) ((O.lt_iff_one_lt g b).mp hgb)
    simpa only [mul_inv_cancel_left] using O.mul_le_mul_left _ _ g hb
  constructor
  · intro hcov
    rcases hcov.eq_or_eq hga.le (hbound hcov.lt) with he | he
    · exact (hga.ne he.symm).elim
    · exact he.symm
  · rintro rfl
    refine ⟨hga, ?_⟩
    intro b hgb hba
    exact not_lt_of_ge (hbound hgb) hba

end FnZPositiveCones
