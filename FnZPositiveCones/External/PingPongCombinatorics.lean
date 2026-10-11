module

public import FnZPositiveCones.External.OddRankObstruction

@[expose] public section

/-!
# Finite component graphs and the boundary calculation for ping-pong

The input to the local component calculation is the cyclic successor of positive
components and the two component bijections induced by a generator and its inverse.
Their endpoint adjacency identity yields the single alternating component cycle;
the single-cycle conclusion is not assumed.
-/

namespace FnZPositiveCones
namespace PingPong

open Equiv

universe u v

/-- The directed bipartite component graph, specified by its outgoing bijections. -/
def componentGraph {A : Type u} {B : Type v} (f : A ≃ B) (g : B ≃ A) : Perm (A ⊕ B) where
  toFun := Sum.elim (fun a => Sum.inr (f a)) (fun b => Sum.inl (g b))
  invFun := Sum.elim (fun a => Sum.inr (g.symm a)) (fun b => Sum.inl (f.symm b))
  left_inv x := by cases x <;> simp
  right_inv x := by cases x <;> simp

@[simp] theorem componentGraph_inl {A : Type u} {B : Type v}
    (f : A ≃ B) (g : B ≃ A) (a : A) : componentGraph f g (Sum.inl a) = Sum.inr (f a) := rfl

@[simp] theorem componentGraph_inr {A : Type u} {B : Type v}
    (f : A ≃ B) (g : B ≃ A) (b : B) : componentGraph f g (Sum.inr b) = Sum.inl (g b) := rfl

theorem componentGraph_no_fixed {A : Type u} {B : Type v}
    (f : A ≃ B) (g : B ≃ A) (x : A ⊕ B) : componentGraph f g x ≠ x := by
  cases x <;> simp

/-- Two consecutive edges follow the actual cyclic successor of positive components. -/
theorem componentGraph_even_iterate {A : Type u} {B : Type v}
    (f : A ≃ B) (g : B ≃ A) (next : Perm A)
    (hadj : ∀ a, g (f a) = next a) (a : A) (m : ℕ) :
    (componentGraph f g ^ (2 * m)) (Sum.inl a) = Sum.inl ((next ^ m) a) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 + 2 * m by omega, pow_add, Perm.mul_apply, ih]
    simp [hadj, pow_succ']

/-- MMRT Proposition 2.8: endpoint adjacency and cyclic component order force
the directed bipartite graph to be one cycle, including one component per side. -/
theorem componentGraph_isCycle {A : Type u} {B : Type v} [Fintype A] [Nonempty A]
    (f : A ≃ B) (g : B ≃ A) (next : Perm A)
    (hnext : next.IsCycleOn Set.univ) (hadj : ∀ a, g (f a) = next a) :
    (componentGraph f g).IsCycle := by
  classical
  let a₀ : A := Classical.choice inferInstance
  have hpositive (a : A) : (componentGraph f g).SameCycle (Sum.inl a₀) (Sum.inl a) := by
    obtain ⟨m, hm⟩ := hnext.exists_pow_eq' Set.finite_univ (Set.mem_univ a₀) (Set.mem_univ a)
    refine ⟨(2 * m : ℕ), ?_⟩
    rw [zpow_natCast, componentGraph_even_iterate f g next hadj, hm]
  refine ⟨Sum.inl a₀, componentGraph_no_fixed f g _, ?_⟩
  intro x _
  cases x with
  | inl a => exact hpositive a
  | inr b =>
    have h := (hpositive (f.symm b)).apply_right
    simpa using h

/-- The component cycle has exactly twice the number of positive components. -/
theorem componentGraph_cycleType {A : Type u} {B : Type v}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] [Nonempty A]
    (f : A ≃ B) (g : B ≃ A) (next : Perm A)
    (hnext : next.IsCycleOn Set.univ) (hadj : ∀ a, g (f a) = next a) :
    (componentGraph f g).cycleType = {2 * Fintype.card A} := by
  rw [(componentGraph_isCycle f g next hnext hadj).cycleType,
    MMRTParity.support_eq_univ_of_no_fixed _ (componentGraph_no_fixed f g), Finset.card_univ,
    Fintype.card_sum, ← Fintype.card_congr f]
  congr 1
  omega

section FiberCycles

variable {I : Type u} {A : I → Type v} [DecidableEq I]

/-- Extend a component permutation by the identity on all other generator fibers. -/
noncomputable def fiberPerm (p : ∀ i, Perm (A i)) (i : I) : Perm (Sigma A) :=
  (p i).extendDomain (Equiv.sigmaSubtype i).symm

@[simp] theorem fiberPerm_same (p : ∀ i, Perm (A i)) (i : I) (a : A i) :
    fiberPerm p i ⟨i, a⟩ = ⟨i, p i a⟩ := by
  simpa [fiberPerm, Equiv.sigmaSubtype] using
    (p i).extendDomain_apply_image (Equiv.sigmaSubtype i).symm a

theorem fiberPerm_other (p : ∀ i, Perm (A i)) {i j : I} (hji : j ≠ i) (a : A j) :
    fiberPerm p i ⟨j, a⟩ = ⟨j, a⟩ :=
  (p i).extendDomain_apply_not_subtype (Equiv.sigmaSubtype i).symm hji

theorem fiberPerm_disjoint (p : ∀ i, Perm (A i)) :
    Pairwise (fun i j => Perm.Disjoint (fiberPerm p i) (fiberPerm p j)) := by
  intro i j hij ⟨k, a⟩
  by_cases hki : k = i
  · subst k
    exact Or.inr (fiberPerm_other p hij a)
  · exact Or.inl (fiberPerm_other p hki a)

/-- A product of disjoint fiber permutations acts once in the specified fiber. -/
theorem fiberPerm_product_apply (p : ∀ i, Perm (A i)) (s : Finset I)
    (hcomm : (s : Set I).Pairwise (fun i j => Commute (fiberPerm p i) (fiberPerm p j)))
    (i : I) (a : A i) :
    s.noncommProd (fiberPerm p) hcomm ⟨i, a⟩ =
      if i ∈ s then ⟨i, p i a⟩ else ⟨i, a⟩ := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hjs ih =>
    rw [Finset.noncommProd_insert_of_notMem _ _ _ _ hjs, Perm.mul_apply]
    rw [ih]
    by_cases hij : i = j
    · subst j
      simp [hjs]
    · by_cases his : i ∈ s <;> simp [his, hij, fiberPerm_other p hij]

/-- The disjoint product is exactly the explicitly fiberwise permutation. -/
theorem fiberPerm_product [Fintype I] (p : ∀ i, Perm (A i)) :
    Finset.univ.noncommProd (fiberPerm p)
        (fun _i _ _j _ hij => (fiberPerm_disjoint p hij).commute) =
      Equiv.Perm.sigmaCongrRight p := by
  apply Equiv.ext
  rintro ⟨i, a⟩
  exact (fiberPerm_product_apply p Finset.univ _ i a).trans (by simp)

/-- Cycle types add over disjoint fibers; this counts the constructed polygon rotations. -/
theorem cycleType_sigmaCongrRight [Fintype I] [∀ i, Fintype (A i)]
    [∀ i, DecidableEq (A i)] (p : ∀ i, Perm (A i)) :
    (Equiv.Perm.sigmaCongrRight p).cycleType = ∑ i, (p i).cycleType := by
  rw [← fiberPerm_product p]
  rw [Perm.Disjoint.cycleType_noncommProd
    (fun i _ j _ hij => fiberPerm_disjoint p hij)]
  apply Finset.sum_congr rfl
  intro i _
  exact Perm.cycleType_extendDomain (Equiv.sigmaSubtype i).symm

end FiberCycles

section SumCycles

variable {A : Type u} {B : Type v} [Fintype A] [Fintype B]
  [DecidableEq A] [DecidableEq B]

/-- Cycle types add under the disjoint union of two permutation domains. -/
theorem cycleType_sumCongr (p : Perm A) (q : Perm B) :
    Equiv.Perm.cycleType (Equiv.sumCongr p q) = p.cycleType + q.cycleType := by
  classical
  have hl : Equiv.sumCongr p (1 : Perm B) =
      p.extendDomain (Equiv.Set.rangeInl A B).symm := by
    apply Equiv.ext
    intro x
    cases x with
    | inl a => exact (p.extendDomain_apply_image (Equiv.Set.rangeInl A B).symm a).symm
    | inr b =>
      exact (p.extendDomain_apply_not_subtype (Equiv.Set.rangeInl A B).symm
        (by simp)).symm
  have hr : Equiv.sumCongr (1 : Perm A) q =
      q.extendDomain (Equiv.Set.rangeInr A B).symm := by
    apply Equiv.ext
    intro x
    cases x with
    | inl a =>
      exact (q.extendDomain_apply_not_subtype (Equiv.Set.rangeInr A B).symm
        (by simp)).symm
    | inr b => exact (q.extendDomain_apply_image (Equiv.Set.rangeInr A B).symm b).symm
  have hd : Perm.Disjoint (Equiv.sumCongr p (1 : Perm B)) (Equiv.sumCongr (1 : Perm A) q) := by
    intro x
    cases x <;> simp
  have he : Equiv.sumCongr p q =
      Equiv.sumCongr p (1 : Perm B) * Equiv.sumCongr (1 : Perm A) q := by
    apply Equiv.ext
    intro x
    cases x <;> rfl
  rw [he, hd.cycleType_mul, hl, hr, Perm.cycleType_extendDomain, Perm.cycleType_extendDomain]

end SumCycles

section Boundary

variable {C : Type u}

/-- Two copies of each glued component: its incidence at the base disc and at a polygon. -/
abbrev Dart (C : Type u) := C ⊕ C

/-- Orient the polygon discs oppositely to the base disc along their glued intervals. -/
def discRotation (circle graph : Perm C) : Perm (Dart C) :=
  Equiv.sumCongr circle graph⁻¹

/-- Each glued interval pairs its incidence on the base disc with its polygon incidence. -/
def gluingPairing (C : Type u) : Perm (Dart C) := Equiv.sumComm C C

/-- Boundary traversal in the actual constructed combinatorial map. -/
def boundary (circle graph : Perm C) : Perm (Dart C) :=
  discRotation circle graph * gluingPairing C

@[simp] theorem boundary_inl (circle graph : Perm C) (c : C) :
    boundary circle graph (Sum.inl c) = Sum.inr (graph⁻¹ c) := rfl

@[simp] theorem boundary_inr (circle graph : Perm C) (c : C) :
    boundary circle graph (Sum.inr c) = Sum.inl (circle c) := rfl

theorem gluingPairing_square (C : Type u) : gluingPairing C ^ 2 = 1 := by
  apply Equiv.ext
  intro d
  cases d <;> rfl

theorem gluingPairing_no_fixed (d : Dart C) : gluingPairing C d ≠ d := by
  cases d <;> simp [gluingPairing]

theorem boundary_no_fixed (circle graph : Perm C) (d : Dart C) :
    boundary circle graph d ≠ d := by
  cases d <;> simp

/-- Two base gaps are joined when the next base component is the next polygon component.
This is the endpoint incidence relation, before taking its equivalence closure. -/
def GapStep (circle graph : Perm C) (c d : C) : Prop := circle c = graph d

/-- A dart lies on the gap immediately before its base-disc incidence. -/
def gapOfDart (circle : Perm C) : Dart C → C :=
  Sum.elim (fun c => circle⁻¹ c) id

/-- Every boundary step either stays in a base gap or crosses one polygon edge. -/
theorem gapOfDart_step (circle graph : Perm C) (d : Dart C) :
    Relation.EqvGen (GapStep circle graph)
      (gapOfDart circle d) (gapOfDart circle (boundary circle graph d)) := by
  cases d with
  | inl c =>
    apply Relation.EqvGen.rel
    change circle (circle⁻¹ c) = graph (graph⁻¹ c)
    simp
  | inr c =>
    change Relation.EqvGen (GapStep circle graph) c (circle⁻¹ (circle c))
    simpa using Relation.EqvGen.refl (r := GapStep circle graph) c

/-- A boundary walk yields a path in the endpoint incidence relation. -/
theorem gapOfDart_iterate (circle graph : Perm C) (d : Dart C) (m : ℕ) :
    Relation.EqvGen (GapStep circle graph)
      (gapOfDart circle d) (gapOfDart circle ((boundary circle graph ^ m) d)) := by
  induction m with
  | zero => exact Relation.EqvGen.refl _
  | succ m ih =>
    rw [pow_succ', Perm.mul_apply]
    exact Relation.EqvGen.trans _ _ _ ih (gapOfDart_step circle graph _)

/-- Every endpoint incidence edge is realized by two steps along the constructed boundary. -/
theorem sameCycle_of_gapStep (circle graph : Perm C) {c d : C}
    (h : GapStep circle graph c d) :
    (boundary circle graph).SameCycle (Sum.inr c) (Sum.inr d) := by
  refine ⟨2, ?_⟩
  change boundary circle graph (boundary circle graph (Sum.inr c)) = Sum.inr d
  rw [boundary_inr, boundary_inl, show circle c = graph d from h]
  simp

/-- Generated gap equivalence implies equality of boundary cycles. -/
theorem sameCycle_of_gapEqv (circle graph : Perm C) {c d : C}
    (h : Relation.EqvGen (GapStep circle graph) c d) :
    (boundary circle graph).SameCycle (Sum.inr c) (Sum.inr d) := by
  induction h with
  | rel c d h => exact sameCycle_of_gapStep circle graph h
  | refl c => exact Perm.SameCycle.rfl
  | symm c d _ ih => exact ih.symm
  | trans c d e _ _ hcd hde => exact hcd.trans hde

/-- Every dart lies in the boundary cycle of the base gap assigned to it. -/
theorem sameCycle_gapOfDart (circle graph : Perm C) (d : Dart C) :
    (boundary circle graph).SameCycle (Sum.inr (gapOfDart circle d)) d := by
  cases d with
  | inl c =>
    have h : (boundary circle graph).SameCycle
        (Sum.inr (circle⁻¹ c)) (boundary circle graph (Sum.inr (circle⁻¹ c))) :=
      Perm.SameCycle.rfl.apply_right
    simpa [gapOfDart] using h
  | inr c => exact Perm.SameCycle.rfl

/-- Boundary cycles coincide exactly with equivalence classes of the endpoint gap relation. -/
theorem sameCycle_boundary_iff_gapEqv [Finite C] (circle graph : Perm C) (d e : Dart C) :
    (boundary circle graph).SameCycle d e ↔
      Relation.EqvGen (GapStep circle graph) (gapOfDart circle d) (gapOfDart circle e) := by
  constructor
  · intro h
    obtain ⟨m, rfl⟩ := h.exists_nat_pow_eq
    exact gapOfDart_iterate circle graph d m
  · intro h
    exact (sameCycle_gapOfDart circle graph d).symm.trans
      ((sameCycle_of_gapEqv circle graph h).trans (sameCycle_gapOfDart circle graph e))

/-- One gap equivalence class forces the constructed boundary to be a single full cycle. -/
theorem boundary_isCycle_of_gap_connected [Nonempty C] (circle graph : Perm C)
    (hgap : ∀ c d, Relation.EqvGen (GapStep circle graph) c d) :
    (boundary circle graph).IsCycle := by
  classical
  let c₀ : C := Classical.choice inferInstance
  refine ⟨Sum.inr c₀, boundary_no_fixed circle graph _, ?_⟩
  intro d _
  exact (sameCycle_of_gapEqv circle graph (hgap c₀ (gapOfDart circle d))).trans
    (sameCycle_gapOfDart circle graph d)

end Boundary

section Configuration

variable {I : Type u} {A B : I → Type v}

/-- All positive and negative domain components, retaining their generator labels. -/
abbrev Component (A B : I → Type v) := Σ i, A i ⊕ B i

/-- Each polygon follows the directed bipartite graph belonging to its generator. -/
def polygonGraph (f : ∀ i, A i ≃ B i) (g : ∀ i, B i ≃ A i) :
    Perm (Component A B) :=
  Equiv.Perm.sigmaCongrRight (fun i => componentGraph (f i) (g i))

theorem polygonGraph_no_fixed (f : ∀ i, A i ≃ B i) (g : ∀ i, B i ≃ A i)
    (c : Component A B) : polygonGraph f g c ≠ c := by
  rcases c with ⟨i, a | b⟩ <;> simp [polygonGraph, Equiv.Perm.sigmaCongrRight]

variable [Fintype I] [DecidableEq I]
  [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]
  [∀ i, DecidableEq (A i)] [∀ i, DecidableEq (B i)]
  [∀ i, Nonempty (A i)]

/-- The number of polygon discs is derived from the local component-order identity. -/
theorem polygonGraph_cycleType (f : ∀ i, A i ≃ B i) (g : ∀ i, B i ≃ A i)
    (next : ∀ i, Perm (A i)) (hnext : ∀ i, (next i).IsCycleOn Set.univ)
    (hadj : ∀ i a, g i (f i a) = next i a) :
    (polygonGraph f g).cycleType = ∑ i, {2 * Fintype.card (A i)} := by
  rw [polygonGraph, cycleType_sigmaCongrRight]
  apply Finset.sum_congr rfl
  intro i _
  exact componentGraph_cycleType (f i) (g i) (next i) (hnext i) (hadj i)

theorem polygonGraph_cycleCount (f : ∀ i, A i ≃ B i) (g : ∀ i, B i ≃ A i)
    (next : ∀ i, Perm (A i)) (hnext : ∀ i, (next i).IsCycleOn Set.univ)
    (hadj : ∀ i a, g i (f i a) = next i a) :
    (polygonGraph f g).cycleType.card = Fintype.card I := by
  rw [polygonGraph_cycleType f g next hnext hadj]
  simp

omit [DecidableEq I] [∀ i, DecidableEq (A i)] [∀ i, DecidableEq (B i)]
  [∀ i, Nonempty (A i)] in
/-- Every paired positive/negative component contributes two glued intervals. -/
theorem component_card (f : ∀ i, A i ≃ B i) :
    Fintype.card (Component A B) = 2 * ∑ i, Fintype.card (A i) := by
  simp only [Component, Fintype.card_sigma, Fintype.card_sum]
  simp_rw [← Fintype.card_congr (f _)]
  rw [Finset.sum_add_distrib, two_mul]

omit [DecidableEq I] [∀ i, DecidableEq (A i)] [∀ i, DecidableEq (B i)]
  [∀ i, Nonempty (A i)] in
/-- Each glued interval has one incidence on the base disc and one on a polygon. -/
theorem dart_card (f : ∀ i, A i ≃ B i) :
    Fintype.card (Dart (Component A B)) = 4 * ∑ i, Fintype.card (A i) := by
  rw [Fintype.card_sum, component_card f]
  omega

variable [Nonempty I] [∀ i, Nonempty (B i)]

omit [Fintype I] [DecidableEq I] [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]
  [∀ i, DecidableEq (A i)] [∀ i, DecidableEq (B i)] [∀ i, Nonempty (B i)] in
instance component_nonempty : Nonempty (Component A B) := by
  let i : I := Classical.choice inferInstance
  exact ⟨⟨i, Sum.inl (Classical.choice inferInstance)⟩⟩

omit [Fintype I] [DecidableEq I] [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]
  [∀ i, DecidableEq (A i)] [∀ i, DecidableEq (B i)] in
/-- The cyclic order on all domain components is a nontrivial base-disc rotation. -/
theorem componentCircle_no_fixed (circle : Perm (Component A B))
    (hcircle : circle.IsCycleOn Set.univ) (c : Component A B) : circle c ≠ c := by
  apply hcircle.apply_ne _ (Set.mem_univ c)
  let i : I := Classical.choice inferInstance
  let a : A i := Classical.choice inferInstance
  let b : B i := Classical.choice inferInstance
  exact ⟨⟨i, Sum.inl a⟩, Set.mem_univ _, ⟨i, Sum.inr b⟩, Set.mem_univ _, by simp⟩

omit [Fintype I] [DecidableEq I] [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]
  [∀ i, DecidableEq (A i)] [∀ i, DecidableEq (B i)] in
theorem componentCircle_isCycle (circle : Perm (Component A B))
    (hcircle : circle.IsCycleOn Set.univ) : circle.IsCycle := by
  let c : Component A B := Classical.choice inferInstance
  exact ⟨c, componentCircle_no_fixed circle hcircle c, fun {_} _ =>
    hcircle.2 (Set.mem_univ _) (Set.mem_univ _)⟩

omit [Fintype I] [DecidableEq I] [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]
  [∀ i, DecidableEq (A i)] [∀ i, DecidableEq (B i)] in
/-- The constructed disc rotation has no uncounted fixed discs. -/
theorem discRotation_no_fixed (f : ∀ i, A i ≃ B i) (g : ∀ i, B i ≃ A i)
    (circle : Perm (Component A B)) (hcircle : circle.IsCycleOn Set.univ)
    (d : Dart (Component A B)) : discRotation circle (polygonGraph f g) d ≠ d := by
  cases d with
  | inl c =>
    simpa [discRotation] using componentCircle_no_fixed circle hcircle c
  | inr c =>
    intro h
    have h' := congrArg (polygonGraph f g) (Sum.inr.inj h)
    have h'' : c = polygonGraph f g c := by simpa [discRotation] using h'
    exact polygonGraph_no_fixed f g c h''.symm

/-- One base disc and the locally constructed polygon discs give precisely `|I|+1` cycles. -/
theorem discRotation_cycleCount (f : ∀ i, A i ≃ B i) (g : ∀ i, B i ≃ A i)
    (next : ∀ i, Perm (A i)) (hnext : ∀ i, (next i).IsCycleOn Set.univ)
    (hadj : ∀ i a, g i (f i a) = next i a)
    (circle : Perm (Component A B)) (hcircle : circle.IsCycleOn Set.univ) :
    (discRotation circle (polygonGraph f g)).cycleType.card = Fintype.card I + 1 := by
  rw [discRotation, cycleType_sumCongr, Multiset.card_add, Perm.cycleType_inv,
    (componentCircle_isCycle circle hcircle).cycleType,
    Multiset.card_singleton, polygonGraph_cycleCount f g next hnext hadj]
  omega

/-- MMRT's parity obstruction from finite cyclic component data.

The boundary, its free edge pairing, the total dart count, and the number of
rotation cycles are all constructed and proved above. The input connectivity
is the equivalence relation on base gaps generated by polygon endpoint incidence;
it is not an assumption that the resulting boundary permutation is one cycle.
Geometric ping-pong data must still establish this incidence relation's agreement
with its principal-gap orbit relation.
-/
theorem even_of_connected_component_configuration
    (f : ∀ i, A i ≃ B i) (g : ∀ i, B i ≃ A i)
    (next : ∀ i, Perm (A i)) (hnext : ∀ i, (next i).IsCycleOn Set.univ)
    (hadj : ∀ i a, g i (f i a) = next i a)
    (circle : Perm (Component A B)) (hcircle : circle.IsCycleOn Set.univ)
    (hgap : ∀ c d, Relation.EqvGen (GapStep circle (polygonGraph f g)) c d) :
    Even (Fintype.card I) := by
  exact MMRTParity.even_of_one_boundary (Fintype.card I)
    (∑ i, Fintype.card (A i)) (discRotation circle (polygonGraph f g))
    (gluingPairing (Component A B)) (dart_card f)
    (discRotation_no_fixed f g circle hcircle)
    (discRotation_cycleCount f g next hnext hadj circle hcircle)
    (gluingPairing_square _) gluingPairing_no_fixed
    (boundary_isCycle_of_gap_connected circle (polygonGraph f g) hgap)
    (boundary_no_fixed circle (polygonGraph f g))

end Configuration

end PingPong
end FnZPositiveCones
