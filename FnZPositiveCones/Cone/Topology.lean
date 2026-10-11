module

public import FnZPositiveCones.Cone.Basic

@[expose] public section

/-! The topology of signs on strict positive cones, and its left-order interpretation (C05). -/

namespace FnZPositiveCones

universe u

/-- The space of strict positive cones on a group. -/
def PositiveCone (G : Type u) [Group G] := {P : Subsemigroup G // IsPositiveCone P}

variable {G : Type u} [Group G]

/-- Boolean signs use the discrete topology on `Bool`. -/
noncomputable def coneSign (P : PositiveCone G) (g : G) : Bool := by
  classical
  exact decide (g ∈ P.1)

/-- The cone topology is induced from the product of discrete sign coordinates. -/
noncomputable instance : TopologicalSpace (PositiveCone G) :=
  TopologicalSpace.induced coneSign inferInstance

@[simp] theorem coneSign_eq_true (P : PositiveCone G) (g : G) :
    coneSign P g = true ↔ g ∈ P.1 := by
  classical
  simp [coneSign]

/-- A finite set of positive signs specifies an open set of cones. -/
theorem isOpen_positiveCylinder (S : Finset G) :
    IsOpen {Q : PositiveCone G | (S : Set G) ⊆ (Q.1 : Set G)} := by
  classical
  apply isOpen_induced_iff.mpr
  refine ⟨(S : Set G).pi (fun _ => ({true} : Set Bool)), ?_, ?_⟩
  · exact isOpen_set_pi S.finite_toSet (fun _ _ => isOpen_discrete _)
  · ext Q
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_singleton_iff, coneSign_eq_true,
      Set.mem_ofPred_eq, Set.subset_def, SetLike.mem_coe]

/-- Finite determination is exactly isolation in the actual product sign topology. -/
theorem finiteDetermination_iff_isolated (P : PositiveCone G) :
    FinitelyDetermined P.1 ↔ IsOpen ({P} : Set (PositiveCone G)) := by
  classical
  constructor
  · rintro ⟨S, hSP, hS⟩
    have hc : {Q : PositiveCone G | (S : Set G) ⊆ (Q.1 : Set G)} = {P} := by
      ext Q
      constructor
      · intro hQ
        exact Set.mem_singleton_iff.mpr (Subtype.ext (hS Q.1 Q.2 hQ))
      · rintro rfl
        exact hSP
    rw [← hc]
    exact isOpen_positiveCylinder S
  · intro hi
    obtain ⟨U, hU, hpre⟩ := isOpen_induced_iff.mp hi
    have hPU : coneSign P ∈ U := by
      have : P ∈ coneSign ⁻¹' U := by rw [hpre]; exact Set.mem_singleton P
      exact this
    obtain ⟨I, V, hV, hsub⟩ := isOpen_pi_iff.mp hU (coneSign P) hPU
    let S : Finset G := I.filter (fun g => g ∈ P.1) ∪
      (I.filter (fun g => g ≠ 1 ∧ g ∉ P.1)).image (fun g => g⁻¹)
    have hSP : (S : Set G) ⊆ (P.1 : Set G) := by
      intro g hg
      rcases Finset.mem_union.mp hg with hg | hg
      · exact (Finset.mem_filter.mp hg).2
      · obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hg
        obtain ⟨_, hne, hneg⟩ := Finset.mem_filter.mp hh
        exact ((P.2.2 h).resolve_left hne).resolve_left hneg
    refine ⟨S, hSP, ?_⟩
    intro Q hQ hSQ
    let R : PositiveCone G := ⟨Q, hQ⟩
    have heq : ∀ g ∈ I, coneSign R g = coneSign P g := by
      intro g hg
      by_cases hp : g ∈ P.1
      · have hq : g ∈ Q := hSQ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hg, hp⟩))
        simp [coneSign, hp, hq, R]
      · by_cases hne : g = 1
        · subst g
          simp [coneSign, R, P.2.1, hQ.1]
        · have hqi : g⁻¹ ∈ Q := hSQ (Finset.mem_union_right _
            (Finset.mem_image.mpr ⟨g, Finset.mem_filter.mpr ⟨hg, hne, hp⟩, rfl⟩))
          have hq : g ∉ Q := fun h => positiveCone_inv_not_mem hQ h hqi
          simp [coneSign, hp, hq, R]
    have hRU : coneSign R ∈ U := hsub (fun g hg => (heq g hg) ▸ (hV g hg).2)
    have hRP : R = P := by
      apply Set.mem_singleton_iff.mp
      rw [← hpre]
      exact hRU
    exact congrArg Subtype.val hRP

/-- The finitely generated cone theorem in topological form (Su, Lemma 2.1). -/
theorem semigroupFG_isolated (P : PositiveCone G) (hfg : SemigroupFG P.1) :
    IsOpen ({P} : Set (PositiveCone G)) :=
  (finiteDetermination_iff_isolated P).mp (semigroupFG_finitelyDetermined P.2 hfg)

/-- A linear order with precisely left translation invariance. -/
structure LeftGroupOrder (G : Type u) [Group G] where
  order : LinearOrder G
  mul_le_mul_left : ∀ a b c : G, order.le a b → order.le (c * a) (c * b)

/-- The order induced by a strict positive cone. -/
@[instance_reducible] noncomputable def coneLinearOrder (P : PositiveCone G) : LinearOrder G := by
  classical
  letI : IsStrictTotalOrder G (fun g h => g⁻¹ * h ∈ P.1) := {
    irrefl := fun g h => P.2.1 (by simpa using h)
    trans := by
      intro g h k hgh hhk
      simpa only [mul_assoc, mul_inv_cancel_left] using P.1.mul_mem hgh hhk
    trichotomous := by
      intro g h hgh hhg
      rcases P.2.2 (g⁻¹ * h) with he | hp | hn
      · exact inv_mul_eq_one.mp he
      · exact (hgh hp).elim
      · exact (hhg (by simpa only [mul_inv_rev, inv_inv] using hn)).elim }
  exact linearOrderOfSTO (fun g h => g⁻¹ * h ∈ P.1)

/-- The cone order is invariant under every left translation. -/
noncomputable def coneLeftOrder (P : PositiveCone G) : LeftGroupOrder G where
  order := coneLinearOrder P
  mul_le_mul_left := by
    intro a b c hab
    change a = b ∨ a⁻¹ * b ∈ P.1 at hab
    change c * a = c * b ∨ (c * a)⁻¹ * (c * b) ∈ P.1
    rcases hab with rfl | hab
    · exact Or.inl rfl
    · exact Or.inr (by simpa only [mul_inv_rev, mul_assoc, inv_mul_cancel_left] using hab)

@[simp] theorem coneLeftOrder_lt (P : PositiveCone G) (g h : G) :
    (coneLeftOrder P).order.lt g h ↔ g⁻¹ * h ∈ P.1 := Iff.rfl

/-- Left translation also preserves strict inequalities. -/
theorem LeftGroupOrder.mul_lt_mul_left (O : LeftGroupOrder G) {a b : G} (c : G)
    (hab : O.order.lt a b) : O.order.lt (c * a) (c * b) := by
  let := O.order
  exact lt_of_le_of_ne (O.mul_le_mul_left a b c (le_of_lt hab))
    (fun he => ne_of_lt hab (mul_left_cancel he))

/-- Strict comparison is detected by the positive difference. -/
theorem LeftGroupOrder.lt_iff_one_lt (O : LeftGroupOrder G) (g h : G) :
    O.order.lt g h ↔ O.order.lt 1 (g⁻¹ * h) := by
  constructor
  · intro hgh
    simpa only [inv_mul_cancel] using O.mul_lt_mul_left g⁻¹ hgh
  · intro hgh
    simpa only [mul_one, mul_inv_cancel_left] using O.mul_lt_mul_left g hgh

/-- The strict positive elements of a left-invariant order form a positive cone. -/
def leftOrderCone (O : LeftGroupOrder G) : PositiveCone G := by
  letI := O.order
  let P : Subsemigroup G := {
    carrier := {g | 1 < g}
    mul_mem' := by
      intro a b ha hb
      exact lt_trans ha (by simpa only [mul_one] using O.mul_lt_mul_left a hb) }
  refine ⟨P, ?_, ?_⟩
  · exact lt_irrefl 1
  · intro g
    rcases lt_trichotomy g 1 with hg | hg | hg
    · apply Or.inr
      apply Or.inr
      change 1 < g⁻¹
      simpa only [inv_mul_cancel, mul_one] using O.mul_lt_mul_left g⁻¹ hg
    · exact Or.inl hg
    · exact Or.inr (Or.inl hg)

@[simp] theorem mem_leftOrderCone (O : LeftGroupOrder G) (g : G) :
    g ∈ (leftOrderCone O).1 ↔ O.order.lt 1 g := Iff.rfl

@[simp] theorem leftOrderCone_coneLeftOrder (P : PositiveCone G) :
    leftOrderCone (coneLeftOrder P) = P := by
  apply Subtype.ext
  ext g
  simp only [mem_leftOrderCone, coneLeftOrder_lt, inv_one, one_mul]

@[simp] theorem coneLeftOrder_leftOrderCone (O : LeftGroupOrder G) :
    coneLeftOrder (leftOrderCone O) = O := by
  have ho : (coneLeftOrder (leftOrderCone O)).order = O.order := by
    apply LinearOrder.ext_lt
    intro g h
    exact (coneLeftOrder_lt _ _ _).trans ((mem_leftOrderCone _ _).trans
      (O.lt_iff_one_lt g h).symm)
  have ext_order : ∀ (A B : LeftGroupOrder G), A.order = B.order → A = B := by
    rintro ⟨A, hA⟩ ⟨B, hB⟩ h
    cases h
    rfl
  exact ext_order _ _ ho

/-- Cones and left-invariant linear orders are equivalent, with both inverses verified. -/
noncomputable def positiveConeEquivLeftOrder : PositiveCone G ≃ LeftGroupOrder G where
  toFun := coneLeftOrder
  invFun := leftOrderCone
  left_inv := leftOrderCone_coneLeftOrder
  right_inv := coneLeftOrder_leftOrderCone

/-- Sign coordinates indexed by comparisons of arbitrary pairs of group elements. -/
noncomputable def leftOrderSign (O : LeftGroupOrder G) (p : G × G) : Bool := by
  classical
  exact decide (O.order.lt p.1 p.2)

/-- The usual topology on left orders, generated by finitely many inequalities. -/
noncomputable instance : TopologicalSpace (LeftGroupOrder G) :=
  TopologicalSpace.induced leftOrderSign inferInstance

@[simp] theorem leftOrderSign_coneLeftOrder (P : PositiveCone G) (g h : G) :
    leftOrderSign (coneLeftOrder P) (g, h) = coneSign P (g⁻¹ * h) := by
  simp [leftOrderSign, coneSign, coneLeftOrder_lt]

@[simp] theorem coneSign_leftOrderCone (O : LeftGroupOrder G) (g : G) :
    coneSign (leftOrderCone O) g = leftOrderSign O (1, g) := by
  simp [leftOrderSign, coneSign]

/-- The sign and inequality topologies correspond under the verified cone/order bijection. -/
noncomputable def positiveConeHomeomorphLeftOrder : PositiveCone G ≃ₜ LeftGroupOrder G where
  toEquiv := positiveConeEquivLeftOrder
  continuous_toFun := by
    apply continuous_induced_rng.mpr
    apply continuous_pi
    intro p
    change Continuous (fun P : PositiveCone G => leftOrderSign (coneLeftOrder P) (p.1, p.2))
    simp only [leftOrderSign_coneLeftOrder]
    exact (continuous_apply (p.1⁻¹ * p.2)).comp
      (show Continuous (coneSign (G := G)) from continuous_induced_dom)
  continuous_invFun := by
    apply continuous_induced_rng.mpr
    apply continuous_pi
    intro g
    change Continuous (fun O : LeftGroupOrder G => coneSign (leftOrderCone O) g)
    simp only [coneSign_leftOrderCone]
    exact (continuous_apply (1, g)).comp
      (show Continuous (leftOrderSign (G := G)) from continuous_induced_dom)

/-- The isolation interface in terms of actual left orders and their inequality topology. -/
theorem finiteDetermination_iff_leftOrder_isolated (P : PositiveCone G) :
    FinitelyDetermined P.1 ↔ IsOpen ({coneLeftOrder P} : Set (LeftGroupOrder G)) := by
  rw [finiteDetermination_iff_isolated]
  have h := (positiveConeHomeomorphLeftOrder (G := G)).isOpen_image (s := {P})
  simpa [positiveConeHomeomorphLeftOrder, positiveConeEquivLeftOrder] using h.symm

end FnZPositiveCones
