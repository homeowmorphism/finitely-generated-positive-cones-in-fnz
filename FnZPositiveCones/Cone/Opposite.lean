module

public import FnZPositiveCones.Cone.Topology

@[expose] public section

/-! Reversing the signs of a strict positive cone, including its sign topology. -/

namespace FnZPositiveCones

universe u
variable {G : Type u} [Group G]

/-- Inverse images under inversion form a semigroup because products reverse
their order. No commutativity of the ambient group is required. -/
def oppositeSubsemigroup (P : Subsemigroup G) : Subsemigroup G where
  carrier := {g | g⁻¹ ∈ P}
  mul_mem' {a b} ha hb := by
    change (a * b)⁻¹ ∈ P
    simpa only [mul_inv_rev] using P.mul_mem hb ha

@[simp] theorem mem_oppositeSubsemigroup (P : Subsemigroup G) (g : G) :
    g ∈ oppositeSubsemigroup P ↔ g⁻¹ ∈ P := Iff.rfl

@[simp] theorem oppositeSubsemigroup_oppositeSubsemigroup (P : Subsemigroup G) :
    oppositeSubsemigroup (oppositeSubsemigroup P) = P := by
  ext g
  simp

/-- Reversing every sign preserves strict positivity and totality. -/
theorem positiveCone_opposite {P : Subsemigroup G} (hP : IsPositiveCone P) :
    IsPositiveCone (oppositeSubsemigroup P) := by
  constructor
  · simpa using hP.1
  · intro g
    rcases hP.2 g with he | hp | hn
    · exact Or.inl he
    · exact Or.inr (Or.inr (by simpa using hp))
    · exact Or.inr (Or.inl hn)

/-- The strict cone for the reverse left order. -/
def PositiveCone.opposite (P : PositiveCone G) : PositiveCone G :=
  ⟨oppositeSubsemigroup P.1, positiveCone_opposite P.2⟩

@[simp] theorem PositiveCone.mem_opposite (P : PositiveCone G) (g : G) :
    g ∈ P.opposite.1 ↔ g⁻¹ ∈ P.1 := Iff.rfl

/-- A nonidentity distinguished element is positive in one of the two orientations. -/
theorem PositiveCone.mem_or_mem_opposite (P : PositiveCone G) {g : G} (hg : g ≠ 1) :
    g ∈ P.1 ∨ g ∈ P.opposite.1 :=
  (P.2.2 g).resolve_left hg

@[simp] theorem PositiveCone.opposite_opposite (P : PositiveCone G) :
    P.opposite.opposite = P := by
  apply Subtype.ext
  exact oppositeSubsemigroup_oppositeSubsemigroup P.1

theorem PositiveCone.opposite_involutive :
    Function.Involutive (PositiveCone.opposite (G := G)) :=
  PositiveCone.opposite_opposite

@[simp] theorem coneSign_opposite (P : PositiveCone G) (g : G) :
    coneSign P.opposite g = coneSign P g⁻¹ := rfl

/-- Sign reversal is continuous: each new sign is one old inverse coordinate. -/
theorem continuous_positiveCone_opposite :
    Continuous (PositiveCone.opposite (G := G)) := by
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro g
  change Continuous (fun P : PositiveCone G => coneSign P g⁻¹)
  exact (continuous_apply g⁻¹).comp
    (show Continuous (coneSign (G := G)) from continuous_induced_dom)

/-- Opposite cones give an involutive homeomorphism of the sign space. -/
noncomputable def positiveConeOppositeHomeomorph : PositiveCone G ≃ₜ PositiveCone G where
  toFun := PositiveCone.opposite
  invFun := PositiveCone.opposite
  left_inv := PositiveCone.opposite_opposite
  right_inv := PositiveCone.opposite_opposite
  continuous_toFun := continuous_positiveCone_opposite
  continuous_invFun := continuous_positiveCone_opposite

/-- Isolation is unaffected by reversing every sign. -/
theorem isOpen_singleton_opposite_iff (P : PositiveCone G) :
    IsOpen ({P.opposite} : Set (PositiveCone G)) ↔
      IsOpen ({P} : Set (PositiveCone G)) := by
  have h := (positiveConeOppositeHomeomorph (G := G)).isOpen_image (s := {P})
  change IsOpen (PositiveCone.opposite '' ({P} : Set (PositiveCone G))) ↔ _ at h
  simpa only [Set.image_singleton] using h

/-- Finite determination is unaffected by reversing every sign. -/
theorem finitelyDetermined_opposite_iff (P : PositiveCone G) :
    FinitelyDetermined P.opposite.1 ↔ FinitelyDetermined P.1 := by
  rw [finiteDetermination_iff_isolated, finiteDetermination_iff_isolated,
    isOpen_singleton_opposite_iff]

end FnZPositiveCones
