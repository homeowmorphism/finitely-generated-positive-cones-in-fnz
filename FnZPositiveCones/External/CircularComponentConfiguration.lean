module

public import FnZPositiveCones.External.CircularEndpointMaps

@[expose] public section

/-! The finite polygon and circle permutations on actual normalized components. -/
namespace FnZPositiveCones
open CircularDynamics
universe u

namespace FiniteNormalizedDomains
variable {ι : Type u} {C : CircularGroupOrder (FreeGroup ι)}
    {R : CircularRealization C} (D : FiniteNormalizedDomains R)

abbrev PositiveComponent (i : ι) := ConnectedComponents ↥(D.domain (i, true))
abbrev NegativeComponent (i : ι) := ConnectedComponents ↥(D.domain (i, false))
abbrev SignedComponent := Σ s : ι × Bool, ConnectedComponents ↥(D.domain s)

/-- The same actual components, grouped by generator for the parity API. -/
def componentSignsEquiv : PingPong.Component D.PositiveComponent D.NegativeComponent ≃
    D.SignedComponent where
  toFun := fun ⟨i, c⟩ => match c with
    | Sum.inl a => ⟨(i, true), a⟩
    | Sum.inr b => ⟨(i, false), b⟩
  invFun := fun ⟨(i, s), c⟩ => match s with
    | false => ⟨i, Sum.inr c⟩
    | true => ⟨i, Sum.inl c⟩
  left_inv := by rintro ⟨i, a | b⟩ <;> rfl
  right_inv := by rintro ⟨⟨i, s⟩, c⟩; cases s <;> rfl

end FiniteNormalizedDomains

/-- A chosen interval description of the actual connected components. Its
existence is proved from the domain data, including same-color separation. -/
structure NormalizedIntervalData {ι : Type u} {C : CircularGroupOrder (FreeGroup ι)}
    {R : CircularRealization C} (D : FiniteNormalizedDomains R) where
  family : CircleIntervalFamily D.SignedComponent
  component_eq : ∀ s c, family.arc ⟨s, c⟩ = domainComponent (D.domain s) c

noncomputable def FiniteNormalizedDomains.intervalData {ι : Type u}
    {C : CircularGroupOrder (FreeGroup ι)} {R : CircularRealization C}
    (D : FiniteNormalizedDomains R) : NormalizedIntervalData D := by
  let h := finiteNormalizedDomains_exists_intervalFamily D
  exact ⟨h.choose, h.choose_spec⟩

namespace NormalizedIntervalData
variable {ι : Type u} {C : CircularGroupOrder (FreeGroup ι)}
    {R : CircularRealization C} {D : FiniteNormalizedDomains R} (Q : NormalizedIntervalData D)

def signedFamily (s : ι × Bool) : CircleIntervalFamily (ConnectedComponents ↥(D.domain s)) where
  left c := Q.family.left ⟨s, c⟩
  right c := Q.family.right ⟨s, c⟩
  left_pos c := Q.family.left_pos ⟨s, c⟩
  left_lt_right c := Q.family.left_lt_right ⟨s, c⟩
  right_lt_one c := Q.family.right_lt_one ⟨s, c⟩
  separated c d hcd := Q.family.separated ⟨s, c⟩ ⟨s, d⟩ (by simpa using hcd)

theorem iUnion_signedFamily (s : ι × Bool) : (⋃ c, (Q.signedFamily s).arc c) = D.domain s := by
  have he (c) : (Q.signedFamily s).arc c = domainComponent (D.domain s) c := Q.component_eq s c
  simp_rw [he]
  exact iUnion_domainComponent _

def componentFamily : CircleIntervalFamily (PingPong.Component D.PositiveComponent D.NegativeComponent) where
  left c := Q.family.left (D.componentSignsEquiv c)
  right c := Q.family.right (D.componentSignsEquiv c)
  left_pos c := Q.family.left_pos (D.componentSignsEquiv c)
  left_lt_right c := Q.family.left_lt_right (D.componentSignsEquiv c)
  right_lt_one c := Q.family.right_lt_one (D.componentSignsEquiv c)
  separated _ _ hcd := Q.family.separated _ _ (fun he => hcd (D.componentSignsEquiv.injective he))

noncomputable local instance componentFintype (s : ι × Bool) :
    Fintype (ConnectedComponents ↥(D.domain s)) := by
  let := D.finite_components s
  exact Fintype.ofFinite _

local instance componentNonempty (s : ι × Bool) :
    Nonempty (ConnectedComponents ↥(D.domain s)) :=
  ⟨ConnectedComponents.mk ⟨(D.nonempty_domain s).choose, (D.nonempty_domain s).choose_spec⟩⟩

theorem negative_image (i : ι) :
    (R.actionHomeomorph (FreeGroup.of i)).symm ''
      (closure (⋃ c, (Q.signedFamily (i, true)).arc c))ᶜ =
      ⋃ c, (Q.signedFamily (i, false)).arc c := by
  rw [Q.iUnion_signedFamily, Q.iUnion_signedFamily]
  exact D.image_domain (i, false)

theorem positive_image (i : ι) :
    (R.actionHomeomorph (FreeGroup.of i)) ''
      (closure (⋃ c, (Q.signedFamily (i, false)).arc c))ᶜ =
      ⋃ c, (Q.signedFamily (i, true)).arc c := by
  rw [Q.iUnion_signedFamily, Q.iUnion_signedFamily]
  exact D.image_domain (i, true)

/-- The negative generator maps the gap after a positive component onto the
negative component selected by this equivalence. -/
noncomputable def forward (i : ι) : D.PositiveComponent i ≃ D.NegativeComponent i :=
  (Q.signedFamily (i, true)).complementImageEquiv (Q.signedFamily (i, false))
    (R.actionHomeomorph (FreeGroup.of i)).symm (Q.negative_image i)

/-- The positive generator gives the other half of the alternating polygon. -/
noncomputable def backward (i : ι) : D.NegativeComponent i ≃ D.PositiveComponent i :=
  (Q.signedFamily (i, false)).complementImageEquiv (Q.signedFamily (i, true))
    (R.actionHomeomorph (FreeGroup.of i)) (Q.positive_image i)

noncomputable def positiveNext (i : ι) : Equiv.Perm (D.PositiveComponent i) :=
  (Q.signedFamily (i, true)).next

theorem positiveNext_isCycleOn (i : ι) : (Q.positiveNext i).IsCycleOn Set.univ :=
  (Q.signedFamily (i, true)).next_isCycleOn

/-- The source's local component equation holds for the actual generator
action and actual normalized domains, without an adjacency hypothesis. -/
theorem backward_forward (i : ι) (c : D.PositiveComponent i) :
    Q.backward i (Q.forward i c) = Q.positiveNext i c := by
  apply (Q.signedFamily (i, true)).complementImageEquiv_adjacency
    (Q.signedFamily (i, false)) (R.actionHomeomorph (FreeGroup.of i)).symm
    (preservesCircular_inv (R.action_preserves (FreeGroup.of i))) (Q.negative_image i)
    (Q.positive_image i) c

/-- Every polygon edge identifies its departing right endpoint with the
arriving left endpoint by an actual group element. -/
theorem graph_endpoint (c : PingPong.Component D.PositiveComponent D.NegativeComponent) :
    ∃ g : FreeGroup ι,
      R.action g (Q.componentFamily.right c : StandardCircle) =
        (Q.componentFamily.left (PingPong.polygonGraph Q.forward Q.backward c) : StandardCircle) := by
  rcases c with ⟨i, c | c⟩
  · have he := (Q.signedFamily (i, true)).gap_image_arc_endpoints (Q.signedFamily (i, false))
      (R.actionHomeomorph (FreeGroup.of i)).symm
      (preservesCircular_inv (R.action_preserves (FreeGroup.of i))) c (Q.forward i c)
      ((Q.signedFamily (i, true)).complementImageEquiv_image (Q.signedFamily (i, false))
        (R.actionHomeomorph (FreeGroup.of i)).symm (Q.negative_image i) c)
    refine ⟨(FreeGroup.of i)⁻¹, ?_⟩
    rw [map_inv]
    exact he.1
  · have he := (Q.signedFamily (i, false)).gap_image_arc_endpoints (Q.signedFamily (i, true))
      (R.actionHomeomorph (FreeGroup.of i)) (R.action_preserves (FreeGroup.of i)) c (Q.backward i c)
      ((Q.signedFamily (i, false)).complementImageEquiv_image (Q.signedFamily (i, true))
        (R.actionHomeomorph (FreeGroup.of i)) (Q.positive_image i) c)
    exact ⟨FreeGroup.of i, he.1⟩

variable [Fintype ι]

noncomputable def circle : Equiv.Perm (PingPong.Component D.PositiveComponent D.NegativeComponent) :=
  Q.componentFamily.next

theorem circle_isCycleOn : Q.circle.IsCycleOn Set.univ := Q.componentFamily.next_isCycleOn

/-- All geometric hypotheses of the finite parity theorem except connectivity
are now supplied by the actual normalized domains. -/
theorem even_card_of_gap_connected [Nonempty ι]
    (hgap : ∀ c d, Relation.EqvGen
      (PingPong.GapStep Q.circle (PingPong.polygonGraph Q.forward Q.backward)) c d) :
    Even (Fintype.card ι) := by
  classical
  exact PingPong.even_of_connected_component_configuration Q.forward Q.backward
    Q.positiveNext Q.positiveNext_isCycleOn Q.backward_forward Q.circle Q.circle_isCycleOn hgap

end NormalizedIntervalData
end FnZPositiveCones
