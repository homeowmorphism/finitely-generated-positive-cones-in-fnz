module

public import FnZPositiveCones.External.CircularNormalizedOrbit
public import FnZPositiveCones.External.CircularGapCoordinate
public import FnZPositiveCones.External.PingPongGapPotential

@[expose] public section

/-! The invariant orbit-gap coordinate forces the actual finite graph to be connected. -/
namespace FnZPositiveCones
open CircularDynamics
universe u

namespace CircularDynamics

theorem frontier_domainComponent_subset {S : Set StandardCircle} (ho : IsOpen S)
    (c : ConnectedComponents ↥S) : frontier (domainComponent S c) ⊆ frontier S := by
  intro x hx
  refine ⟨closure_mono (domainComponent_subset S c) hx.1, ?_⟩
  rw [ho.interior_eq]
  intro hxS
  have hxc : x ∈ domainComponent S c := by
    rw [← closure_domainComponent_inter S c]
    exact ⟨hx.1, hxS⟩
  exact hx.2 ((isOpen_domainComponent ho c).interior_eq.symm ▸ hxc)

namespace CircleIntervalFamily
variable {I : Type u} (F : CircleIntervalFamily I) [Fintype I]

theorem gap_endpoints_ne (c : I) :
    (F.right c : StandardCircle) ≠ (F.left (F.next c) : StandardCircle) := by
  have hne : F.right c ≠ F.left (F.next c) := by
    by_cases h : F.left c < F.left (F.next c)
    · exact (F.right_lt_left_of_left_lt h).ne
    · exact ((le_of_not_gt h).trans_lt (F.left_lt_right c)).ne'
  intro he
  apply hne
  simpa only [circleCoordinate_coe ⟨((F.left_pos c).trans (F.left_lt_right c)).le, F.right_lt_one c⟩,
    circleCoordinate_coe ⟨(F.left_pos _).le, (F.left_lt_right _).trans (F.right_lt_one _)⟩]
    using congrArg circleCoordinate he

theorem closure_gap_eq_segment (c : I) : closure (F.gap c) =
    circularClosedSegment (F.right c : StandardCircle) (F.left (F.next c)) := by
  rw [closure_eq_self_union_frontier, F.frontier_gap, F.gap_eq_sbtw]
  ext x
  simp only [circularClosedSegment, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff,
    Set.mem_ofPred_eq]
  tauto

end CircleIntervalFamily
end CircularDynamics

namespace NormalizedIntervalData
variable {ι : Type u} {C : CircularGroupOrder (FreeGroup ι)}
    {R : CircularRealization C} {D : FiniteNormalizedDomains R} (Q : NormalizedIntervalData D)

attribute [local instance] componentFintype componentNonempty

theorem componentFamily_arc_eq (c : PingPong.Component D.PositiveComponent D.NegativeComponent) :
    Q.componentFamily.arc c =
      domainComponent (D.domain (D.componentSignsEquiv c).1) (D.componentSignsEquiv c).2 :=
  Q.component_eq _ _

theorem iUnion_componentFamily : (⋃ c, Q.componentFamily.arc c) = ⋃ s, D.domain s := by
  ext x
  constructor
  · intro hx
    obtain ⟨c, hc⟩ := Set.mem_iUnion.mp hx
    rw [Q.componentFamily_arc_eq] at hc
    exact Set.mem_iUnion.mpr ⟨_, domainComponent_subset _ _ hc⟩
  · intro hx
    obtain ⟨s, hs⟩ := Set.mem_iUnion.mp hx
    let d := ConnectedComponents.mk (⟨x, hs⟩ : D.domain s)
    let c := D.componentSignsEquiv.symm ⟨s, d⟩
    apply Set.mem_iUnion.mpr ⟨c, ?_⟩
    rw [Q.componentFamily_arc_eq]
    rw [show D.componentSignsEquiv c = ⟨s, d⟩ from D.componentSignsEquiv.apply_symm_apply ⟨s, d⟩]
    exact ⟨⟨x, hs⟩, rfl, rfl⟩

theorem endpoint_right_not_orbitClosure [Finite ι]
    (c : PingPong.Component D.PositiveComponent D.NegativeComponent) :
    (Q.componentFamily.right c : StandardCircle) ∉
      closure (Set.range (fun g : FreeGroup ι => R.action g 0)) := by
  have hx : (Q.componentFamily.right c : StandardCircle) ∈ frontier (Q.componentFamily.arc c) := by
    rw [Q.componentFamily.frontier_arc]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, or_true]
  rw [Q.componentFamily_arc_eq] at hx
  have hxD := frontier_domainComponent_subset (D.isOpen_domain _) _ hx
  exact fun hbad => Set.disjoint_left.mp (D.frontier_disjoint_orbitClosure _) hxD hbad

variable [Fintype ι] [Nonempty ι]

/-- There is exactly one finite complementary interval containing the base. -/
theorem exists_base_gap : ∃ b, (0 : StandardCircle) ∈ Q.componentFamily.gap b := by
  have hz : (0 : StandardCircle) ∈ (closure (⋃ c, Q.componentFamily.arc c))ᶜ := by
    rw [Q.iUnion_componentFamily, closure_iUnion_of_finite]
    intro hz
    obtain ⟨s, hs⟩ := Set.mem_iUnion.mp hz
    exact D.base_avoids s hs
  rw [← Q.componentFamily.iUnion_gap] at hz
  exact Set.mem_iUnion.mp hz

/-- Every other closed finite gap lies wholly in one tight orbit gap: its
interior and endpoints avoid the orbit closure. -/
theorem nonbase_gap_disjoint_orbitClosure
    {b : PingPong.Component D.PositiveComponent D.NegativeComponent}
    (hb : (0 : StandardCircle) ∈ Q.componentFamily.gap b)
    {c : PingPong.Component D.PositiveComponent D.NegativeComponent} (hcb : c ≠ b) :
    Disjoint (closure (Q.componentFamily.gap c))
      (closure (Set.range (fun g : FreeGroup ι => R.action g 0))) := by
  have hzero : (0 : StandardCircle) ∉ closure (Q.componentFamily.gap c) := by
    have hsub : closure (Q.componentFamily.gap c) ⊆ (Q.componentFamily.gap b)ᶜ := by
      apply closure_minimal
      · exact fun _ hc hb' => Set.disjoint_left.mp (Q.componentFamily.gap_disjoint hcb) hc hb'
      · exact (Q.componentFamily.isOpen_gap b).isClosed_compl
    exact fun h => hsub h hb
  have hsub : closure (Q.componentFamily.gap c) ⊆ (⋃ s, D.domain s)ᶜ := by
    apply closure_minimal
    · intro x hx hxD
      have hgap : x ∈ (closure (⋃ d, Q.componentFamily.arc d))ᶜ := by
        rw [← Q.componentFamily.iUnion_gap]
        exact Set.mem_iUnion.mpr ⟨c, hx⟩
      apply hgap
      rw [Q.iUnion_componentFamily]
      exact subset_closure hxD
    · exact (isOpen_iUnion D.isOpen_domain).isClosed_compl
  apply Set.disjoint_left.mpr
  intro x hx hxK
  rcases D.orbitClosure_subset_base_union_domains hxK with hx0 | hxD
  · exact hzero (hx0 ▸ hx)
  · exact hsub hx hxD

/-- The invariant coordinate strictly increases across every nonbase finite
gap. This is the geometric input to the finite potential argument. -/
theorem gapCoordinate_lt_across_nonbase {a : FreeGroup ι} (ha : C.IsSuccessor a)
    {b : PingPong.Component D.PositiveComponent D.NegativeComponent}
    (hb : (0 : StandardCircle) ∈ Q.componentFamily.gap b)
    {c : PingPong.Component D.PositiveComponent D.NegativeComponent} (hcb : c ≠ b) :
    R.gapCoordinate a (Q.componentFamily.right c : StandardCircle) <
      R.gapCoordinate a (Q.componentFamily.left (Q.circle c) : StandardCircle) := by
  have hpre := (Q.componentFamily.isConnected_gap c).isPreconnected.closure
  have hx : (Q.componentFamily.right c : StandardCircle) ∈ closure (Q.componentFamily.gap c) := by
    rw [Q.componentFamily.closure_gap_eq_segment]
    exact mem_circularClosedSegment_left _ _
  obtain ⟨g, hg⟩ := R.preconnected_subset_circleGap ha hpre
    (Q.nonbase_gap_disjoint_orbitClosure hb hcb) hx
  apply R.gapCoordinate_lt_of_segment_subset ha (Q.componentFamily.gap_endpoints_ne c)
  rw [← Q.componentFamily.closure_gap_eq_segment]
  exact hg

/-- The actual finite endpoint graph is connected. Every boundary cycle must
pass through the unique base gap, since the invariant gap coordinate would
otherwise increase strictly around a finite cycle. -/
theorem gap_connected {a : FreeGroup ι} (ha : C.IsSuccessor a) :
    ∀ c d, Relation.EqvGen
      (PingPong.GapStep Q.circle (PingPong.polygonGraph Q.forward Q.backward)) c d := by
  obtain ⟨b, hb⟩ := Q.exists_base_gap
  let graph := PingPong.polygonGraph Q.forward Q.backward
  let V := fun c => R.gapCoordinate a (Q.componentFamily.right c : StandardCircle)
  apply PingPong.gap_connected_of_increase_off_one Q.circle graph V b
  intro c hcb
  have hlt := Q.gapCoordinate_lt_across_nonbase ha hb hcb
  let d := (graph⁻¹ * Q.circle) c
  have hd : graph d = Q.circle c := graph.apply_symm_apply _
  obtain ⟨g, hg⟩ := Q.graph_endpoint d
  change R.action g (Q.componentFamily.right d : StandardCircle) =
    (Q.componentFamily.left (graph d) : StandardCircle) at hg
  rw [hd] at hg
  have hcoord := R.gapCoordinate_action ha g (Q.endpoint_right_not_orbitClosure d)
  rw [hg] at hcoord
  exact hlt.trans_eq hcoord

include Q in
/-- The constructed normalized domains on a tight circular realization with a
successor force the free rank to be even. No connectivity input remains. -/
theorem even_card {a : FreeGroup ι} (ha : C.IsSuccessor a) : Even (Fintype.card ι) :=
  Q.even_card_of_gap_connected (Q.gap_connected ha)

end NormalizedIntervalData
end FnZPositiveCones
