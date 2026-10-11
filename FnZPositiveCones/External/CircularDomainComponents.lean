module

public import FnZPositiveCones.External.CircularExpandedFiniteArcs
public import FnZPositiveCones.External.PingPongCircleComponents
public import Mathlib.Topology.Connected.TotallyDisconnected

@[expose] public section

/-! Finiteness of actual connected components, extracted from finite arc unions. -/
namespace FnZPositiveCones.CircularDynamics

/-- A finite preconnected cover gives finitely many actual connected components.
No enumeration or cardinality of components is assumed. -/
theorem finite_components_of_finite_preconnected_cover {X I : Type*}
    [TopologicalSpace X] [Finite I] (D : I → Set X)
    (hpre : ∀ i, IsPreconnected (D i)) (hcover : ∀ x, ∃ i, x ∈ D i) :
    Finite (ConnectedComponents X) := by
  classical
  let J := {i : I // (D i).Nonempty}
  let p : J → X := fun j => j.property.choose
  have hp (j : J) : p j ∈ D j.val := j.property.choose_spec
  apply Finite.of_surjective (fun j : J => ConnectedComponents.mk (p j))
  intro c
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
  obtain ⟨i, hi⟩ := hcover x
  let j : J := ⟨i, x, hi⟩
  refine ⟨j, ?_⟩
  exact ConnectedComponents.coe_eq_coe'.mpr ((hpre i).subset_connectedComponent hi (hp j))

/-- Intersecting a closed arc with the interior of a set containing that arc
remains preconnected: only its two endpoints can be removed. -/
theorem closedCircleArc_inter_interior_preconnected (a b : ℝ) (E : Set StandardCircle)
    (hsub : closedCircleArc a b ⊆ E) :
    IsPreconnected (closedCircleArc a b ∩ interior E) := by
  let q : ℝ → StandardCircle := fun x => (x : StandardCircle)
  have hq : Continuous q := AddCircle.continuous_mk' (1 : ℝ)
  have ho : IsOpenMap q := QuotientAddGroup.isOpenMap_coe
  by_cases hab : a < b
  · have hcore : q '' Set.Ioo a b ⊆ interior E := (ho _ isOpen_Ioo).subset_interior_iff.mpr
      ((Set.image_mono Set.Ioo_subset_Icc_self).trans hsub)
    apply (isPreconnected_Ioo.image q hq.continuousOn).subset_closure
    · exact fun _ hx => ⟨Set.image_mono Set.Ioo_subset_Icc_self hx, hcore hx⟩
    · intro x hx
      have hc : x ∈ q '' closure (Set.Ioo a b) := by
        rw [closure_Ioo hab.ne]
        exact hx.1
      exact image_closure_subset_closure_image hq hc
  · have hs : closedCircleArc a b ⊆ {(a : StandardCircle)} := by
      rintro _ ⟨x, hx, rfl⟩
      have he : x = a := le_antisymm (hx.2.trans (le_of_not_gt hab)) hx.1
      simp only [he, Set.mem_singleton_iff]
    have hsing : (closedCircleArc a b ∩ interior E).Subsingleton := by
      intro x hx y hy
      exact (hs hx.1).trans (hs hy.1).symm
    exact hsing.isPreconnected

/-- The interior of a finite closed-arc union has finitely many actual
components, including all cases of touching and degenerate raw arcs. -/
theorem finite_components_interior_finite_arcs (E : Set StandardCircle)
    (F : Finset (ℝ × ℝ)) (hE : E = ⋃ p ∈ F, closedCircleArc p.1 p.2) :
    Finite (ConnectedComponents ↥(interior E)) := by
  let D : ↥F → Set ↥(interior E) := fun p => Subtype.val ⁻¹' closedCircleArc p.val.1 p.val.2
  apply finite_components_of_finite_preconnected_cover D
  · intro p
    apply Topology.IsInducing.subtypeVal.isPreconnected_image.mp
    rw [Subtype.image_preimage_coe, Set.inter_comm]
    apply closedCircleArc_inter_interior_preconnected
    intro x hx
    rw [hE]
    exact Set.mem_iUnion₂.mpr ⟨p.val, p.property, hx⟩
  · intro x
    have hx : x.val ∈ E := interior_subset x.property
    have hx' : x.val ∈ ⋃ p ∈ F, closedCircleArc p.1 p.2 := hE ▸ hx
    obtain ⟨p, hp, hx'⟩ := Set.mem_iUnion₂.mp hx'
    exact ⟨⟨p, hp⟩, hx'⟩

/-- A circle set described by finitely many intervals in the normalized
coordinate has a complement with finitely many connected components. The proof
uses the finite family of choices of left or right half-lines. -/
theorem finite_components_compl_coordinate_intervals {I : Type*} [Finite I]
    (E : Set StandardCircle) (a b : I → ℝ)
    (hE : ∀ x, x ∈ E ↔ ∃ i, circleCoordinate x ∈ Set.Icc (a i) (b i)) :
    Finite (ConnectedComponents ↥Eᶜ) := by
  classical
  let _ := Fintype.ofFinite I
  let T : (I → Bool) → Set ℝ := fun e =>
    Set.Ico 0 1 ∩ {x | ∀ i, if e i then x < a i else b i < x}
  let q : ℝ → StandardCircle := fun x => (x : StandardCircle)
  let S (e : I → Bool) := q '' T e
  have hpre (e : I → Bool) : IsPreconnected (S e) := by
    have hc : Set.OrdConnected (T e) := by
      refine ⟨?_⟩
      intro x hx y hy z hz
      refine ⟨⟨hx.1.1.trans hz.1, hz.2.trans_lt hy.1.2⟩, ?_⟩
      intro i
      have hxi := hx.2 i
      have hyi := hy.2 i
      cases he : e i
      · simp only [he, Bool.false_eq_true, ↓reduceIte] at hxi hyi ⊢
        exact hxi.trans_le hz.1
      · simp only [he, ↓reduceIte] at hxi hyi ⊢
        exact hz.2.trans_lt hyi
    exact hc.isPreconnected.image q (AddCircle.continuous_mk' (1 : ℝ)).continuousOn
  have hsub (e : I → Bool) : S e ⊆ Eᶜ := by
    rintro _ ⟨x, hx, rfl⟩ hxE
    obtain ⟨i, hi⟩ := (hE (q x)).mp hxE
    have hxcoord : circleCoordinate (q x) = x := circleCoordinate_coe hx.1
    rw [hxcoord] at hi
    have hh := hx.2 i
    cases he : e i
    · simp only [he, Bool.false_eq_true, ↓reduceIte] at hh
      exact not_lt_of_ge hi.2 hh
    · simp only [he, ↓reduceIte] at hh
      exact not_lt_of_ge hi.1 hh
  apply finite_components_of_finite_preconnected_cover
    (fun e : I → Bool => Subtype.val ⁻¹' S e)
  · intro e
    apply Topology.IsInducing.subtypeVal.isPreconnected_image.mp
    rw [Subtype.image_preimage_coe, Set.inter_eq_right.mpr (hsub e)]
    exact hpre e
  · intro x
    let e : I → Bool := fun i => decide (circleCoordinate x.val < a i)
    refine ⟨e, circleCoordinate x.val, ⟨circleCoordinate_mem x.val, ?_⟩, coe_circleCoordinate x.val⟩
    intro i
    by_cases hi : circleCoordinate x.val < a i
    · simp only [e, hi, decide_true, ↓reduceIte]
    · have hbi : b i < circleCoordinate x.val := by
        by_contra hbi
        exact x.property ((hE x.val).mpr ⟨i, le_of_not_gt hi, le_of_not_gt hbi⟩)
      simpa only [e, hi, decide_false, Bool.false_eq_true, ↓reduceIte] using hbi

/-- The complement of a finite closed-arc union avoiding zero has finitely
many actual components. Each nonempty arc is normalized through the continuous
coordinate chart before the finite half-line construction is applied. -/
theorem finite_components_compl_finite_arcs (E : Set StandardCircle)
    (F : Finset (ℝ × ℝ)) (hE : E = ⋃ p ∈ F, closedCircleArc p.1 p.2)
    (hzero : 0 ∉ E) : Finite (ConnectedComponents ↥Eᶜ) := by
  classical
  let J := {p : ↥F // (closedCircleArc p.val.1 p.val.2).Nonempty}
  let K (j : J) := circleCoordinate '' closedCircleArc j.val.val.1 j.val.val.2
  let a (j : J) := sInf (K j)
  let b (j : J) := sSup (K j)
  have hsub (p : ↥F) : closedCircleArc p.val.1 p.val.2 ⊆ E := by
    intro x hx
    rw [hE]
    exact Set.mem_iUnion₂.mpr ⟨p.val, p.property, hx⟩
  have hK (j : J) : K j = Set.Icc (a j) (b j) := by
    have hcont : ContinuousOn circleCoordinate (closedCircleArc j.val.val.1 j.val.val.2) := by
      intro x hx
      apply (continuousAt_circleCoordinate ?_).continuousWithinAt
      intro he
      exact hzero (he ▸ hsub j.val hx)
    apply eq_Icc_of_connected_compact
    · have hconn : IsConnected (closedCircleArc j.val.val.1 j.val.val.2) :=
        ⟨j.property, isPreconnected_Icc.image _ (AddCircle.continuous_mk' (1 : ℝ)).continuousOn⟩
      exact hconn.image _ hcont
    · exact (isCompact_closedCircleArc _ _).image_of_continuousOn hcont
  apply finite_components_compl_coordinate_intervals E a b
  intro x
  constructor
  · intro hx
    have hx' : x ∈ ⋃ p ∈ F, closedCircleArc p.1 p.2 := hE ▸ hx
    obtain ⟨p, hp, hx'⟩ := Set.mem_iUnion₂.mp hx'
    let j : J := ⟨⟨p, hp⟩, x, hx'⟩
    refine ⟨j, ?_⟩
    rw [← hK j]
    exact ⟨x, hx', rfl⟩
  · rintro ⟨j, hj⟩
    rw [← hK j] at hj
    obtain ⟨y, hy, he⟩ := hj
    have hyx : y = x := by
      simpa only [coe_circleCoordinate] using congrArg (fun r : ℝ => (r : StandardCircle)) he
    exact hyx ▸ hsub j.val hy

universe u
variable {ι : Type u} [DecidableEq ι] [Nonempty ι] [Finite ι]
variable {C : CircularGroupOrder (FreeGroup ι)} (R : CircularRealization C)

/-- Component finiteness for the actual open expanded domains. -/
theorem finite_components_openExpandedDomain (h : FreeGroup ι) (hh : C.IsSuccessor h)
    (hsep : ∀ s t, s ≠ t →
      Disjoint (closure (letterOrbit (realizationGenerators R) 0 s))
        (closure (letterOrbit (realizationGenerators R) 0 t))) (s : ι × Bool) :
    Finite (ConnectedComponents ↥(openExpandedDomain R h s)) := by
  obtain ⟨F, hF⟩ := expandedFirstLetterDomain_finite_arcs R h hh hsep s
  exact finite_components_interior_finite_arcs _ F hF

/-- Actual complement-component finiteness for each expanded closed domain. -/
theorem finite_components_compl_expandedFirstLetterDomain (h : FreeGroup ι)
    (hh : C.IsSuccessor h)
    (hsep : ∀ s t, s ≠ t →
      Disjoint (closure (letterOrbit (realizationGenerators R) 0 s))
        (closure (letterOrbit (realizationGenerators R) 0 t))) (s : ι × Bool) :
    Finite (ConnectedComponents ↥(expandedFirstLetterDomain R h s)ᶜ) := by
  obtain ⟨F, hF⟩ := expandedFirstLetterDomain_finite_arcs R h hh hsep s
  exact finite_components_compl_finite_arcs _ F hF
    (base_not_mem_expandedFirstLetterDomain R h hh hsep s)

/-- Normalization preserves finiteness of the actual components through its
proved action-induced homeomorphism of the complement and domain. -/
theorem finite_components_normalizedExpandedDomain (h : FreeGroup ι)
    (hh : C.IsSuccessor h)
    (hsep : ∀ s t, s ≠ t →
      Disjoint (closure (letterOrbit (realizationGenerators R) 0 s))
        (closure (letterOrbit (realizationGenerators R) 0 t))) (s : ι × Bool) :
    Finite (ConnectedComponents ↥(normalizedExpandedDomain R h s)) := by
  rcases s with ⟨i, s⟩
  cases s
  · exact finite_components_openExpandedDomain R h hh hsep (i, false)
  · have hfinite : Finite (ConnectedComponents ↥(closure (openExpandedDomain R h (i, false)))ᶜ) := by
      rw [closure_openExpandedDomain R h hh hsep]
      exact finite_components_compl_expandedFirstLetterDomain R h hh hsep (i, false)
    let _ := hfinite
    exact Finite.of_equiv _ (normalizedPositiveDomainComponents
      (R.actionHomeomorph (FreeGroup.of i)) (openExpandedDomain R h (i, false)))

end FnZPositiveCones.CircularDynamics
