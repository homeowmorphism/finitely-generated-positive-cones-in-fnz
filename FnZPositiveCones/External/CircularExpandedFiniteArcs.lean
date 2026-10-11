module

public import FnZPositiveCones.External.CircularExpandedSeparation

@[expose] public section

/-! Finite closed-arc descriptions of the actual enlarged domains. -/
namespace FnZPositiveCones.CircularDynamics

/-- A compact connected piece avoiding the cut is a genuine closed circle arc.
An empty piece is represented by an empty real interval. -/
theorem compact_preconnected_circle_eq_arc (S : Set StandardCircle)
    (hc : IsCompact S) (hp : IsPreconnected S) (hzero : 0 ∉ S) :
    ∃ a b : ℝ, S = closedCircleArc a b := by
  classical
  by_cases hn : S.Nonempty
  · let K := circleCoordinate '' S
    have hcont : ContinuousOn circleCoordinate S := fun x hx =>
      (continuousAt_circleCoordinate (fun he => hzero (he ▸ hx))).continuousWithinAt
    have hKc : IsCompact K := hc.image_of_continuousOn hcont
    have hKconn : IsConnected K := (show IsConnected S from ⟨hn, hp⟩).image _ hcont
    have he := eq_Icc_of_connected_compact hKconn hKc
    refine ⟨sInf K, sSup K, ?_⟩
    have hback : (fun x : ℝ => (x : StandardCircle)) '' K = S := by
      dsimp only [K]
      rw [Set.image_image]
      simp only [coe_circleCoordinate, Set.image_id']
    calc
      S = (fun x : ℝ => (x : StandardCircle)) '' K := hback.symm
      _ = (fun x : ℝ => (x : StandardCircle)) '' Set.Icc (sInf K) (sSup K) :=
        congrArg (fun T : Set ℝ => (fun x : ℝ => (x : StandardCircle)) '' T) he
      _ = closedCircleArc (sInf K) (sSup K) := rfl
  · refine ⟨1, 0, ?_⟩
    rw [Set.not_nonempty_iff_eq_empty.mp hn, closedCircleArc,
      Set.Icc_eq_empty_of_lt (by norm_num : (0 : ℝ) < 1), Set.image_empty]

universe u
variable {ι : Type u} [DecidableEq ι] [Nonempty ι] [Finite ι]
variable {C : CircularGroupOrder (FreeGroup ι)} (R : CircularRealization C)

/-- A terminal principal-gap piece is a real closed arc in the chart avoiding
zero. This follows from its actual continuous image, not an assumed endpoint map. -/
theorem principal_right_piece_eq_arc (h : FreeGroup ι) (hh : C.IsSuccessor h)
    (hsep : ∀ s t, s ≠ t →
      Disjoint (closure (letterOrbit (realizationGenerators R) 0 s))
        (closure (letterOrbit (realizationGenerators R) 0 t)))
    (j : Fin (FreeGroup.norm h)) : ∃ a b : ℝ,
    principalGapChart R h j.castSucc '' Set.Icc (principalGapCut _ j) 1 = closedCircleArc a b := by
  apply compact_preconnected_circle_eq_arc
  · exact isCompact_Icc.image (principalGapChart_continuous R h _)
  · exact isPreconnected_Icc.image _ (principalGapChart_continuous R h _).continuousOn
  · rintro ⟨t, ht, he⟩
    apply base_not_mem_expandedFirstLetterDomain R h hh hsep (successorLetter h j)
    exact he ▸ mem_expandAlongGapChain_right _ _ _ _ j ht

/-- The initial principal-gap piece has the same checked arc representation. -/
theorem principal_left_piece_eq_arc (h : FreeGroup ι) (hh : C.IsSuccessor h)
    (hsep : ∀ s t, s ≠ t →
      Disjoint (closure (letterOrbit (realizationGenerators R) 0 s))
        (closure (letterOrbit (realizationGenerators R) 0 t)))
    (j : Fin (FreeGroup.norm h)) : ∃ a b : ℝ,
    principalGapChart R h j.succ '' Set.Icc 0 (principalGapCut _ j) = closedCircleArc a b := by
  apply compact_preconnected_circle_eq_arc
  · exact isCompact_Icc.image (principalGapChart_continuous R h _)
  · exact isPreconnected_Icc.image _ (principalGapChart_continuous R h _).continuousOn
  · rintro ⟨t, ht, he⟩
    apply base_not_mem_expandedFirstLetterDomain R h hh hsep
      (PingPong.inverseLetter (successorLetter h j))
    exact he ▸ mem_expandAlongGapChain_left _ _ _ _ j ht

/-- The actual expanded domain is a finite union of genuine closed circle arcs. -/
theorem expandedFirstLetterDomain_finite_arcs (h : FreeGroup ι) (hh : C.IsSuccessor h)
    (hsep : ∀ s t, s ≠ t →
      Disjoint (closure (letterOrbit (realizationGenerators R) 0 s))
        (closure (letterOrbit (realizationGenerators R) 0 t))) (s : ι × Bool) :
    ∃ F : Finset (ℝ × ℝ), expandedFirstLetterDomain R h s =
      ⋃ p ∈ F, closedCircleArc p.1 p.2 := by
  classical
  have hfree : Function.Injective (fun g => FreeGroup.lift (realizationGenerators R) g 0) := by
    simpa only [realizationGenerators_lift] using R.orbit_injective
  have hc : ∀ s, Continuous (letterPerm (realizationGenerators R) s) := by
    intro s
    rw [realizationGenerators_letter]
    exact R.action_continuous _
  have hbase := base_not_mem_colorClosures_of_separated _ _ hfree hc hsep
  obtain ⟨F, hF⟩ := firstLetterDomain_finite_arcs (realizationGenerators R) hsep hbase s
  choose ar br hr using principal_right_piece_eq_arc R h hh hsep
  choose al bl hl using principal_left_piece_eq_arc R h hh hsep
  let Jr : Finset (Fin (FreeGroup.norm h)) := Finset.univ.filter (fun j => successorLetter h j = s)
  let Jl : Finset (Fin (FreeGroup.norm h)) := Finset.univ.filter (fun j => PingPong.inverseLetter (successorLetter h j) = s)
  let Fr := Jr.image (fun j => (ar j, br j))
  let Fl := Jl.image (fun j => (al j, bl j))
  refine ⟨F ∪ Fr ∪ Fl, ?_⟩
  ext x
  constructor
  · rintro ((hx | ⟨j, hj, t, ht, rfl⟩) | ⟨j, hj, t, ht, rfl⟩)
    · rw [hF] at hx
      obtain ⟨p, hp, hx⟩ := Set.mem_iUnion₂.mp hx
      exact Set.mem_iUnion₂.mpr ⟨p, Finset.mem_union_left _ (Finset.mem_union_left _ hp), hx⟩
    · have hjr : j ∈ Jr := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩
      have hpr : (ar j, br j) ∈ Fr := Finset.mem_image.mpr ⟨j, hjr, rfl⟩
      exact Set.mem_iUnion₂.mpr ⟨(ar j, br j),
        Finset.mem_union_left _ (Finset.mem_union_right _ hpr), hr j ▸ ⟨t, ht, rfl⟩⟩
    · have hjl : j ∈ Jl := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩
      have hpl : (al j, bl j) ∈ Fl := Finset.mem_image.mpr ⟨j, hjl, rfl⟩
      exact Set.mem_iUnion₂.mpr ⟨(al j, bl j),
        Finset.mem_union_right _ hpl, hl j ▸ ⟨t, ht, rfl⟩⟩
  · rintro hx
    obtain ⟨p, hp, hx⟩ := Set.mem_iUnion₂.mp hx
    rcases Finset.mem_union.mp hp with hp | hp
    · rcases Finset.mem_union.mp hp with hp | hp
      · apply subset_expandAlongGapChain _ _ _ _ _
        rw [hF]
        exact Set.mem_iUnion₂.mpr ⟨p, hp, hx⟩
      · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hp
        have hjs := (Finset.mem_filter.mp hj).2
        rw [← hr j] at hx
        obtain ⟨t, ht, rfl⟩ := hx
        exact Or.inl (Or.inr ⟨j, hjs, t, ht, rfl⟩)
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hp
      have hjs := (Finset.mem_filter.mp hj).2
      rw [← hl j] at hx
      obtain ⟨t, ht, rfl⟩ := hx
      exact Or.inr ⟨j, hjs, t, ht, rfl⟩

end FnZPositiveCones.CircularDynamics
