module

public import FnZPositiveCones.External.CircularExpandedDomains
public import Mathlib.Topology.Algebra.GroupWithZero

@[expose] public section

/-! Regularity of the actual gap enlargement. Nondegenerate added arcs thicken
the isolated orbit points; degenerate raw color components are not discarded. -/
namespace FnZPositiveCones.CircularDynamics

/-- A nondegenerate interval under a continuous open map lies in the closure
of the interior of any set containing its image. -/
theorem image_Icc_subset_closure_interior {X : Type*} [TopologicalSpace X]
    (f : ℝ → X) (hc : Continuous f) (ho : IsOpenMap f)
    {a b : ℝ} (hab : a < b) (E : Set X) (hE : f '' Set.Icc a b ⊆ E) :
    f '' Set.Icc a b ⊆ closure (interior E) := by
  have hi : f '' Set.Ioo a b ⊆ interior E := (ho _ isOpen_Ioo).subset_interior_iff.mpr
    ((Set.image_mono Set.Ioo_subset_Icc_self).trans hE)
  calc
    f '' Set.Icc a b = f '' closure (Set.Ioo a b) := by rw [closure_Ioo hab.ne]
    _ ⊆ closure (f '' Set.Ioo a b) := image_closure_subset_closure_image hc
    _ ⊆ closure (interior E) := closure_mono hi

/-- A filled real color domain inherits regularity from its colored points;
nondegenerate filled intervals provide their own interior. -/
theorem image_colorFilledHull_subset_closure_interior {X : Type*} [TopologicalSpace X]
    {D : Type*} (K : Set ℝ) (color : ℝ → D) (c : D)
    (f : ℝ → X) (hc : Continuous f) (ho : IsOpenMap f) (E : Set X)
    (hE : f '' colorFilledHull K color c ⊆ E)
    (hpoints : ∀ x ∈ K, color x = c → f x ∈ closure (interior E)) :
    f '' colorFilledHull K color c ⊆ closure (interior E) := by
  rintro _ ⟨x, ⟨a, ha, b, hb, hax, hxb, hm⟩, rfl⟩
  have hab : a ≤ b := hax.trans hxb
  rcases eq_or_lt_of_le hab with he | he
  · have hxa : x = a := le_antisymm (by simpa only [← he] using hxb) hax
    subst x
    exact hpoints a ha (hm a ha ⟨le_rfl, hab⟩)
  · apply image_Icc_subset_closure_interior f hc ho he E ?_ ⟨x, ⟨hax, hxb⟩, rfl⟩
    rintro _ ⟨y, hy, rfl⟩
    exact hE ⟨y, ⟨a, ha, b, hb, hy.1, hy.2, hm⟩, rfl⟩

universe u
variable {ι : Type u} [DecidableEq ι]
variable {C : CircularGroupOrder (FreeGroup ι)} (R : CircularRealization C)

/-- The actual gap parameter is an open map: multiplication by its positive
length, followed by the quotient map and the action homeomorphism. -/
theorem principalGapChart_isOpenMap (h : FreeGroup ι) (hh : C.IsSuccessor h)
    (i : Fin (FreeGroup.norm h + 1)) : IsOpenMap (principalGapChart R h i) := by
  have hn := (R.representativeOrbit_pos hh).ne'
  exact (R.actionHomeomorph _).isOpenMap.comp
    (QuotientAddGroup.isOpenMap_coe.comp (Homeomorph.mulRight₀ _ hn).isOpenMap)

variable [Nonempty ι] [Finite ι]

omit [Finite ι] in
/-- Every right-hand added closed arc is approximated by the interior of the
expanded domain, including its endpoints. -/
theorem right_addedArc_subset_closure_interior (h : FreeGroup ι) (hh : C.IsSuccessor h)
    (j : Fin (FreeGroup.norm h)) :
    principalGapChart R h j.castSucc '' Set.Icc (principalGapCut (FreeGroup.norm h) j) 1 ⊆
      closure (interior (expandedFirstLetterDomain R h (successorLetter h j))) := by
  apply image_Icc_subset_closure_interior _ (principalGapChart_continuous R h _)
    (principalGapChart_isOpenMap R h hh _) (principalGapCut_mem _ _).2
  rintro _ ⟨t, ht, rfl⟩
  exact mem_expandAlongGapChain_right _ _ _ _ j ht

omit [Finite ι] in
/-- Every left-hand added closed arc is likewise approximated by the interior. -/
theorem left_addedArc_subset_closure_interior (h : FreeGroup ι) (hh : C.IsSuccessor h)
    (j : Fin (FreeGroup.norm h)) :
    principalGapChart R h j.succ '' Set.Icc 0 (principalGapCut (FreeGroup.norm h) j) ⊆
      closure (interior (expandedFirstLetterDomain R h
        (PingPong.inverseLetter (successorLetter h j)))) := by
  apply image_Icc_subset_closure_interior _ (principalGapChart_continuous R h _)
    (principalGapChart_isOpenMap R h hh _) (principalGapCut_mem _ _).1
  rintro _ ⟨t, ht, rfl⟩
  exact mem_expandAlongGapChain_left _ _ _ _ j ht

omit [DecidableEq ι] [Nonempty ι] [Finite ι] in
/-- The left endpoint is a limit of its actual successor gap. -/
theorem orbit_mem_closure_circleGap (h : FreeGroup ι) (hh : C.IsSuccessor h)
    (g : FreeGroup ι) : R.action g 0 ∈ closure (R.circleGap h g) := by
  have hr := R.representativeOrbit_pos hh
  have hzero : (0 : ℝ) ∈ closure (Set.Ioo 0
      (OrderedActions.representativeOrbit R.realLift R.positive R.cofinal h)) := by
    rw [closure_Ioo hr.ne]
    exact ⟨le_rfl, hr.le⟩
  have hq : ((0 : ℝ) : StandardCircle) ∈ closure
      ((fun x : ℝ => (x : StandardCircle)) '' Set.Ioo 0
        (OrderedActions.representativeOrbit R.realLift R.positive R.cofinal h)) :=
    mem_closure_image (show Continuous (fun x : ℝ => (x : StandardCircle)) from
      AddCircle.continuous_mk' (1 : ℝ)).continuousAt hzero
  have hg := mem_closure_image (R.action_continuous g).continuousAt hq
  simpa only [AddCircle.coe_zero, CircularRealization.circleGap] using hg

omit [Finite ι] in
/-- Every colored orbit point is approximated by the interior of its expanded
domain. Principal gaps use the explicit cutoff arc; other gaps are filled. -/
theorem letterOrbit_subset_closure_interior_expanded (h : FreeGroup ι)
    (hh : C.IsSuccessor h)
    (hsep : ∀ s t, s ≠ t →
      Disjoint (closure (letterOrbit (realizationGenerators R) 0 s))
        (closure (letterOrbit (realizationGenerators R) 0 t))) (s : ι × Bool) :
    letterOrbit (realizationGenerators R) 0 s ⊆
      closure (interior (expandedFirstLetterDomain R h s)) := by
  rintro _ ⟨w, hw, rfl⟩
  let g := FreeGroup.mk (s :: w)
  have hgword : g.toWord = s :: w := by
    rw [FreeGroup.toWord_mk, hw.reduce_eq]
  have heval : evalWord (realizationGenerators R) (s :: w) 0 = R.action g 0 := by
    rw [← lift_mk_apply, realizationGenerators_lift]
  rw [heval]
  by_cases hp : PrincipalGapLabel h g
  · obtain ⟨i, hi⟩ := (principalGapPrefixEquiv h).surjective ⟨g, hp⟩
    have he : inversePrefix h i = g := congrArg Subtype.val hi
    revert he
    induction i using Fin.cases with
    | zero =>
      intro he
      have hg1 : g = 1 := he.symm.trans (by
        change (1 : FreeGroup ι)⁻¹ = 1
        exact inv_one)
      rw [hg1, FreeGroup.toWord_one] at hgword
      contradiction
    | succ j =>
      intro he
      have hheads := inversePrefix_successor_word h j
      rw [he, hgword] at hheads
      have hs : s = PingPong.inverseLetter (successorLetter h j) := (List.cons.inj hheads).1
      rw [hs]
      apply left_addedArc_subset_closure_interior R h hh j
      refine ⟨0, ⟨le_rfl, (principalGapCut_mem _ _).1.le⟩, ?_⟩
      simp only [principalGapChart, zero_mul, AddCircle.coe_zero, he]
  · obtain ⟨t, u, v, hgu, hgh⟩ := nonprincipal_same_heads h g hp
    have ht : t = s := (List.cons.inj (hgu.symm.trans hgword)).1
    subst t
    have hsub : R.circleGap h g ⊆ expandedFirstLetterDomain R h s :=
      (circleGap_subset_firstLetterDomain R h hh g s hsep
        (realization_head_mem R g s u hgu)
        (realization_head_mem R (g * h) s v hgh)).trans
          (subset_expandAlongGapChain _ _ _ _ _)
    have hint : R.circleGap h g ⊆ interior (expandedFirstLetterDomain R h s) :=
      (R.circleGap_isOpen h g).subset_interior_iff.mpr hsub
    exact closure_mono hint (orbit_mem_closure_circleGap R h hh g)

/-- The raw domain, including singleton components, is approximated by the
interior of the enlarged domain. -/
theorem firstLetterDomain_subset_closure_interior_expanded (h : FreeGroup ι)
    (hh : C.IsSuccessor h)
    (hsep : ∀ s t, s ≠ t →
      Disjoint (closure (letterOrbit (realizationGenerators R) 0 s))
        (closure (letterOrbit (realizationGenerators R) 0 t))) (s : ι × Bool) :
    firstLetterDomain (realizationGenerators R) 0 s ⊆
      closure (interior (expandedFirstLetterDomain R h s)) := by
  let ρ := realizationGenerators R
  let K := coloredOrbitClosure ρ 0
  have hfree : Function.Injective (fun g => FreeGroup.lift ρ g 0) := by
    simpa only [ρ, realizationGenerators_lift] using R.orbit_injective
  have hc : ∀ s, Continuous (letterPerm ρ s) := by
    intro s
    change Continuous (letterPerm (realizationGenerators R) s)
    rw [realizationGenerators_letter]
    exact R.action_continuous _
  have hbase := base_not_mem_colorClosures_of_separated ρ 0 hfree hc hsep
  have hzero : 0 ∉ K := base_not_mem_coloredOrbitClosure ρ 0 hbase
  have he : firstLetterDomain ρ 0 s =
      (fun x : ℝ => (x : StandardCircle)) ''
        colorFilledHull (circleCoordinate '' K)
          (fun x : ℝ => orbitClosureColor ρ 0 (x : StandardCircle)) s :=
    circularColorFilledHull_eq_image K hzero _ s
  change firstLetterDomain ρ 0 s ⊆ _
  rw [he]
  apply image_colorFilledHull_subset_closure_interior _ _ _
    (fun x : ℝ => (x : StandardCircle))
    (AddCircle.continuous_mk' (1 : ℝ)) QuotientAddGroup.isOpenMap_coe
  · rw [← he]
    exact subset_expandAlongGapChain _ _ _ _ _
  · rintro _ ⟨p, hp, rfl⟩ hcolor
    simp only [coe_circleCoordinate] at hcolor ⊢
    have hm := mem_closure_letterOrbit_of_mem_coloredOrbitClosure ρ 0 hp
    rw [hcolor] at hm
    exact closure_minimal (letterOrbit_subset_closure_interior_expanded R h hh hsep s)
      isClosed_closure hm

/-- The enlargement is regular closed. In particular, isolated raw color
points have not introduced singleton components in the final domain. -/
theorem expandedFirstLetterDomain_regularClosed (h : FreeGroup ι)
    (hh : C.IsSuccessor h)
    (hsep : ∀ s t, s ≠ t →
      Disjoint (closure (letterOrbit (realizationGenerators R) 0 s))
        (closure (letterOrbit (realizationGenerators R) 0 t))) (s : ι × Bool) :
    closure (interior (expandedFirstLetterDomain R h s)) = expandedFirstLetterDomain R h s := by
  apply Set.Subset.antisymm
  · exact closure_minimal interior_subset (isCompact_expandedFirstLetterDomain R h hsep s).isClosed
  · rintro x ((hx | ⟨j, rfl, t, ht, rfl⟩) | ⟨j, rfl, t, ht, rfl⟩)
    · exact firstLetterDomain_subset_closure_interior_expanded R h hh hsep s hx
    · exact right_addedArc_subset_closure_interior R h hh j ⟨t, ht, rfl⟩
    · exact left_addedArc_subset_closure_interior R h hh j ⟨t, ht, rfl⟩

end FnZPositiveCones.CircularDynamics
