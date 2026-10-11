module

public import FnZPositiveCones.External.CircularExpandedOpen

@[expose] public section

/-! Separation of the actual principal-gap enlargement. -/
namespace FnZPositiveCones.CircularDynamics

/-- If an open circular gap crosses the interior of a closed segment while
both segment endpoints avoid the gap, both gap endpoints lie in the segment. -/
theorem circularGap_endpoints_mem_segment {X : Type*} [CircularOrder X]
    {a b u v x : X} (haxb : sbtw a x b) (huxv : sbtw u x v)
    (hu : ¬ sbtw a u b) (hv : ¬ sbtw a v b) :
    a ∈ circularClosedSegment u v ∧ b ∈ circularClosedSegment u v := by
  have huv : u ≠ v := by intro he; subst v; exact sbtw_irrefl_left_right huxv
  constructor
  · by_cases hau : a = u
    · exact Or.inl hau
    by_cases hav : a = v
    · exact Or.inr (Or.inl hav)
    rcases CircularCarry.strict_or_reverse (Ne.symm hau) hav huv.symm with h | h
    · exact Or.inr (Or.inr h)
    · exact False.elim (hu ((huxv.cyclic_left.trans_left h).cyclic_left.trans_right haxb))
  · by_cases hbu : b = u
    · exact Or.inl hbu
    by_cases hbv : b = v
    · exact Or.inr (Or.inl hbv)
    rcases CircularCarry.strict_or_reverse (Ne.symm hbu) hbv huv.symm with h | h
    · exact Or.inr (Or.inr h)
    · exact False.elim (hv (haxb.trans_left (h.cyclic_left.trans_left huxv).cyclic_left))

universe u
variable {ι : Type u} [DecidableEq ι] [Nonempty ι] [Finite ι]
variable {C : CircularGroupOrder (FreeGroup ι)} (R : CircularRealization C)

/-- A principal successor gap is disjoint from every raw filled color domain.
The two identity-endpoint cases are included explicitly. -/
theorem principalGap_disjoint_firstLetterDomain (h : FreeGroup ι) (hh : C.IsSuccessor h)
    (hsep : ∀ s t, s ≠ t →
      Disjoint (closure (letterOrbit (realizationGenerators R) 0 s))
        (closure (letterOrbit (realizationGenerators R) 0 t)))
    (g : FreeGroup ι) (hg : PrincipalGapLabel h g) (s : ι × Bool) :
    Disjoint (R.circleGap h g) (firstLetterDomain (realizationGenerators R) 0 s) := by
  let ρ := realizationGenerators R
  let K := coloredOrbitClosure ρ 0
  have hKsub : K ⊆ closure (Set.range (fun g => R.action g 0)) := by
    rw [← realizationGenerators_lift R, orbitClosure_eq_base_union_colorClosures]
    exact Set.subset_union_right
  apply Set.disjoint_left.mpr
  rintro x hx ⟨u, hu, v, hv, hseg, hzero, hmono⟩
  have hgap : sbtw (R.action g 0) x (R.action (g * h) 0) :=
    by rw [circleGap_eq_sbtw R h g] at hx; exact hx
  have hout (y : StandardCircle) (hy : y ∈ K) :
      ¬ sbtw (R.action g 0) y (R.action (g * h) 0) := by
    intro hygap
    exact Set.disjoint_left.mp (R.circleGap_disjoint_orbitClosure hh g)
      ((circleGap_eq_sbtw R h g).symm ▸ hygap) (hKsub hy)
  have huvx : sbtw u x v := by
    rcases hseg with he | he | hs
    · subst x
      exact False.elim (hout u hu hgap)
    · subst x
      exact False.elim (hout v hv hgap)
    · exact hs
  obtain ⟨ha, hb⟩ := circularGap_endpoints_mem_segment hgap huvx (hout u hu) (hout v hv)
  rcases hg with rfl | hg | ⟨a, b, w, z, hga, hgb, hab⟩
  · exact hzero (by simpa only [map_one, Equiv.Perm.one_apply] using ha)
  · exact hzero (by simpa only [hg, map_one, Equiv.Perm.one_apply] using hb)
  · have hca : R.action g 0 ∈ closure (letterOrbit ρ 0 a) :=
      subset_closure (realization_head_mem R g a w hga)
    have hcb : R.action (g * h) 0 ∈ closure (letterOrbit ρ 0 b) :=
      subset_closure (realization_head_mem R (g * h) b z hgb)
    have has := hmono (R.action g 0) (Set.mem_iUnion.mpr ⟨a, hca⟩) ha
    have hbs := hmono (R.action (g * h) 0) (Set.mem_iUnion.mpr ⟨b, hcb⟩) hb
    rw [orbitClosureColor_eq_of_mem ρ 0 hsep hca] at has
    rw [orbitClosureColor_eq_of_mem ρ 0 hsep hcb] at hbs
    exact hab (has.trans hbs.symm)

omit [Nonempty ι] [Finite ι] in
@[simp] theorem principalGapChart_zero (h : FreeGroup ι) (i : Fin (FreeGroup.norm h + 1)) :
    principalGapChart R h i 0 = R.action (inversePrefix h i) 0 := by
  simp only [principalGapChart, zero_mul, AddCircle.coe_zero]

omit [Nonempty ι] [Finite ι] in
@[simp] theorem principalGapChart_one (h : FreeGroup ι) (i : Fin (FreeGroup.norm h + 1)) :
    principalGapChart R h i 1 = R.action (inversePrefix h i * h) 0 := by
  rw [principalGapChart, one_mul, ← realization_orbit_representative R h,
    map_mul, Equiv.Perm.mul_apply]

/-- The actual right endpoint of each added terminal subarc has its assigned
first-letter color. -/
theorem principalGapChart_one_mem_raw (h : FreeGroup ι)
    (hsep : ∀ s t, s ≠ t →
      Disjoint (closure (letterOrbit (realizationGenerators R) 0 s))
        (closure (letterOrbit (realizationGenerators R) 0 t)))
    (j : Fin (FreeGroup.norm h)) :
    principalGapChart R h j.castSucc 1 ∈ firstLetterDomain (realizationGenerators R) 0
      (successorLetter h j) := by
  have hfree : Function.Injective (fun g => FreeGroup.lift (realizationGenerators R) g 0) := by
    simpa only [realizationGenerators_lift] using R.orbit_injective
  have hc : ∀ s, Continuous (letterPerm (realizationGenerators R) s) := by
    intro s
    rw [realizationGenerators_letter]
    exact R.action_continuous _
  have hbase := base_not_mem_colorClosures_of_separated _ _ hfree hc hsep
  rw [principalGapChart_one]
  apply closure_letterOrbit_subset_firstLetterDomain _ hsep hbase _
  exact subset_closure (realization_head_mem R _ _ _ (inversePrefix_right_word h j))

/-- The left endpoint of each initial subarc has the inverse-letter color
assigned by the prefix chain. -/
theorem principalGapChart_zero_mem_raw (h : FreeGroup ι)
    (hsep : ∀ s t, s ≠ t →
      Disjoint (closure (letterOrbit (realizationGenerators R) 0 s))
        (closure (letterOrbit (realizationGenerators R) 0 t)))
    (j : Fin (FreeGroup.norm h)) :
    principalGapChart R h j.succ 0 ∈ firstLetterDomain (realizationGenerators R) 0
      (PingPong.inverseLetter (successorLetter h j)) := by
  have hfree : Function.Injective (fun g => FreeGroup.lift (realizationGenerators R) g 0) := by
    simpa only [realizationGenerators_lift] using R.orbit_injective
  have hc : ∀ s, Continuous (letterPerm (realizationGenerators R) s) := by
    intro s
    rw [realizationGenerators_letter]
    exact R.action_continuous _
  have hbase := base_not_mem_colorClosures_of_separated _ _ hfree hc hsep
  rw [principalGapChart_zero]
  apply closure_letterOrbit_subset_firstLetterDomain _ hsep hbase _
  exact subset_closure (realization_head_mem R _ _ _ (inversePrefix_successor_word h j))

/-- Every added endpoint is already in the raw domain. Remaining added points
lie strictly inside the corresponding actual complementary gap. -/
theorem mem_expandedFirstLetterDomain_cases (h : FreeGroup ι)
    (hsep : ∀ s t, s ≠ t →
      Disjoint (closure (letterOrbit (realizationGenerators R) 0 s))
        (closure (letterOrbit (realizationGenerators R) 0 t)))
    {s : ι × Bool} {x : StandardCircle} (hx : x ∈ expandedFirstLetterDomain R h s) :
    x ∈ firstLetterDomain (realizationGenerators R) 0 s ∨
      (∃ j, successorLetter h j = s ∧ ∃ t ∈ Set.Ico (principalGapCut _ j) 1,
        principalGapChart R h j.castSucc t = x) ∨
      (∃ j, PingPong.inverseLetter (successorLetter h j) = s ∧
        ∃ t ∈ Set.Ioc 0 (principalGapCut _ j), principalGapChart R h j.succ t = x) := by
  rcases hx with (hx | ⟨j, rfl, t, ht, rfl⟩) | ⟨j, rfl, t, ht, rfl⟩
  · exact Or.inl hx
  · rcases eq_or_lt_of_le ht.2 with rfl | ht1
    · exact Or.inl (principalGapChart_one_mem_raw R h hsep j)
    · exact Or.inr (Or.inl ⟨j, rfl, t, ⟨ht.1, ht1⟩, rfl⟩)
  · rcases eq_or_lt_of_le ht.1 with ht0 | ht0
    · subst t
      exact Or.inl (principalGapChart_zero_mem_raw R h hsep j)
    · exact Or.inr (Or.inr ⟨j, rfl, t, ⟨ht0, ht.2⟩, rfl⟩)

omit [Nonempty ι] [Finite ι] in
/-- A principal gap chart is injective on its whole closed parameter interval. -/
theorem principalGapChart_injOn (h : FreeGroup ι) (hh : C.IsSuccessor h)
    (i : Fin (FreeGroup.norm h + 1)) :
    Set.InjOn (principalGapChart R h i) (Set.Icc (0 : ℝ) 1) := by
  let r := OrderedActions.representativeOrbit R.realLift R.positive R.cofinal h
  have hr : 0 < r := R.representativeOrbit_pos hh
  have hr1 : r < 1 := (OrderedActions.representativeOrbit_mem R.realLift R.base_zero
    R.central_translation R.positive R.cofinal h).2
  have hmem (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : t * r ∈ Set.Ico (0 : ℝ) (0 + 1) := by
    refine ⟨mul_nonneg ht.1 hr.le, ?_⟩
    have hm := mul_le_mul_of_nonneg_right ht.2 hr.le
    have hm' : t * r ≤ r := by simpa only [one_mul] using hm
    simpa only [zero_add] using hm'.trans_lt hr1
  intro a ha b hb he
  have hec : ((a * r : ℝ) : StandardCircle) = ((b * r : ℝ) : StandardCircle) :=
    (R.action (inversePrefix h i)).injective he
  have her := (AddCircle.coe_eq_coe_iff_of_mem_Ico (hmem a ha) (hmem b hb)).mp hec
  nlinarith

omit [Nonempty ι] [Finite ι] in
/-- Distinct principal charts have disjoint interiors; equality determines both
the prefix index and the real parameter. -/
theorem principalGapChart_eq_iff (h : FreeGroup ι) (hh : C.IsSuccessor h)
    (i j : Fin (FreeGroup.norm h + 1)) {a b : ℝ}
    (ha : a ∈ Set.Ioo (0 : ℝ) 1) (hb : b ∈ Set.Ioo (0 : ℝ) 1) :
    principalGapChart R h i a = principalGapChart R h j b ↔ i = j ∧ a = b := by
  constructor
  · intro he
    have hi : principalGapChart R h i a ∈ R.circleGap h (inversePrefix h i) := by
      rw [← principalGapChart_image R h hh i]
      exact ⟨a, ha, rfl⟩
    have hj : principalGapChart R h j b ∈ R.circleGap h (inversePrefix h j) := by
      rw [← principalGapChart_image R h hh j]
      exact ⟨b, hb, rfl⟩
    have hg : inversePrefix h i = inversePrefix h j := by
      by_contra hne
      exact Set.disjoint_left.mp (R.circleGap_disjoint hh hne) hi (he ▸ hj)
    have hij : i = j := Fin.ext (by simpa only [inversePrefix_norm] using congrArg FreeGroup.norm hg)
    subst j
    exact ⟨rfl, principalGapChart_injOn R h hh i ⟨ha.1.le, ha.2.le⟩ ⟨hb.1.le, hb.2.le⟩ he⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- The actual enlarged closed domains are pairwise disjoint. Increasing cuts
separate the two portions assigned to different colors in an intermediate gap. -/
theorem expandedFirstLetterDomain_disjoint (h : FreeGroup ι) (hh : C.IsSuccessor h)
    (hsep : ∀ s t, s ≠ t →
      Disjoint (closure (letterOrbit (realizationGenerators R) 0 s))
        (closure (letterOrbit (realizationGenerators R) 0 t)))
    {s t : ι × Bool} (hst : s ≠ t) :
    Disjoint (expandedFirstLetterDomain R h s) (expandedFirstLetterDomain R h t) := by
  have hfree : Function.Injective (fun g => FreeGroup.lift (realizationGenerators R) g 0) := by
    simpa only [realizationGenerators_lift] using R.orbit_injective
  have hc : ∀ s, Continuous (letterPerm (realizationGenerators R) s) := by
    intro s
    rw [realizationGenerators_letter]
    exact R.action_continuous _
  have hbase := base_not_mem_colorClosures_of_separated _ _ hfree hc hsep
  have hraw (i : Fin (FreeGroup.norm h + 1)) (a : ℝ) (ha : a ∈ Set.Ioo (0 : ℝ) 1)
      (c : ι × Bool) : principalGapChart R h i a ∉ firstLetterDomain (realizationGenerators R) 0 c := by
    intro hm
    apply Set.disjoint_left.mp (principalGap_disjoint_firstLetterDomain R h hh hsep
      (inversePrefix h i) (inversePrefix_principal h i) c) ?_ hm
    rw [← principalGapChart_image R h hh i]
    exact ⟨a, ha, rfl⟩
  have hright (j : Fin (FreeGroup.norm h)) {a : ℝ}
      (ha : a ∈ Set.Ico (principalGapCut _ j) 1) : a ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨(principalGapCut_mem _ j).1.trans_le ha.1, ha.2⟩
  have hleft (j : Fin (FreeGroup.norm h)) {a : ℝ}
      (ha : a ∈ Set.Ioc 0 (principalGapCut _ j)) : a ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨ha.1, ha.2.trans_lt (principalGapCut_mem _ j).2⟩
  apply Set.disjoint_left.mpr
  intro x hxs hxt
  have hs := mem_expandedFirstLetterDomain_cases R h hsep hxs
  have ht := mem_expandedFirstLetterDomain_cases R h hsep hxt
  rcases hs with hs | ⟨j, hjs, a, ha, hax⟩ | ⟨j, hjs, a, ha, hax⟩
  · rcases ht with ht | ⟨k, hkt, b, hb, hbx⟩ | ⟨k, hkt, b, hb, hbx⟩
    · exact Set.disjoint_left.mp (firstLetterDomain_disjoint _ hbase hst) hs ht
    · exact hraw k.castSucc b (hright k hb) s (hbx.symm ▸ hs)
    · exact hraw k.succ b (hleft k hb) s (hbx.symm ▸ hs)
  · rcases ht with ht | ⟨k, hkt, b, hb, hbx⟩ | ⟨k, hkt, b, hb, hbx⟩
    · exact hraw j.castSucc a (hright j ha) t (hax.symm ▸ ht)
    · obtain ⟨hjk, _⟩ := (principalGapChart_eq_iff R h hh j.castSucc k.castSucc
        (hright j ha) (hright k hb)).mp (hax.trans hbx.symm)
      have hjk' : j = k := Fin.ext (by have he := congrArg (fun q : Fin (FreeGroup.norm h + 1) => q.val) hjk; exact he)
      exact hst (hjs.symm.trans (hjk' ▸ hkt))
    · obtain ⟨hjk, hab⟩ := (principalGapChart_eq_iff R h hh j.castSucc k.succ
        (hright j ha) (hleft k hb)).mp (hax.trans hbx.symm)
      have hkj : k < j := by have he := congrArg Fin.val hjk; change k.val < j.val; simp only [Fin.val_castSucc, Fin.val_succ] at he; omega
      have hcut := principalGapCut_strictMono (FreeGroup.norm h) hkj
      linarith [ha.1, hb.2]
  · rcases ht with ht | ⟨k, hkt, b, hb, hbx⟩ | ⟨k, hkt, b, hb, hbx⟩
    · exact hraw j.succ a (hleft j ha) t (hax.symm ▸ ht)
    · obtain ⟨hjk, hab⟩ := (principalGapChart_eq_iff R h hh j.succ k.castSucc
        (hleft j ha) (hright k hb)).mp (hax.trans hbx.symm)
      have hjk' : j < k := by have he := congrArg Fin.val hjk; change j.val < k.val; simp only [Fin.val_castSucc, Fin.val_succ] at he; omega
      have hcut := principalGapCut_strictMono (FreeGroup.norm h) hjk'
      linarith [ha.2, hb.1]
    · obtain ⟨hjk, _⟩ := (principalGapChart_eq_iff R h hh j.succ k.succ
        (hleft j ha) (hleft k hb)).mp (hax.trans hbx.symm)
      have hjk' : j = k := Fin.ext (by have he := congrArg Fin.val hjk; simp only [Fin.val_succ] at he; omega)
      exact hst (hjs.symm.trans (hjk' ▸ hkt))

/-- The basepoint stays outside every expanded closed domain. -/
theorem base_not_mem_expandedFirstLetterDomain (h : FreeGroup ι) (hh : C.IsSuccessor h)
    (hsep : ∀ s t, s ≠ t →
      Disjoint (closure (letterOrbit (realizationGenerators R) 0 s))
        (closure (letterOrbit (realizationGenerators R) 0 t))) (s : ι × Bool) :
    (0 : StandardCircle) ∉ expandedFirstLetterDomain R h s := by
  have hzero : (0 : StandardCircle) ∈ closure (Set.range (fun g => R.action g 0)) := by
    apply subset_closure
    exact ⟨1, by simp⟩
  have hchart (i : Fin (FreeGroup.norm h + 1)) (a : ℝ) (ha : a ∈ Set.Ioo (0 : ℝ) 1) :
      principalGapChart R h i a ≠ 0 := by
    intro he
    have hm : principalGapChart R h i a ∈ R.circleGap h (inversePrefix h i) := by
      rw [← principalGapChart_image R h hh i]
      exact ⟨a, ha, rfl⟩
    rw [he] at hm
    exact Set.disjoint_left.mp (R.circleGap_disjoint_orbitClosure hh _) hm hzero
  intro hx
  rcases mem_expandedFirstLetterDomain_cases R h hsep hx with hx |
      ⟨j, _, a, ha, he⟩ | ⟨j, _, a, ha, he⟩
  · exact base_not_mem_circularColorFilledHull _ _ _ _ hx
  · exact hchart j.castSucc a ⟨(principalGapCut_mem _ j).1.trans_le ha.1, ha.2⟩ he
  · exact hchart j.succ a ⟨ha.1, ha.2.trans_lt (principalGapCut_mem _ j).2⟩ he

/-- The actual open domains have disjoint closures. -/
theorem openExpandedDomain_disjoint_closures (h : FreeGroup ι) (hh : C.IsSuccessor h)
    (hsep : ∀ s t, s ≠ t →
      Disjoint (closure (letterOrbit (realizationGenerators R) 0 s))
        (closure (letterOrbit (realizationGenerators R) 0 t)))
    {s t : ι × Bool} (hst : s ≠ t) :
    Disjoint (closure (openExpandedDomain R h s)) (closure (openExpandedDomain R h t)) := by
  rw [closure_openExpandedDomain R h hh hsep, closure_openExpandedDomain R h hh hsep]
  exact expandedFirstLetterDomain_disjoint R h hh hsep hst

/-- The exact action normalization retains pairwise disjoint closures. -/
theorem normalizedExpandedDomain_disjoint_closures (h : FreeGroup ι) (hh : C.IsSuccessor h)
    (hsep : ∀ s t, s ≠ t →
      Disjoint (closure (letterOrbit (realizationGenerators R) 0 s))
        (closure (letterOrbit (realizationGenerators R) 0 t)))
    {s t : ι × Bool} (hst : s ≠ t) :
    Disjoint (closure (normalizedExpandedDomain R h s))
      (closure (normalizedExpandedDomain R h t)) :=
  (openExpandedDomain_disjoint_closures R h hh hsep hst).mono
    (closure_mono (normalizedExpandedDomain_subset R h hh hsep s))
    (closure_mono (normalizedExpandedDomain_subset R h hh hsep t))

/-- The free basepoint is outside the closure of every final normalized domain. -/
theorem base_not_mem_closure_normalizedExpandedDomain (h : FreeGroup ι) (hh : C.IsSuccessor h)
    (hsep : ∀ s t, s ≠ t →
      Disjoint (closure (letterOrbit (realizationGenerators R) 0 s))
        (closure (letterOrbit (realizationGenerators R) 0 t))) (s : ι × Bool) :
    (0 : StandardCircle) ∉ closure (normalizedExpandedDomain R h s) := by
  intro hx
  have he := closure_mono (normalizedExpandedDomain_subset R h hh hsep s) hx
  rw [closure_openExpandedDomain R h hh hsep] at he
  exact base_not_mem_expandedFirstLetterDomain R h hh hsep s he

/-- Each final domain is nonempty: it contains the corresponding signed
image of the free basepoint. -/
theorem normalizedExpandedDomain_nonempty (h : FreeGroup ι) (hh : C.IsSuccessor h)
    (hsep : ∀ s t, s ≠ t →
      Disjoint (closure (letterOrbit (realizationGenerators R) 0 s))
        (closure (letterOrbit (realizationGenerators R) 0 t))) (s : ι × Bool) :
    (normalizedExpandedDomain R h s).Nonempty := by
  rw [← normalizedExpandedDomain_image R h hh hsep s]
  exact ⟨letterPerm (realizationGenerators R) s 0, 0,
    base_not_mem_closure_normalizedExpandedDomain R h hh hsep _, rfl⟩

end FnZPositiveCones.CircularDynamics
