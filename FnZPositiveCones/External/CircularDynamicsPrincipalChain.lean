module

public import FnZPositiveCones.External.OrderedActionsCircleGaps
public import FnZPositiveCones.External.CircularPrincipalGapPrefixes
public import FnZPositiveCones.External.CircularDynamicsDomainTransport
public import FnZPositiveCones.External.CircularDynamicsSeparationAdapter
public import FnZPositiveCones.External.CircularDynamicsCircleFilled

@[expose] public section

/-! Actual principal successor gaps and the finite inverse-prefix chain. -/
namespace FnZPositiveCones
namespace CircularDynamics
universe u
variable {ι : Type u} [DecidableEq ι]
variable {C : CircularGroupOrder (FreeGroup ι)} (R : CircularRealization C)

/-- Generator permutations of the given, already constructed circle action. -/
noncomputable def realizationGenerators (i : ι) : Equiv.Perm (AddCircle (1 : ℝ)) :=
  R.action (FreeGroup.of i)

omit [DecidableEq ι] in
@[simp] theorem realizationGenerators_lift :
    FreeGroup.lift (realizationGenerators R) = R.action := by
  apply FreeGroup.ext_hom
  intro i
  simp only [FreeGroup.lift_apply_of]
  rfl

omit [DecidableEq ι] in
@[simp] theorem realizationGenerators_letter (s : ι × Bool) :
    letterPerm (realizationGenerators R) s = R.action (FreeGroup.mk [s]) := by
  have hh := congrArg (fun f : FreeGroup ι →* Equiv.Perm (AddCircle (1 : ℝ)) =>
    f (FreeGroup.mk [s])) (realizationGenerators_lift R)
  ext x
  have hx := Equiv.congr_fun hh x
  simpa only [lift_mk_apply, evalWord] using hx

/-- A concrete chart for each inverse-prefix translate of the successor gap. -/
noncomputable def principalGapChart (h : FreeGroup ι)
    (i : Fin (FreeGroup.norm h + 1)) (t : ℝ) : AddCircle (1 : ℝ) :=
  R.action (inversePrefix h i)
    ((t * OrderedActions.representativeOrbit R.realLift R.positive R.cofinal h : ℝ) :
      AddCircle (1 : ℝ))

def successorLetter (h : FreeGroup ι) (j : Fin (FreeGroup.norm h)) : ι × Bool :=
  h.toWord[j.val]

theorem inversePrefix_successor_word (h : FreeGroup ι) (j : Fin (FreeGroup.norm h)) :
    (inversePrefix h j.succ).toWord =
      PingPong.inverseLetter (successorLetter h j) :: (inversePrefix h j.castSucc).toWord := by
  simp only [inversePrefix, FreeGroup.toWord_inv, FreeGroup.toWord_mk,
    (prefix_reduced h _).reduce_eq]
  change FreeGroup.invRev (h.toWord.take (j.val + 1)) = _
  rw [← List.take_concat_get' h.toWord j.val j.isLt, FreeGroup.invRev_append]
  rfl

theorem inversePrefix_right_word (h : FreeGroup ι) (j : Fin (FreeGroup.norm h)) :
    (inversePrefix h j.castSucc * h).toWord =
      successorLetter h j :: h.toWord.drop (j.val + 1) := by
  rw [inversePrefix_mul_successor, FreeGroup.toWord_mk, (suffix_reduced h _).reduce_eq]
  exact List.drop_eq_getElem_cons j.isLt

/-- Only the two neighboring chain letters can cancel either gap endpoint.
Every other letter places both endpoints in its actual first-letter color. -/
theorem principalGap_other_reduced (h : FreeGroup ι)
    (i : Fin (FreeGroup.norm h + 1)) (s : ι × Bool)
    (hleft : ¬∃ j, i = j.succ ∧ s = successorLetter h j)
    (hright : ¬∃ j, i = j.castSucc ∧ s = PingPong.inverseLetter (successorLetter h j)) :
    FreeGroup.IsReduced (s :: (inversePrefix h i).toWord) ∧
      FreeGroup.IsReduced (s :: (inversePrefix h i * h).toWord) := by
  constructor
  · rcases i.eq_zero_or_eq_succ with rfl | ⟨j, rfl⟩
    · rw [show inversePrefix h (0 : Fin (FreeGroup.norm h + 1)) = 1 from inversePrefix_zero h,
        FreeGroup.toWord_one]
      exact FreeGroup.IsReduced.singleton
    · rw [inversePrefix_successor_word]
      apply reduced_cons_of_ne_inverse
      · rw [← inversePrefix_successor_word]
        exact FreeGroup.isReduced_toWord
      · intro he
        apply hleft
        refine ⟨j, rfl, ?_⟩
        have he' := congrArg PingPong.inverseLetter he
        simpa only [PingPong.inverseLetter_inverse] using he'.symm
  · induction i using Fin.lastCases with
    | last =>
        rw [show inversePrefix h (Fin.last (FreeGroup.norm h)) = h⁻¹ from inversePrefix_last h,
          inv_mul_cancel, FreeGroup.toWord_one]
        exact FreeGroup.IsReduced.singleton
    | cast j =>
        rw [inversePrefix_right_word]
        apply reduced_cons_of_ne_inverse
        · rw [← inversePrefix_right_word]
          exact FreeGroup.isReduced_toWord
        · intro he
          exact hright ⟨j, rfl, by simpa only [PingPong.inverseLetter_inverse] using
            (congrArg PingPong.inverseLetter he).symm⟩

/-- The exact inverse-letter transition between consecutive actual charts. -/
theorem principalGapChart_step (h : FreeGroup ι) (j : Fin (FreeGroup.norm h)) (t : ℝ) :
    letterPerm (realizationGenerators R) (PingPong.inverseLetter (successorLetter h j))
      (principalGapChart R h j.castSucc t) = principalGapChart R h j.succ t := by
  rw [PingPong.letterPerm_inverseLetter, realizationGenerators_letter]
  unfold principalGapChart
  rw [show inversePrefix h j.succ =
    (FreeGroup.mk [successorLetter h j])⁻¹ * inversePrefix h j.castSucc from
      inversePrefix_successor h j.val j.isLt]
  rw [map_mul, map_inv]
  rfl

/-- These charts parameterize the actual complementary gaps, not merely a
finite approximation to the orbit. -/
theorem principalGapChart_image (h : FreeGroup ι) (hh : C.IsSuccessor h)
    (i : Fin (FreeGroup.norm h + 1)) :
    principalGapChart R h i '' Set.Ioo (0 : ℝ) 1 = R.circleGap h (inversePrefix h i) := by
  have hp := R.representativeOrbit_pos hh
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨_, ⟨t * _, ⟨mul_pos ht.1 hp, ?_⟩, rfl⟩, rfl⟩
    exact (mul_lt_mul_iff_left₀ hp).mpr ht.2 |>.trans_eq (one_mul _)
  · rintro ⟨_, ⟨t, ht, rfl⟩, rfl⟩
    refine ⟨t / _, ⟨div_pos ht.1 hp, (div_lt_one hp).mpr ht.2⟩, ?_⟩
    simp only [principalGapChart, div_mul_cancel₀ _ hp.ne']

omit [DecidableEq ι] in
/-- The orbit endpoint is the projection of its actual fundamental representative. -/
theorem realization_orbit_representative (h : FreeGroup ι) :
    R.action h 0 = ((OrderedActions.representativeOrbit R.realLift R.positive R.cofinal h : ℝ) :
      AddCircle (1 : ℝ)) :=
  OrderedActions.productCircleAction_zero R.realLift R.central_translation R.positive R.cofinal h

omit [DecidableEq ι] in
/-- An actual complementary gap is exactly the oriented open interval between
its two orbit endpoints. -/
theorem circleGap_eq_sbtw (h : FreeGroup ι) (g : FreeGroup ι) :
    R.circleGap h g = {x | sbtw (R.action g 0) x (R.action (g * h) 0)} := by
  have hr := OrderedActions.representativeOrbit_mem R.realLift R.base_zero
    R.central_translation R.positive R.cofinal h
  have hc (y : AddCircle (1 : ℝ)) :
      y ∈ ((↑) : ℝ → AddCircle (1 : ℝ)) ''
        Set.Ioo 0 (OrderedActions.representativeOrbit R.realLift R.positive R.cofinal h) ↔
      sbtw (0 : AddCircle (1 : ℝ)) y (R.action h 0) := by
    rw [realization_orbit_representative R]
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact (OrderedActions.circle_sbtw_zero_iff ⟨ht.1.le, ht.2.trans hr.2⟩ hr).mpr ht
    · intro hs
      have ht := (OrderedActions.circle_sbtw_zero_iff
        (circleCoordinate_mem y) hr).mp (by simpa only [coe_circleCoordinate] using hs)
      exact ⟨circleCoordinate y, ht, coe_circleCoordinate y⟩
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hs := (hc y).mp hy
    have hp := R.action_preserves g
    simpa only [Set.mem_ofPred_eq, map_mul, Equiv.Perm.mul_apply, sbtw_iff_btw_not_btw,
      hp 0 y (R.action h 0), hp (R.action h 0) y 0] using hs
  · intro hx
    refine ⟨(R.action g).symm x, (hc _).mpr ?_, (R.action g).apply_symm_apply x⟩
    have hp := R.action_preserves g
    have hs : sbtw (R.action g 0) (R.action g ((R.action g).symm x))
        (R.action g (R.action h 0)) := by
      simpa only [Set.mem_ofPred_eq, Equiv.apply_symm_apply, map_mul, Equiv.Perm.mul_apply] using hx
    simpa only [sbtw_iff_btw_not_btw, hp 0 _ (R.action h 0), hp (R.action h 0) _ 0] using hs

omit [DecidableEq ι] in
/-- A true complementary gap with matching first-letter endpoint colors is
contained in the canonical filled domain of that color. -/
theorem circleGap_subset_firstLetterDomain [Nonempty ι]
    (h : FreeGroup ι) (hh : C.IsSuccessor h) (g : FreeGroup ι) (s : ι × Bool)
    (hsep : ∀ s t, s ≠ t →
      Disjoint (closure (letterOrbit (realizationGenerators R) 0 s))
        (closure (letterOrbit (realizationGenerators R) 0 t)))
    (hleft : R.action g 0 ∈ letterOrbit (realizationGenerators R) 0 s)
    (hright : R.action (g * h) 0 ∈ letterOrbit (realizationGenerators R) 0 s) :
    R.circleGap h g ⊆ firstLetterDomain (realizationGenerators R) 0 s := by
  have hKsub : coloredOrbitClosure (realizationGenerators R) 0 ⊆
      closure (Set.range (fun k => R.action k 0)) := by
    intro z hz
    obtain ⟨t, ht⟩ := Set.mem_iUnion.mp hz
    apply closure_mono (s := letterOrbit (realizationGenerators R) 0 t) ?_ ht
    rintro z ⟨w, hw, rfl⟩
    refine ⟨FreeGroup.mk (t :: w), ?_⟩
    rw [← realizationGenerators_lift R]
    exact lift_mk_apply _ _ _
  have hfree : Function.Injective (fun k => FreeGroup.lift (realizationGenerators R) k 0) := by
    simpa only [realizationGenerators_lift] using R.orbit_injective
  have hbase : (0 : AddCircle (1 : ℝ)) ∉ letterOrbit (realizationGenerators R) 0 s :=
    base_not_mem_letterOrbit _ _ hfree s
  have hzeroC : (0 : AddCircle (1 : ℝ)) ∈ closure (Set.range (fun k => R.action k 0)) :=
    subset_closure ⟨1, by simp⟩
  intro x hx
  change x ∈ circularColorFilledHull _ _ _ _
  refine ⟨R.action g 0, Set.mem_iUnion.mpr ⟨s, subset_closure hleft⟩,
    R.action (g * h) 0, Set.mem_iUnion.mpr ⟨s, subset_closure hright⟩,
    Or.inr (Or.inr ?_), ?_, ?_⟩
  · exact (show x ∈ {x | sbtw (R.action g 0) x (R.action (g * h) 0)} from
      (circleGap_eq_sbtw R h g) ▸ hx)
  · rintro (he | he | hs)
    · exact hbase (by simpa only [← he] using hleft)
    · exact hbase (by simpa only [← he] using hright)
    · exact Set.disjoint_left.mp (R.circleGap_disjoint_orbitClosure hh g)
        ((circleGap_eq_sbtw R h g).symm ▸ hs) hzeroC
  · intro z hz hseg
    rcases hseg with rfl | rfl | hs
    · exact orbitClosureColor_eq_of_mem _ _ hsep (subset_closure hleft)
    · exact orbitClosureColor_eq_of_mem _ _ hsep (subset_closure hright)
    · exact False.elim (Set.disjoint_left.mp (R.circleGap_disjoint_orbitClosure hh g)
        ((circleGap_eq_sbtw R h g).symm ▸ hs) (hKsub hz))

theorem realization_non_cancelling_letter_mem (g : FreeGroup ι) (s : ι × Bool)
    (hr : FreeGroup.IsReduced (s :: g.toWord)) :
    R.action (FreeGroup.mk [s] * g) 0 ∈ letterOrbit (realizationGenerators R) 0 s := by
  refine ⟨g.toWord, hr, ?_⟩
  rw [← lift_mk_apply, realizationGenerators_lift,
    show FreeGroup.mk (s :: g.toWord) = FreeGroup.mk [s] * g from by
      calc
        _ = FreeGroup.mk [s] * FreeGroup.mk g.toWord := by rw [FreeGroup.mul_mk]; rfl
        _ = _ := by rw [FreeGroup.mk_toWord]]

/-- Every non-neighboring letter sends the entire actual principal gap into
its canonical filled color domain. The condition is proved using the two
reduced endpoint words, rather than assumed as gap dynamics. -/
theorem principalGapChart_other [Nonempty ι]
    (h : FreeGroup ι) (hh : C.IsSuccessor h)
    (hsep : ∀ s t, s ≠ t →
      Disjoint (closure (letterOrbit (realizationGenerators R) 0 s))
        (closure (letterOrbit (realizationGenerators R) 0 t)))
    (i : Fin (FreeGroup.norm h + 1)) (s : ι × Bool) (t : ℝ)
    (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (hleft : ¬∃ j, i = j.succ ∧ s = successorLetter h j)
    (hright : ¬∃ j, i = j.castSucc ∧ s = PingPong.inverseLetter (successorLetter h j)) :
    letterPerm (realizationGenerators R) s (principalGapChart R h i t) ∈
      firstLetterDomain (realizationGenerators R) 0 s := by
  obtain ⟨hl, hr⟩ := principalGap_other_reduced h i s hleft hright
  have hgap : principalGapChart R h i t ∈ R.circleGap h (inversePrefix h i) := by
    rw [← principalGapChart_image R h hh i]
    exact ⟨t, ht, rfl⟩
  rw [realizationGenerators_letter]
  apply circleGap_subset_firstLetterDomain R h hh (FreeGroup.mk [s] * inversePrefix h i) s hsep
  · exact realization_non_cancelling_letter_mem R _ _ hl
  · simpa only [mul_assoc] using realization_non_cancelling_letter_mem R _ _ hr
  · rw [R.circleGap_transport]
    exact ⟨_, hgap, rfl⟩

/-- A nonprincipal actual gap has matching nonempty first-letter endpoint words. -/
theorem nonprincipal_same_heads (h g : FreeGroup ι) (hp : ¬PrincipalGapLabel h g) :
    ∃ s w z, g.toWord = s :: w ∧ (g * h).toWord = s :: z := by
  cases hg : g.toWord with
  | nil => exact False.elim (hp (Or.inl (FreeGroup.toWord_eq_nil_iff.mp hg)))
  | cons s w =>
    cases hh : (g * h).toWord with
    | nil => exact False.elim (hp (Or.inr (Or.inl (FreeGroup.toWord_eq_nil_iff.mp hh))))
    | cons t z =>
      have he : s = t := by
        by_contra hne
        exact hp (Or.inr (Or.inr ⟨s, t, w, z, hg, hh, hne⟩))
      subst t
      exact ⟨s, w, z, rfl, rfl⟩

theorem realization_head_mem (g : FreeGroup ι) (s : ι × Bool) (w : List (ι × Bool))
    (hg : g.toWord = s :: w) : R.action g 0 ∈ letterOrbit (realizationGenerators R) 0 s := by
  refine ⟨w, hg ▸ FreeGroup.isReduced_toWord, ?_⟩
  rw [← hg, ← lift_mk_apply, FreeGroup.mk_toWord, realizationGenerators_lift]

/-- The actual gap complement splits into filled domains and precisely the
finite inverse-prefix gap chain; orbit-limit points are covered as well. -/
theorem principalGapChart_cover [Nonempty ι] [Finite ι]
    (h : FreeGroup ι) (hh : C.IsSuccessor h)
    (hsep : ∀ s t, s ≠ t →
      Disjoint (closure (letterOrbit (realizationGenerators R) 0 s))
        (closure (letterOrbit (realizationGenerators R) 0 t))) :
    ∀ x : AddCircle (1 : ℝ), x = 0 ∨
      (∃ s, x ∈ firstLetterDomain (realizationGenerators R) 0 s) ∨
      ∃ i t, t ∈ Set.Ioo (0 : ℝ) 1 ∧ principalGapChart R h i t = x := by
  have hfree : Function.Injective (fun g => FreeGroup.lift (realizationGenerators R) g 0) := by
    simpa only [realizationGenerators_lift] using R.orbit_injective
  have hc : ∀ s, Continuous (letterPerm (realizationGenerators R) s) := by
    intro s
    rw [realizationGenerators_letter]
    exact R.action_continuous _
  have hzK : (0 : AddCircle (1 : ℝ)) ∉ coloredOrbitClosure (realizationGenerators R) 0 := by
    intro hz
    obtain ⟨s, hs⟩ := Set.mem_iUnion.mp hz
    exact base_not_mem_colorClosures_of_separated _ _ hfree hc hsep s hs
  intro x
  by_cases hx : x ∈ closure (Set.range (fun g => R.action g 0))
  · rw [← realizationGenerators_lift R, orbitClosure_eq_base_union_colorClosures] at hx
    rcases hx with rfl | hx
    · exact Or.inl rfl
    · right; left
      let s := orbitClosureColor (realizationGenerators R) 0 x
      exact ⟨s, ((circularColorFilledHull_inter _ _ _ hzK s).symm ▸
        (show x ∈ {x | x ∈ coloredOrbitClosure (realizationGenerators R) 0 ∧
          orbitClosureColor (realizationGenerators R) 0 x = s} from ⟨hx, rfl⟩)).1⟩
  · obtain ⟨g, hg⟩ := R.exists_mem_circleGap hh hx
    by_cases hp : PrincipalGapLabel h g
    · right; right
      obtain ⟨i, hi⟩ := (principalGapPrefixEquiv h).surjective ⟨g, hp⟩
      have he : inversePrefix h i = g := congrArg Subtype.val hi
      rw [← he, ← principalGapChart_image R h hh i] at hg
      obtain ⟨t, ht, he'⟩ := hg
      exact ⟨i, t, ht, he'⟩
    · obtain ⟨s, w, z, hw, hz⟩ := nonprincipal_same_heads h g hp
      exact Or.inr (Or.inl ⟨s, circleGap_subset_firstLetterDomain R h hh g s hsep
        (realization_head_mem R g s w hw) (realization_head_mem R (g * h) s z hz) hg⟩)

/-- The cut sequence is strictly increasing and lies inside the fundamental gap. -/
noncomputable def principalGapCut (N : ℕ) (j : Fin N) : ℝ := (j.val + 1 : ℝ) / (N + 1)

theorem principalGapCut_mem (N : ℕ) (j : Fin N) :
    principalGapCut N j ∈ Set.Ioo (0 : ℝ) 1 := by
  have hN : (0 : ℝ) < N + 1 := by positivity
  constructor
  · exact div_pos (by positivity) hN
  · apply (div_lt_one hN).mpr
    exact_mod_cast Nat.add_lt_add_right j.isLt 1

theorem principalGapCut_strictMono (N : ℕ) : StrictMono (principalGapCut N) := by
  intro i j hij
  apply (div_lt_div_iff_of_pos_right (by positivity : (0 : ℝ) < N + 1)).mpr
  exact_mod_cast Nat.add_lt_add_right hij 1

end CircularDynamics
end FnZPositiveCones
