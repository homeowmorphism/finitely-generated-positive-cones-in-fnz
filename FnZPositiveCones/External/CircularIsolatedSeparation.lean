module

public import FnZPositiveCones.External.CircularSuffixSeparation
public import FnZPositiveCones.External.CircularSuccessorAccumulation
public import FnZPositiveCones.External.CircularLastLetterDynamics
public import FnZPositiveCones.External.CircularDynamicsPrincipalChain

@[expose] public section

/-!
Isolation and actual last-letter accumulation density imply separation of
first-letter orbit closures. The density input remains explicit in this
module; finite trace adjacency is repaired by closed suffix avoidance.
-/

namespace FnZPositiveCones.CircularRealization
open CircularDynamics
universe u
variable {ι : Type u} {C : CircularGroupOrder (FreeGroup ι)} (R : CircularRealization C)

private theorem realization_word (w : List (ι × Bool)) :
    evalWord (realizationGenerators R) w 0 = R.action (FreeGroup.mk w) 0 := by
  rw [← lift_mk_apply, realizationGenerators_lift]

/-- Full-orbit accumulation density supplies a prescribed last letter in
each genuine coordinate interval containing an accumulation point. -/
theorem exists_lastLetter_between_of_accumulation
    (hdensity : ∀ t : ι × Bool, derivedSet (Set.range (fun g => R.action g 0)) ⊆
      closure (lastLetterOrbit (realizationGenerators R) 0 t))
    {a b : ℝ} (ha : 0 < a) (hb : b < 1)
    (hacc : ∃ t ∈ Set.Ioo a b,
      AccPt (t : StandardCircle) (Filter.principal (Set.range (fun g => R.action g 0))))
    (r : ι × Bool) :
    ∃ w, FreeGroup.IsReduced w ∧ w.getLast? = some r ∧
      circleCoordinate (R.action (FreeGroup.mk w) 0) ∈ Set.Ioo a b := by
  obtain ⟨t, ht, htacc⟩ := hacc
  have hcl := hdensity r htacc
  let U : Set StandardCircle := ((↑) : ℝ → StandardCircle) '' Set.Ioo a b
  have hU : IsOpen U := QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo
  obtain ⟨y, hyU, w, hw, hwy⟩ := mem_closure_iff.mp hcl U hU ⟨t, ht, rfl⟩
  obtain ⟨z, hz, hzy⟩ := hyU
  refine ⟨w ++ [r], hw, ?_, ?_⟩
  · simp
  · have hzIco : z ∈ Set.Ico (0 : ℝ) 1 := ⟨(ha.trans hz.1).le, hz.2.trans hb⟩
    rw [← realization_word, hwy, ← hzy, circleCoordinate_coe hzIco]
    exact hz

/-- A mixed-head interval avoiding the protected and bounded-word cutsets
contains a fully admissible supported crossing. -/
theorem crossingConfig_of_lastLetter_density [DecidableEq ι]
    {h : FreeGroup ι} (hh : C.IsSuccessor h)
    (hdensity : ∀ t : ι × Bool, derivedSet (Set.range (fun g => R.action g 0)) ⊆
      closure (lastLetterOrbit (realizationGenerators R) 0 t))
    (W : Finset (List (ι × Bool))) (a b : List (ι × Bool))
    (ha : FreeGroup.IsReduced a) (hb : FreeGroup.IsReduced b)
    (hhead : a.head? ≠ b.head?)
    (hapos : 0 < circleCoordinate (R.action (FreeGroup.mk a) 0))
    (hab : circleCoordinate (R.action (FreeGroup.mk a) 0) <
      circleCoordinate (R.action (FreeGroup.mk b) 0))
    (hprotect : ∀ y ∈ protectedTrace (realizationGenerators R) W,
      circleCoordinate y ∉ Set.Icc (circleCoordinate (R.action (FreeGroup.mk a) 0))
        (circleCoordinate (R.action (FreeGroup.mk b) 0)))
    (hcut : ∀ g : FreeGroup ι, FreeGroup.norm g ≤ FreeGroup.norm h →
      circleCoordinate (R.action g 0) ∉ Set.Icc (circleCoordinate (R.action (FreeGroup.mk a) 0))
        (circleCoordinate (R.action (FreeGroup.mk b) 0))) :
    Nonempty (CrossingConfig (realizationGenerators R) W) := by
  classical
  let coord : List (ι × Bool) → ℝ := fun w => circleCoordinate (R.action (FreeGroup.mk w) 0)
  have hcoord : ∀ v w, FreeGroup.IsReduced v → FreeGroup.IsReduced w →
      coord v = coord w → v = w := by
    intro v w hv hw he
    have heq := R.orbit_injective (circleCoordinate_injective he)
    have hwords := congrArg FreeGroup.toWord heq
    simpa only [FreeGroup.toWord_mk, hv.reduce_eq, hw.reduce_eq] using hwords
  have hzero : coord [] ∉ Set.Icc (coord a) (coord b) := by
    have hbase : coord [] = 0 := by
      change circleCoordinate (R.action 1 0) = 0
      rw [map_one, Equiv.Perm.one_apply]
      exact circleCoordinate_coe (show (0 : ℝ) ∈ Set.Ico (0 : ℝ) 1 from ⟨le_rfl, zero_lt_one⟩)
    rw [hbase]
    exact fun hz => hapos.not_ge hz.1
  have hlocal : ∀ u v, FreeGroup.IsReduced u → FreeGroup.IsReduced v →
      coord a ≤ coord u → coord u < coord v → coord v ≤ coord b →
      u.head? ≠ v.head? → ∀ r : ι × Bool,
      ∃ w, FreeGroup.IsReduced w ∧ w.getLast? = some r ∧ coord w ∈ Set.Ioo (coord u) (coord v) := by
    intro u v hu hv hau huv hvb hheads r
    have hcut' : ∀ g : FreeGroup ι, FreeGroup.norm g ≤ FreeGroup.norm h →
        circleCoordinate (R.action g 0) ∉ Set.Icc (coord u) (coord v) := by
      intro g hg hx
      exact hcut g hg ⟨hau.trans hx.1, hx.2.trans hvb⟩
    have hhheads : (FreeGroup.mk u).toWord.head? ≠ (FreeGroup.mk v).toWord.head? := by
      simpa only [FreeGroup.toWord_mk, hu.reduce_eq, hv.reduce_eq] using hheads
    have hacc := R.exists_circle_accPt_of_mixed_heads_outside_cutset hh
      (FreeGroup.mk u) (FreeGroup.mk v) (hapos.trans_le hau) huv hhheads hcut'
    exact R.exists_lastLetter_between_of_accumulation hdensity
      (hapos.trans_le hau) (circleCoordinate_mem _).2 hacc r
  obtain ⟨u, v, hu, hv, hau, huv, hvb, hheads, havoid⟩ :=
    exists_closed_suffix_avoiding_pair coord hcoord a b ha hb hab hhead hzero hlocal
  have hunil : u ≠ [] := by
    intro he
    exact hzero ⟨he ▸ hau, he ▸ huv.le.trans hvb⟩
  have hvnil : v ≠ [] := by
    intro he
    exact hzero ⟨he ▸ hau.trans huv.le, he ▸ hvb⟩
  cases u with
  | nil => exact False.elim (hunil rfl)
  | cons s u =>
    cases v with
    | nil => exact False.elim (hvnil rfl)
    | cons t v =>
      refine ⟨{
        first := s
        second := t
        leftTail := u
        rightTail := v
        different := ?_
        leftCoord := coord (s :: u)
        rightCoord := coord (t :: v)
        left_pos := hapos.trans_le hau
        left_lt_right := huv
        right_lt_one := (circleCoordinate_mem _).2
        left_value := ?_
        right_value := ?_
        avoids := ?_ }⟩
      · intro he
        exact hheads (by simp only [List.head?_cons, he])
      · rw [realization_word, coe_circleCoordinate]
      · rw [realization_word, coe_circleCoordinate]
      · intro y hy hyint
        rcases hy with hy | hy | hy
        · exact hprotect y hy ⟨hau.trans hyint.1, hyint.2.trans hvb⟩
        · obtain ⟨w, hwu, hwy⟩ := (mem_wordTrace_iff (realizationGenerators R) 0 y u).mp hy
          have hws : w.IsSuffix (s :: u) := hwu.trans ⟨[s], rfl⟩
          have hwne : w ≠ s :: u := by
            intro he
            have hh := hwu.length_le
            simp only [he, List.length_cons] at hh
            omega
          apply havoid w (Or.inl ⟨hws, hwne⟩)
          simpa only [coord, ← realization_word, hwy] using hyint
        · obtain ⟨w, hwv, hwy⟩ := (mem_wordTrace_iff (realizationGenerators R) 0 y v).mp hy
          have hws : w.IsSuffix (t :: v) := hwv.trans ⟨[t], rfl⟩
          have hwne : w ≠ t :: v := by
            intro he
            have hh := hwv.length_le
            simp only [he, List.length_cons] at hh
            omega
          apply havoid w (Or.inr ⟨hws, hwne⟩)
          simpa only [coord, ← realization_word, hwy] using hyint

/-- The general isolated-order separation step. Its only external geometric
input is the displayed density of each actual last-letter orbit at the
accumulation set of the full marked orbit. -/
theorem firstLetter_closures_disjoint_of_isolated_of_lastLetter_density [Finite ι]
    (hi : IsOpen ({C} : Set (CircularGroupOrder (FreeGroup ι))))
    {h : FreeGroup ι} (hh : C.IsSuccessor h)
    (hdensity : ∀ t : ι × Bool, derivedSet (Set.range (fun g => R.action g 0)) ⊆
      closure (lastLetterOrbit (realizationGenerators R) 0 t))
    (s t : ι × Bool) (hst : s ≠ t) :
    Disjoint (closure (letterOrbit (realizationGenerators R) 0 s))
      (closure (letterOrbit (realizationGenerators R) 0 t)) := by
  classical
  let ρ := realizationGenerators R
  have hρ : ∀ i, PreservesCircular (ρ i) := fun i => R.action_preserves (FreeGroup.of i)
  have hfree : Function.Injective (fun g => FreeGroup.lift ρ g 0) := by
    simpa only [ρ, realizationGenerators_lift] using R.orbit_injective
  have horder : circularOrbitOrder (FreeGroup.lift ρ) (preservesCircular_lift ρ hρ) 0 hfree = C := by
    apply CircularGroupOrder.ext
    intro a b c
    simpa only [circularOrbitOrder_sbtw, ρ, realizationGenerators_lift]
      using (R.orbit_sbtw a b c).symm
  obtain ⟨W, hW⟩ := isolated_has_finite_crossing_obstruction ρ hρ hfree (horder.symm ▸ hi)
  let F : Set StandardCircle := (protectedTrace ρ W : Set StandardCircle) ∪
    (fun g => R.action g 0) '' {g : FreeGroup ι | FreeGroup.norm g ≤ FreeGroup.norm h}
  have hF : F.Finite := (protectedTrace ρ W).finite_toSet.union
    ((finite_freeGroup_norm_ball (ι := ι) (FreeGroup.norm h)).image _)
  have hFsubset : F ⊆ Set.range (fun g => R.action g 0) := by
    intro y hy
    rcases hy with hy | ⟨g, _, rfl⟩
    · obtain ⟨w, _, hyw⟩ := Finset.mem_biUnion.mp hy
      obtain ⟨v, _, hv⟩ := (mem_wordTrace_iff ρ 0 y w).mp (List.mem_toFinset.mp hyw)
      exact ⟨FreeGroup.mk v, (realization_word R v).symm.trans hv⟩
    · exact ⟨g, rfl⟩
  have hsubset (j : ι × Bool) : letterOrbit ρ 0 j ⊆ Set.range (fun g => R.action g 0) := by
    rintro _ ⟨w, _, rfl⟩
    exact ⟨FreeGroup.mk (j :: w), (realization_word R _).symm⟩
  have hpos (j : ι × Bool) (w : List (ι × Bool)) (hw : FreeGroup.IsReduced (j :: w)) :
      0 < circleCoordinate (evalWord ρ (j :: w) 0) := by
    apply lt_of_le_of_ne (circleCoordinate_mem _).1
    intro he
    have heval : evalWord ρ (j :: w) 0 = 0 := by
      rw [← coe_circleCoordinate (evalWord ρ (j :: w) 0), ← he]
      rfl
    exact base_not_mem_letterOrbit ρ 0 hfree j ⟨w, hw, heval⟩
  apply disjoint_closures_circle_of_finite_separators _ _ F hF
    (letterOrbit_disjoint ρ 0 hfree hst)
  · rintro _ ⟨w, hw, rfl⟩ _ ⟨v, hv, rfl⟩
    by_contra hnone
    have havoid : ∀ y ∈ F, circleCoordinate y ∉
        Set.uIcc (circleCoordinate (evalWord ρ (s :: w) 0))
          (circleCoordinate (evalWord ρ (t :: v) 0)) := by
      intro y hy hyint
      exact hnone ⟨y, hy, hyint⟩
    have hne : circleCoordinate (evalWord ρ (s :: w) 0) ≠
        circleCoordinate (evalWord ρ (t :: v) 0) := by
      intro he
      have hewords := (evalWord_eq_iff_of_reduced ρ 0 hfree hw hv).mp (circleCoordinate_injective he)
      exact hst (List.cons.inj hewords).1
    have hsthead : (s :: w).head? ≠ (t :: v).head? := by
      simpa only [List.head?_cons, ne_eq, Option.some.injEq] using hst
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · apply hW
      apply R.crossingConfig_of_lastLetter_density hh hdensity W (s :: w) (t :: v) hw hv hsthead
      · simpa only [ρ, realization_word] using hpos s w hw
      · simpa only [ρ, realization_word] using hlt
      · intro y hy
        have hh := havoid y (Or.inl hy)
        rw [Set.uIcc_of_le hlt.le] at hh
        simpa only [ρ, realization_word] using hh
      · intro g hg
        have hh := havoid (R.action g 0) (Or.inr ⟨g, hg, rfl⟩)
        rw [Set.uIcc_of_le hlt.le] at hh
        simpa only [ρ, realization_word] using hh
    · apply hW
      apply R.crossingConfig_of_lastLetter_density hh hdensity W (t :: v) (s :: w) hv hw (Ne.symm hsthead)
      · simpa only [ρ, realization_word] using hpos t v hv
      · simpa only [ρ, realization_word] using hlt
      · intro y hy
        have hh := havoid y (Or.inl hy)
        rw [Set.uIcc_of_ge hlt.le] at hh
        simpa only [ρ, realization_word] using hh
      · intro g hg
        have hh := havoid (R.action g 0) (Or.inr ⟨g, hg, rfl⟩)
        rw [Set.uIcc_of_ge hlt.le] at hh
        simpa only [ρ, realization_word] using hh
  · intro x hx
    have hxorb : x ∈ Set.range (fun g => R.action g 0) := by
      rcases hx with hx | hx
      · refine ⟨1, ?_⟩
        simpa only [map_one, Equiv.Perm.one_apply] using hx.symm
      · exact hFsubset hx
    obtain ⟨g, rfl⟩ := hxorb
    obtain ⟨U, hU, hgU, hsing⟩ := R.exists_orbit_isolating_neighborhood hh g
    refine ⟨U, hU, hgU, ?_⟩
    rintro x ⟨hxU, hx⟩
    apply hsing ▸ (show x ∈ U ∩ closure (Set.range (fun g => R.action g 0)) from ?_)
    exact ⟨hxU, subset_closure (hx.elim (fun hs => hsubset s hs) (fun ht => hsubset t ht))⟩

end FnZPositiveCones.CircularRealization
