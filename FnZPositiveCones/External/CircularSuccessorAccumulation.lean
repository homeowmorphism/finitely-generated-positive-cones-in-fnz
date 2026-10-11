module

public import FnZPositiveCones.External.CircularIntervalAccumulation
public import FnZPositiveCones.External.CircularIntervalGaps
public import FnZPositiveCones.External.CircularPrincipalGapPrefixes
public import FnZPositiveCones.External.CircularFGSeparationTopology

@[expose] public section

/-! Actual successor gaps provide the finite cutset used in suffix separation.
The bounded-word conclusion below is applied only after ruling out every
full-orbit point in the coordinate interval. -/

namespace FnZPositiveCones
universe u

theorem CircularGroupOrder.successor_unique {G : Type u} [Group G]
    (C : CircularGroupOrder G) {a b : G} (ha : C.IsSuccessor a) (hb : C.IsSuccessor b) :
    a = b := by
  let := C.order
  have h₁ : btw a b 1 := btw_iff_not_sbtw.mpr (ha.2 b)
  have h₂ : btw 1 b a := (btw_iff_not_sbtw.mpr (hb.2 a)).cyclic_right
  rcases h₁.antisymm h₂ with hab | hb1 | h1a
  · exact hab
  · exact False.elim (hb.1 hb1)
  · exact False.elim (ha.1 h1a.symm)

namespace CircularRealization
open CircularDynamics
variable {G : Type u} [Group G] {C : CircularGroupOrder G} (R : CircularRealization C)

/-- In a coordinate interval away from the cut, either a full-orbit point
lies between its endpoints or the endpoints are actual successor labels. -/
theorem eq_mul_successor_or_exists_orbit_between {h : G} (hh : C.IsSuccessor h)
    (u v : G) (hu : 0 < circleCoordinate (R.action u 0))
    (huv : circleCoordinate (R.action u 0) < circleCoordinate (R.action v 0)) :
    v = u * h ∨ ∃ w : G, circleCoordinate (R.action u 0) < circleCoordinate (R.action w 0) ∧
      circleCoordinate (R.action w 0) < circleCoordinate (R.action v 0) := by
  classical
  by_cases hex : ∃ w : G, circleCoordinate (R.action u 0) < circleCoordinate (R.action w 0) ∧
      circleCoordinate (R.action w 0) < circleCoordinate (R.action v 0)
  · exact Or.inr hex
  left
  have hnobt (w : G) : ¬ C.order.sbtw u w v := by
    intro hbt
    have hcircle := (R.orbit_sbtw u w v).mp hbt
    have hchart := (circle_sbtw_coordinate_iff hu (circleCoordinate_mem _).2
      (hu.trans huv) (circleCoordinate_mem _).2 huv.ne (R.action w 0))
    rw [coe_circleCoordinate, coe_circleCoordinate, ite_eq_left huv] at hchart
    exact hex ⟨w, hchart.mp hcircle⟩
  have huvne : u ≠ v := by
    rintro rfl
    exact lt_irrefl _ huv
  have hsucc : C.IsSuccessor (u⁻¹ * v) := by
    refine ⟨fun he => huvne (inv_mul_eq_one.mp he), ?_⟩
    intro w hw
    apply hnobt (u * w)
    have hx := (C.mul_sbtw_mul_left u 1 w (u⁻¹ * v)).mpr hw
    simpa only [mul_one, mul_inv_cancel_left] using hx
  have heq : u⁻¹ * v = h := C.successor_unique hsucc hh
  rw [← heq, mul_inv_cancel_left]

/-- A real accumulation point in the coordinate chart gives a genuine circle
accumulation point. Injectivity is used only on the fundamental interval. -/
theorem accPt_circle_of_accPt_coordinates {t : ℝ} (ht : t ∈ Set.Ico (0 : ℝ) 1)
    (hacc : AccPt t (Filter.principal
      (Set.range (fun g => circleCoordinate (R.action g 0))))) :
    AccPt (t : StandardCircle) (Filter.principal (Set.range (fun g => R.action g 0))) := by
  rw [accPt_iff_nhds]
  intro U hU
  have hpre : ((↑) : ℝ → StandardCircle) ⁻¹' U ∈ nhds t :=
    (AddCircle.continuous_mk' (1 : ℝ)).continuousAt.preimage_mem_nhds hU
  obtain ⟨y, ⟨hyU, g, rfl⟩, hyne⟩ := (accPt_iff_nhds.mp hacc) _ hpre
  refine ⟨R.action g 0, ⟨?_, ⟨g, rfl⟩⟩, ?_⟩
  · simpa only [Set.mem_preimage, coe_circleCoordinate] using hyU
  · intro he
    apply hyne
    simpa only [circleCoordinate_coe ht] using congrArg circleCoordinate he

/-- Successors exclude accumulation at each marked orbit point. -/
theorem not_accPt_orbit_of_successor {h : G} (hh : C.IsSuccessor h) (g : G) :
    ¬ AccPt (R.action g 0) (Filter.principal (Set.range (fun k => R.action k 0))) := by
  intro hacc
  obtain ⟨U, hU, hgU, hsing⟩ := R.exists_orbit_isolating_neighborhood hh g
  obtain ⟨y, ⟨hyU, hyO⟩, hyne⟩ := (accPt_iff_nhds.mp hacc) U (hU.mem_nhds hgU)
  exact hyne (Set.mem_singleton_iff.mp (hsing ▸ ⟨hyU, subset_closure hyO⟩))

/-- The coordinate orbit inherits the same nonaccumulation property. -/
theorem not_accPt_orbit_coordinates_of_successor {h : G} (hh : C.IsSuccessor h) (g : G) :
    ¬ AccPt (circleCoordinate (R.action g 0)) (Filter.principal
      (Set.range (fun k => circleCoordinate (R.action k 0)))) := by
  intro hacc
  have hc := R.accPt_circle_of_accPt_coordinates (circleCoordinate_mem _) hacc
  rw [coe_circleCoordinate] at hc
  exact R.not_accPt_orbit_of_successor hh g hc

end CircularRealization

namespace CircularRealization
open CircularDynamics
variable {ι : Type u} [DecidableEq ι] {C : CircularGroupOrder (FreeGroup ι)} (R : CircularRealization C)

/-- Distinct heads include the empty-word cases in the principal-gap condition. -/
theorem principalGapLabel_of_heads_ne (h u : FreeGroup ι)
    (hne : u.toWord.head? ≠ (u * h).toWord.head?) : PrincipalGapLabel h u := by
  classical
  cases hu : u.toWord with
  | nil => exact Or.inl (FreeGroup.toWord_eq_nil_iff.mp hu)
  | cons s w =>
    cases hv : (u * h).toWord with
    | nil => exact Or.inr (Or.inl (FreeGroup.toWord_eq_nil_iff.mp hv))
    | cons t v =>
      refine Or.inr (Or.inr ⟨s, t, w, v, hu, hv, ?_⟩)
      intro he
      apply hne
      simp only [hu, hv, List.head?_cons, he]

/-- Outside the bounded-word cutset, every pair of differently headed orbit
points has another full-orbit point strictly between it. -/
theorem exists_orbit_between_of_mixed_heads_outside_cutset
    {h : FreeGroup ι} (hh : C.IsSuccessor h) (A B : ℝ) (hA : 0 < A)
    (hcut : ∀ g : FreeGroup ι, FreeGroup.norm g ≤ FreeGroup.norm h →
      circleCoordinate (R.action g 0) ∉ Set.Icc A B)
    (u v : FreeGroup ι)
    (hau : A ≤ circleCoordinate (R.action u 0))
    (huv : circleCoordinate (R.action u 0) < circleCoordinate (R.action v 0))
    (hvb : circleCoordinate (R.action v 0) ≤ B)
    (hhead : u.toWord.head? ≠ v.toWord.head?) :
    ∃ w : FreeGroup ι, circleCoordinate (R.action u 0) < circleCoordinate (R.action w 0) ∧
      circleCoordinate (R.action w 0) < circleCoordinate (R.action v 0) := by
  classical
  rcases R.eq_mul_successor_or_exists_orbit_between hh u v (hA.trans_le hau) huv with he | he
  · have hprincipal : PrincipalGapLabel h u :=
      principalGapLabel_of_heads_ne h u (he ▸ hhead)
    exact False.elim (hcut u (principalGap_norm_le h u hprincipal)
      ⟨hau, huv.le.trans hvb⟩)
  · exact he

/-- The bounded-word cutset forces an actual circle accumulation point inside
every remaining mixed-head interval. No density of last-letter orbits is
assumed in this step. -/
theorem exists_circle_accPt_of_mixed_heads_outside_cutset
    {h : FreeGroup ι} (hh : C.IsSuccessor h) (a b : FreeGroup ι)
    (ha : 0 < circleCoordinate (R.action a 0))
    (hab : circleCoordinate (R.action a 0) < circleCoordinate (R.action b 0))
    (hhead : a.toWord.head? ≠ b.toWord.head?)
    (hcut : ∀ g : FreeGroup ι, FreeGroup.norm g ≤ FreeGroup.norm h →
      circleCoordinate (R.action g 0) ∉
        Set.Icc (circleCoordinate (R.action a 0)) (circleCoordinate (R.action b 0))) :
    ∃ t : ℝ, t ∈ Set.Ioo (circleCoordinate (R.action a 0)) (circleCoordinate (R.action b 0)) ∧
      AccPt (t : StandardCircle) (Filter.principal (Set.range (fun g => R.action g 0))) := by
  classical
  let f : FreeGroup ι → ℝ := fun g => circleCoordinate (R.action g 0)
  have hf : Function.Injective f := circleCoordinate_injective.comp R.orbit_injective
  let color : ℝ → Option (ι × Bool) := fun x => (Function.invFun f x).toWord.head?
  have hcolor (g : FreeGroup ι) : color (f g) = g.toWord.head? := by
    simp only [color, Function.leftInverse_invFun hf g]
  obtain ⟨t, ht, hacc⟩ := exists_accPt_between_of_no_mixed_adjacent
    (Set.range f) color (a := f a) (b := f b) ⟨a, rfl⟩ ⟨b, rfl⟩ hab
    (by simpa only [hcolor] using hhead)
    (R.not_accPt_orbit_coordinates_of_successor hh a)
    (R.not_accPt_orbit_coordinates_of_successor hh b) (by
      rintro x ⟨u, rfl⟩ y ⟨v, rfl⟩ hau huv hvb hne
      obtain ⟨w, huw, hwv⟩ := R.exists_orbit_between_of_mixed_heads_outside_cutset hh
        (f a) (f b) ha hcut u v hau huv hvb (by simpa only [hcolor] using hne)
      exact ⟨f w, ⟨w, rfl⟩, huw, hwv⟩)
  refine ⟨t, ht, R.accPt_circle_of_accPt_coordinates ?_ hacc⟩
  exact ⟨(ha.trans ht.1).le, ht.2.trans (circleCoordinate_mem _).2⟩

end CircularRealization
end FnZPositiveCones
