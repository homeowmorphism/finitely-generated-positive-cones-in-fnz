module

public import FnZPositiveCones.External.CircularDynamicsCircleDomains
public import FnZPositiveCones.External.CircularDynamicsCircularHull
public import FnZPositiveCones.External.CircularDynamicsHull
public import FnZPositiveCones.External.OrderedActionsCircleRealization

@[expose] public section

/-! Exact finite arc decomposition for the canonical filled circular color domains. -/
namespace FnZPositiveCones
namespace CircularDynamics

/-- In a chart avoiding zero, the actual oriented segment is exactly a real
closed interval, including the singleton case. -/
theorem circularClosedSegment_coe_iff {a b x : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hb : 0 < b) (hb1 : b < 1)
    (hab : a ≤ b) (hx : x ∈ Set.Ico (0 : ℝ) 1) :
    (x : StandardCircle) ∈ circularClosedSegment (a : StandardCircle) (b : StandardCircle) ↔
      x ∈ Set.Icc a b := by
  have hxa : (x : StandardCircle) = (a : StandardCircle) ↔ x = a :=
    AddCircle.coe_eq_coe_iff_of_mem_Ico (a := (0 : ℝ))
      (by simpa using hx) (by simpa using (show a ∈ Set.Ico (0 : ℝ) 1 from ⟨ha.le, ha1⟩))
  have hxb : (x : StandardCircle) = (b : StandardCircle) ↔ x = b :=
    AddCircle.coe_eq_coe_iff_of_mem_Ico (a := (0 : ℝ))
      (by simpa using hx) (by simpa using (show b ∈ Set.Ico (0 : ℝ) 1 from ⟨hb.le, hb1⟩))
  rcases eq_or_lt_of_le hab with rfl | hab
  · simp only [circularClosedSegment, Set.mem_ofPred_eq, sbtw_irrefl_left_right,
      or_false, or_self, hxa, Set.mem_Icc, le_antisymm_iff]
    exact and_comm
  · have h0ab : sbtw (0 : StandardCircle) a b :=
      (OrderedActions.circle_sbtw_zero_iff ⟨ha.le, ha1⟩ ⟨hb.le, hb1⟩).mpr ⟨ha, hab⟩
    simp only [circularClosedSegment, Set.mem_ofPred_eq, hxa, hxb, sbtw_cut_iff h0ab,
      OrderedActions.circle_sbtw_zero_iff ⟨ha.le, ha1⟩ hx,
      OrderedActions.circle_sbtw_zero_iff hx ⟨hb.le, hb1⟩, Set.mem_Icc]
    constructor
    · rintro (rfl | rfl | ⟨⟨_, hax⟩, _, hxb⟩)
      · exact ⟨le_rfl, hab.le⟩
      · exact ⟨hab.le, le_rfl⟩
      · exact ⟨hax.le, hxb.le⟩
    · rintro ⟨hax, hxb⟩
      rcases eq_or_lt_of_le hax with he | he
      · exact Or.inl he.symm
      rcases eq_or_lt_of_le hxb with he' | he'
      · exact Or.inr (Or.inl he')
      · exact Or.inr (Or.inr ⟨⟨ha, he⟩, ha.trans he, he'⟩)

theorem circleCoordinate_pos_of_mem {K : Set StandardCircle} (hzero : 0 ∉ K)
    {x : StandardCircle} (hx : x ∈ K) : 0 < circleCoordinate x := by
  apply lt_of_le_of_ne (circleCoordinate_mem x).1
  intro he
  have hx0 : x = 0 := by rw [← coe_circleCoordinate x, ← he]; rfl
  exact hzero (hx0 ▸ hx)

/-- Avoidance of the basepoint fixes the linear orientation of the chart. -/
theorem circularClosedSegment_coordinate_le {a b : StandardCircle}
    (hb : b ≠ 0) (hzero : 0 ∉ circularClosedSegment a b) :
    circleCoordinate a ≤ circleCoordinate b := by
  by_contra h
  have hbpos : 0 < circleCoordinate b := by
    apply lt_of_le_of_ne (circleCoordinate_mem b).1
    intro he
    apply hb
    rw [← coe_circleCoordinate b, ← he]
    rfl
  have hs : sbtw (0 : StandardCircle) (circleCoordinate b) (circleCoordinate a) :=
    (OrderedActions.circle_sbtw_zero_iff (circleCoordinate_mem b) (circleCoordinate_mem a)).mpr
      ⟨hbpos, lt_of_not_ge h⟩
  apply hzero
  exact Or.inr (Or.inr (by simpa only [coe_circleCoordinate] using hs.cyclic_right))

/-- The canonical circular filled domain is exactly the image of the canonical
real filled domain in the cut chart. This is stronger than a finite arc cover. -/
theorem circularColorFilledHull_eq_image {C : Type*} (K : Set StandardCircle)
    (hzero : 0 ∉ K) (color : StandardCircle → C) (c : C) :
    circularColorFilledHull K color 0 c =
      (fun x : ℝ => (x : StandardCircle)) ''
        colorFilledHull (circleCoordinate '' K) (fun x : ℝ => color (x : StandardCircle)) c := by
  let R := circleCoordinate '' K
  have hR : ∀ x ∈ R, (x : StandardCircle) ∈ K ∧ 0 < x ∧ x < 1 := by
    rintro x ⟨y, hy, rfl⟩
    exact ⟨by simpa using hy, circleCoordinate_pos_of_mem hzero hy, (circleCoordinate_mem y).2⟩
  ext x
  constructor
  · rintro ⟨a, ha, b, hb, hxab, hcut, hm⟩
    have hap := circleCoordinate_pos_of_mem hzero ha
    have hbp := circleCoordinate_pos_of_mem hzero hb
    have hab := circularClosedSegment_coordinate_le
      (fun he => hzero (he ▸ hb)) hcut
    have hxI : circleCoordinate x ∈ Set.Icc (circleCoordinate a) (circleCoordinate b) := by
      apply (circularClosedSegment_coe_iff hap (circleCoordinate_mem a).2 hbp
        (circleCoordinate_mem b).2 hab (circleCoordinate_mem x)).mp
      simpa only [coe_circleCoordinate] using hxab
    refine ⟨circleCoordinate x, ?_, coe_circleCoordinate x⟩
    refine ⟨circleCoordinate a, ⟨a, ha, rfl⟩, circleCoordinate b, ⟨b, hb, rfl⟩,
      hxI.1, hxI.2, ?_⟩
    intro z hz hzi
    apply hm (z : StandardCircle) (hR z hz).1
    have hs := (circularClosedSegment_coe_iff hap (circleCoordinate_mem a).2 hbp
      (circleCoordinate_mem b).2 hab ⟨(hR z hz).2.1.le, (hR z hz).2.2⟩).mpr hzi
    simpa only [coe_circleCoordinate] using hs
  · rintro ⟨y, ⟨a, ha, b, hb, hay, hyb, hm⟩, rfl⟩
    have ha' := hR a ha
    have hb' := hR b hb
    have hab := hay.trans hyb
    have hyI : y ∈ Set.Ico (0 : ℝ) 1 := ⟨ha'.2.1.le.trans hay, hyb.trans_lt hb'.2.2⟩
    refine ⟨(a : StandardCircle), ha'.1, (b : StandardCircle), hb'.1,
      (circularClosedSegment_coe_iff ha'.2.1 ha'.2.2 hb'.2.1 hb'.2.2 hab hyI).mpr ⟨hay, hyb⟩,
      ?_, ?_⟩
    · intro hs
      have h0 : (0 : ℝ) ∈ Set.Icc a b :=
        (circularClosedSegment_coe_iff ha'.2.1 ha'.2.2 hb'.2.1 hb'.2.2 hab
          ⟨le_rfl, zero_lt_one⟩).mp hs
      linarith [h0.1, ha'.2.1]
    · intro z hz hzs
      have hzI : circleCoordinate z ∈ Set.Icc a b := by
        apply (circularClosedSegment_coe_iff ha'.2.1 ha'.2.2 hb'.2.1 hb'.2.2 hab
          (circleCoordinate_mem z)).mp
        simpa only [coe_circleCoordinate] using hzs
      simpa only [coe_circleCoordinate] using hm (circleCoordinate z) ⟨z, hz, rfl⟩ hzI


/-- Local separation passes to the real cut without any uniformity assumption. -/
theorem circleCoordinateImage_local_color {C : Type*} (K : Set StandardCircle)
    (color : StandardCircle → C)
    (hlocal : ∀ x ∈ K, ∃ ε > 0, ∀ y ∈ K, dist x y < ε → color x = color y) :
    ∀ x ∈ circleCoordinate '' K, ∃ ε > 0, ∀ y ∈ circleCoordinate '' K,
      dist x y < ε → color (x : StandardCircle) = color (y : StandardCircle) := by
  rintro x ⟨z, hz, rfl⟩
  obtain ⟨ε, hε, hm⟩ := hlocal z hz
  refine ⟨ε, hε, ?_⟩
  rintro y ⟨w, hw, rfl⟩ hzw
  have he := (circle_dist_coe_le (circleCoordinate z) (circleCoordinate w)).trans_lt hzw
  simpa only [coe_circleCoordinate] using hm w hw (by simpa only [coe_circleCoordinate] using he)

/-- Exact finite closed-arc decomposition of the actual filled circular domain. -/
theorem circularColorFilledHull_finite_arcs {C : Type*} (K : Set StandardCircle)
    (hK : IsCompact K) (hzero : 0 ∉ K) (color : StandardCircle → C)
    (hlocal : ∀ x ∈ K, ∃ ε > 0, ∀ y ∈ K, dist x y < ε → color x = color y)
    (c : C) : ∃ F : Finset (ℝ × ℝ),
      circularColorFilledHull K color 0 c = ⋃ p ∈ F, closedCircleArc p.1 p.2 := by
  have hR : IsCompact (circleCoordinate '' K) := hK.image_of_continuousOn
    (fun x hx => (continuousAt_circleCoordinate (fun he => hzero (he ▸ hx))).continuousWithinAt)
  obtain ⟨F, hF⟩ := colorFilledHull_finite_intervals (circleCoordinate '' K) hR
    (fun x : ℝ => color (x : StandardCircle)) (circleCoordinateImage_local_color K color hlocal) c
  refine ⟨F, ?_⟩
  rw [circularColorFilledHull_eq_image K hzero color c, hF]
  simp only [Set.image_iUnion, closedCircleArc]

/-- Compactness is proved from the actual finite arc decomposition. -/
theorem isCompact_circularColorFilledHull {C : Type*} (K : Set StandardCircle)
    (hK : IsCompact K) (hzero : 0 ∉ K) (color : StandardCircle → C)
    (hlocal : ∀ x ∈ K, ∃ ε > 0, ∀ y ∈ K, dist x y < ε → color x = color y)
    (c : C) : IsCompact (circularColorFilledHull K color 0 c) := by
  obtain ⟨F, hF⟩ := circularColorFilledHull_finite_arcs K hK hzero color hlocal c
  rw [hF]
  exact F.finite_toSet.isCompact_biUnion (fun p _ => isCompact_closedCircleArc p.1 p.2)

/-- Different actual filled circular domains are disjoint, including their
endpoints; this is derived from the cut, not assumed for the filled sets. -/
theorem circularColorFilledHull_disjoint {C : Type*} (K : Set StandardCircle)
    (hzero : 0 ∉ K) (color : StandardCircle → C) {c d : C} (hcd : c ≠ d) :
    Disjoint (circularColorFilledHull K color 0 c) (circularColorFilledHull K color 0 d) := by
  rw [circularColorFilledHull_eq_image K hzero color c,
    circularColorFilledHull_eq_image K hzero color d]
  have hmem : ∀ e, ∀ x ∈ colorFilledHull (circleCoordinate '' K)
      (fun x : ℝ => color (x : StandardCircle)) e, x ∈ Set.Ico (0 : ℝ) 1 := by
    rintro e x ⟨a, ⟨p, hp, rfl⟩, b, ⟨q, hq, rfl⟩, hax, hxb, hm⟩
    exact ⟨(circleCoordinate_mem p).1.trans hax, hxb.trans_lt (circleCoordinate_mem q).2⟩
  apply Set.disjoint_left.mpr
  rintro x ⟨a, ha, hax⟩ ⟨b, hb, hbx⟩
  have he : a = b := (AddCircle.coe_eq_coe_iff_of_mem_Ico (a := (0 : ℝ))
    (by simpa using hmem c a ha) (by simpa using hmem d b hb)).mp (hax.trans hbx.symm)
  exact Set.disjoint_left.mp (colorFilledHull_disjoint _ _ hcd) ha (he ▸ hb)

end CircularDynamics
end FnZPositiveCones
