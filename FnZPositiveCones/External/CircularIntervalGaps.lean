module

public import FnZPositiveCones.External.CircularIntervalSuccessor

@[expose] public section

/-! Successor intervals are the actual connected complementary components. -/
namespace FnZPositiveCones.CircularDynamics

theorem btw_iff_mem_circularClosedSegment {X : Type*} [CircularOrder X]
    {a b x : X} (hab : a ≠ b) : btw a x b ↔ x ∈ circularClosedSegment a b := by
  constructor
  · intro h
    by_cases hxa : x = a
    · exact Or.inl hxa
    by_cases hxb : x = b
    · exact Or.inr (Or.inl hxb)
    right; right
    apply sbtw_iff_btw_not_btw.mpr ⟨h, ?_⟩
    intro hr
    rcases h.antisymm hr with ha | hb | he
    · exact hxa ha.symm
    · exact hxb hb
    · exact hab he.symm
  · rintro (rfl | rfl | h)
    · exact btw_rfl_left
    · exact btw_rfl_right
    · exact h.btw

/-- Strict circular betweenness has the two expected coordinate forms. -/
theorem circle_sbtw_coordinate_iff {a b : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (hb : 0 < b) (hb1 : b < 1) (hab : a ≠ b) (x : StandardCircle) :
    sbtw (a : StandardCircle) x b ↔
      if a < b then a < circleCoordinate x ∧ circleCoordinate x < b
      else a < circleCoordinate x ∨ circleCoordinate x < b := by
  have hx := circleCoordinate_mem x
  by_cases hlt : a < b
  · rw [ite_eq_left hlt]
    have h0 : sbtw (0 : StandardCircle) a b :=
      (OrderedActions.circle_sbtw_zero_iff ⟨ha.le, ha1⟩ ⟨hb.le, hb1⟩).mpr ⟨ha, hlt⟩
    rw [sbtw_cut_iff h0, ← coe_circleCoordinate x,
      OrderedActions.circle_sbtw_zero_iff ⟨ha.le, ha1⟩ hx,
      OrderedActions.circle_sbtw_zero_iff hx ⟨hb.le, hb1⟩, coe_circleCoordinate]
    constructor
    · exact fun h => ⟨h.1.2, h.2.2⟩
    · exact fun h => ⟨⟨ha, h.1⟩, ha.trans h.1, h.2⟩
  · rw [ite_eq_right hlt, sbtw_iff_not_btw]
    have hba : (b : StandardCircle) ≠ (a : StandardCircle) := by
      intro he
      have he' : b = a := by
        simpa only [circleCoordinate_coe ⟨hb.le, hb1⟩, circleCoordinate_coe ⟨ha.le, ha1⟩]
          using congrArg circleCoordinate he
      exact hab he'.symm
    rw [btw_iff_mem_circularClosedSegment hba, ← coe_circleCoordinate x,
      circularClosedSegment_coe_iff hb hb1 ha ha1 (le_of_not_gt hlt) hx, coe_circleCoordinate]
    simp only [Set.mem_Icc, not_and_or, not_le]
    exact or_comm

/-- A chart interval crossing the cut has the expected two coordinate pieces. -/
theorem mem_wrapped_circle_arc {a b : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (hb : 0 < b) (hb1 : b < 1) (x : StandardCircle) :
    x ∈ (fun t : ℝ => (t : StandardCircle)) '' Set.Ioo a (b + 1) ↔
      a < circleCoordinate x ∨ circleCoordinate x < b := by
  have hshift (t : ℝ) : ((t - 1 : ℝ) : StandardCircle) = (t : StandardCircle) := by
    have h := AddCircle.coe_add_period (1 : ℝ) (t - 1)
    simpa only [sub_add_cancel] using h.symm
  constructor
  · rintro ⟨t, ht, rfl⟩
    by_cases ht1 : t < 1
    · left
      rw [circleCoordinate_coe ⟨(ha.trans ht.1).le, ht1⟩]
      exact ht.1
    · right
      have htm : t - 1 ∈ Set.Ico (0 : ℝ) 1 := by constructor <;> linarith [ht.2]
      change circleCoordinate (t : StandardCircle) < b
      rw [← hshift t, circleCoordinate_coe htm]
      linarith [ht.2]
  · intro hx
    have hcoord := circleCoordinate_mem x
    rcases hx with hx | hx
    · exact ⟨circleCoordinate x, ⟨hx, by linarith [hcoord.2]⟩, coe_circleCoordinate x⟩
    · refine ⟨circleCoordinate x + 1, ⟨by linarith [hcoord.1], by linarith⟩, ?_⟩
      change ((circleCoordinate x + 1 : ℝ) : StandardCircle) = x
      rw [AddCircle.coe_add_period, coe_circleCoordinate]

namespace CircleIntervalFamily
universe u
variable {I : Type u} (F : CircleIntervalFamily I) [Fintype I]

/-- The gap immediately following an actual component. -/
def gap (i : I) : Set StandardCircle := {x | F.GapCoordinate i (circleCoordinate x)}

theorem gap_eq_image (i : I) : F.gap i =
    (fun t : ℝ => (t : StandardCircle)) ''
      Set.Ioo (F.right i) (F.left (F.next i) + if F.left i < F.left (F.next i) then 0 else 1) := by
  ext x
  by_cases hi : F.left i < F.left (F.next i)
  · simp only [gap, Set.mem_ofPred_eq, GapCoordinate, hi, ↓reduceIte, add_zero]
    have hr : 0 < F.right i := (F.left_pos i).trans (F.left_lt_right i)
    have hl : F.left (F.next i) < 1 := (F.left_lt_right _).trans (F.right_lt_one _)
    have h := coe_mem_open_arc_iff hr hl (circleCoordinate_mem x)
    simpa only [coe_circleCoordinate, Set.mem_Ioo] using h.symm
  · simp only [gap, Set.mem_ofPred_eq, GapCoordinate, hi, ↓reduceIte]
    exact (mem_wrapped_circle_arc ((F.left_pos i).trans (F.left_lt_right i))
      (F.right_lt_one i) (F.left_pos _) ((F.left_lt_right _).trans (F.right_lt_one _)) x).symm

theorem gap_interval_nonempty (i : I) :
    F.right i < F.left (F.next i) + if F.left i < F.left (F.next i) then 0 else 1 := by
  split_ifs with hi
  · simpa only [add_zero] using F.right_lt_left_of_left_lt hi
  · have h := F.right_lt_one i
    have h' := F.left_pos (F.next i)
    linarith

theorem isOpen_gap (i : I) : IsOpen (F.gap i) := by
  rw [F.gap_eq_image]
  exact QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo

theorem isConnected_gap (i : I) : IsConnected (F.gap i) := by
  rw [F.gap_eq_image]
  exact (isConnected_Ioo (F.gap_interval_nonempty i)).image _
    (AddCircle.continuous_mk' (1 : ℝ)).continuousOn

theorem gap_disjoint {i j : I} (hij : i ≠ j) : Disjoint (F.gap i) (F.gap j) :=
  Set.disjoint_left.mpr (fun _ hi hj => hij (F.gapCoordinate_unique hi hj))

theorem iUnion_gap [Nonempty I] : (⋃ i, F.gap i) = (closure (⋃ i, F.arc i))ᶜ := by
  rw [closure_iUnion_of_finite]
  simp_rw [F.closure_arc]
  ext x
  constructor
  · intro hxg hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hxg
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
    have hj' : circleCoordinate x ∈ Set.Icc (F.left j) (F.right j) := by
      apply (coe_mem_closed_arc_iff (F.left_pos j) (F.right_lt_one j) (circleCoordinate_mem x)).mp
      simpa only [coe_circleCoordinate] using hj
    exact F.gapCoordinate_avoids hi j hj'
  · intro hx
    obtain ⟨i, hi⟩ := F.exists_gapCoordinate (circleCoordinate x) (fun j hj =>
      hx (Set.mem_iUnion.mpr ⟨j, circleCoordinate x, hj, coe_circleCoordinate x⟩))
    exact Set.mem_iUnion.mpr ⟨i, hi⟩

/-- A successor gap is exactly the connected component containing any one of
its points, in the complement of the closed domain family. -/
theorem gap_eq_connectedComponentIn [Nonempty I] (i : I) {x : StandardCircle}
    (hx : x ∈ F.gap i) :
    F.gap i = connectedComponentIn (closure (⋃ j, F.arc j))ᶜ x := by
  rw [← F.iUnion_gap]
  exact (PingPong.connectedComponentIn_open_family F.gap F.isOpen_gap
    (fun j => (F.isConnected_gap j).isPreconnected) (fun _ _ hij => F.gap_disjoint hij) hx).symm

theorem arc_eq_sbtw (i : I) :
    F.arc i = {x | sbtw (F.left i : StandardCircle) x (F.right i)} := by
  ext x
  rw [Set.mem_ofPred_eq, circle_sbtw_coordinate_iff (F.left_pos i)
    ((F.left_lt_right i).trans (F.right_lt_one i))
    ((F.left_pos i).trans (F.left_lt_right i)) (F.right_lt_one i) (F.left_lt_right i).ne,
    ite_eq_left (F.left_lt_right i)]
  have h := coe_mem_open_arc_iff (F.left_pos i) (F.right_lt_one i) (circleCoordinate_mem x)
  simpa only [coe_circleCoordinate, Set.mem_Ioo, arc] using h

theorem gap_eq_sbtw (i : I) :
    F.gap i = {x | sbtw (F.right i : StandardCircle) x (F.left (F.next i))} := by
  have hr := (F.left_pos i).trans (F.left_lt_right i)
  have hl1 := (F.left_lt_right (F.next i)).trans (F.right_lt_one (F.next i))
  ext x
  by_cases hi : F.left i < F.left (F.next i)
  · have hi' := F.right_lt_left_of_left_lt hi
    rw [Set.mem_ofPred_eq, circle_sbtw_coordinate_iff hr (F.right_lt_one i)
      (F.left_pos _) hl1 hi'.ne, ite_eq_left hi']
    simp only [gap, Set.mem_ofPred_eq, GapCoordinate, hi, ↓reduceIte]
  · have hi' : F.left (F.next i) < F.right i := (le_of_not_gt hi).trans_lt (F.left_lt_right i)
    rw [Set.mem_ofPred_eq, circle_sbtw_coordinate_iff hr (F.right_lt_one i)
      (F.left_pos _) hl1 hi'.ne', ite_eq_right (not_lt_of_ge hi'.le)]
    simp only [gap, Set.mem_ofPred_eq, GapCoordinate, hi, ↓reduceIte]

end CircleIntervalFamily
end FnZPositiveCones.CircularDynamics
