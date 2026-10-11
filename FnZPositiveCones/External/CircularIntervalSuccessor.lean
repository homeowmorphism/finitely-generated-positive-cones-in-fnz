module

public import FnZPositiveCones.External.CircularIntervalFamilies

@[expose] public section

/-! Adjacency and exact complement coverage for sorted component intervals. -/
namespace FnZPositiveCones.CircularDynamics.CircleIntervalFamily
universe u
variable {I : Type u} (F : CircleIntervalFamily I)

theorem right_le_right_of_left_le {i j : I} (hij : F.left i ≤ F.left j) :
    F.right i ≤ F.right j := by
  rcases hij.lt_or_eq with h | h
  · exact ((F.right_lt_left_of_left_lt h).trans (F.left_lt_right j)).le
  · exact (congrArg F.right (F.left_injective h)).le

/-- In the sorted enumeration, rotation either moves to the immediately
following endpoint, or moves from the greatest endpoint to the least one. -/
theorem next_order [Fintype I] (i : I) :
    (F.left i < F.left (F.next i) ∧
      ∀ j, F.left i < F.left j → F.left (F.next i) ≤ F.left j) ∨
    (F.left (F.next i) ≤ F.left i ∧
      ∀ j, F.left (F.next i) ≤ F.left j ∧ F.left j ≤ F.left i) := by
  obtain ⟨k, rfl⟩ := F.enumeration.surjective i
  rw [F.next_enumeration]
  have hm := F.enumeration_strictMono
  have hrot :
      (k.val + 1 < Fintype.card I ∧ (finRotate _ k).val = k.val + 1) ∨
      (k.val + 1 = Fintype.card I ∧ (finRotate _ k).val = 0) := by
    generalize hn : Fintype.card I = n at k ⊢
    cases n with
    | zero => exact k.elim0
    | succ n =>
      by_cases hk : k = Fin.last n
      · right
        subst k
        simp
      · left
        refine ⟨?_, coe_finRotate_of_ne_last hk⟩
        have hh := Fin.val_lt_last hk
        omega
  rcases hrot with ⟨hk, hr⟩ | ⟨hk, hr⟩
  · left
    refine ⟨hm (show k < finRotate _ k by change k.val < _; omega), ?_⟩
    intro j hj
    obtain ⟨l, rfl⟩ := F.enumeration.surjective j
    apply hm.monotone
    have hkl : k < l := hm.lt_iff_lt.mp hj
    change (finRotate _ k).val ≤ l.val
    change k.val < l.val at hkl
    omega
  · right
    refine ⟨hm.monotone (show finRotate _ k ≤ k by change _ ≤ k.val; omega), ?_⟩
    intro j
    obtain ⟨l, rfl⟩ := F.enumeration.surjective j
    constructor <;> apply hm.monotone
    · change (finRotate _ k).val ≤ l.val
      omega
    · change l.val ≤ k.val
      have hl := l.isLt
      omega

/-- The open interval after a component, expressed in the fundamental chart.
The second branch is the unique interval crossing the cut. -/
def GapCoordinate [Fintype I] (i : I) (t : ℝ) : Prop :=
  if F.left i < F.left (F.next i) then F.right i < t ∧ t < F.left (F.next i)
  else F.right i < t ∨ t < F.left (F.next i)

theorem gapCoordinate_avoids [Fintype I] {i : I} {t : ℝ}
    (ht : F.GapCoordinate i t) (j : I) : t ∉ Set.Icc (F.left j) (F.right j) := by
  intro hj
  rcases F.next_order i with ⟨hi, hnext⟩ | ⟨hi, hext⟩
  · rw [GapCoordinate, ite_eq_left hi] at ht
    rcases le_or_gt (F.left j) (F.left i) with hji | hij
    · exact not_lt_of_ge (hj.2.trans (F.right_le_right_of_left_le hji)) ht.1
    · exact not_lt_of_ge ((hnext j hij).trans hj.1) ht.2
  · rw [GapCoordinate, ite_eq_right (not_lt_of_ge hi)] at ht
    rcases ht with ht | ht
    · exact not_lt_of_ge (hj.2.trans (F.right_le_right_of_left_le (hext j).2)) ht
    · exact not_lt_of_ge ((hext j).1.trans hj.1) ht

/-- Every point outside the finite closed intervals belongs to an actual
successor gap. The proof includes points on either side of the chart cut. -/
theorem exists_gapCoordinate [Fintype I] [Nonempty I] (t : ℝ)
    (ht : ∀ j, t ∉ Set.Icc (F.left j) (F.right j)) : ∃ i, F.GapCoordinate i t := by
  classical
  let B := Finset.univ.filter (fun i => F.left i ≤ t)
  by_cases hB : B.Nonempty
  · obtain ⟨i, hi, hmax⟩ := B.exists_max_image F.left hB
    have hli : F.left i ≤ t := (Finset.mem_filter.mp hi).2
    have hri : F.right i < t := lt_of_not_ge (fun hh => ht i ⟨hli, hh⟩)
    refine ⟨i, ?_⟩
    unfold GapCoordinate
    split_ifs with hnext
    · refine ⟨hri, lt_of_not_ge ?_⟩
      intro hnt
      have hnB : F.next i ∈ B := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnt⟩
      exact not_lt_of_ge (hmax _ hnB) hnext
    · exact Or.inl hri
  · obtain ⟨i, _, hmax⟩ := Finset.univ.exists_max_image F.left Finset.univ_nonempty
    have hnext : ¬ F.left i < F.left (F.next i) :=
      not_lt_of_ge (hmax _ (Finset.mem_univ _))
    refine ⟨i, ?_⟩
    rw [GapCoordinate, ite_eq_right hnext]
    right
    apply lt_of_not_ge
    intro hn
    exact hB ⟨F.next i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn⟩⟩

/-- The gap is unique, not merely a member of an arbitrary finite cover. -/
theorem gapCoordinate_unique [Fintype I] {i j : I} {t : ℝ}
    (hi : F.GapCoordinate i t) (hj : F.GapCoordinate j t) : i = j := by
  by_contra hne
  have aux (i j : I) (hij : F.left i < F.left j)
      (hi : F.GapCoordinate i t) (hj : F.GapCoordinate j t) : False := by
    rcases F.next_order i with ⟨hii, hni⟩ | ⟨hii, hni⟩
    · rw [GapCoordinate, ite_eq_left hii] at hi
      have htl : t < F.left j := hi.2.trans_le (hni j hij)
      rcases F.next_order j with ⟨hjj, hnj⟩ | ⟨hjj, hnj⟩
      · rw [GapCoordinate, ite_eq_left hjj] at hj
        exact (not_lt_of_ge (htl.trans (F.left_lt_right j)).le) hj.1
      · rw [GapCoordinate, ite_eq_right (not_lt_of_ge hjj)] at hj
        rcases hj with hj | hj
        · exact (not_lt_of_ge (htl.trans (F.left_lt_right j)).le) hj
        · exact (lt_irrefl t) (hj.trans_le ((hnj i).1.trans ((F.left_lt_right i).le.trans hi.1.le)))
    · exact (not_lt_of_ge (hni j).2) hij
  rcases lt_or_gt_of_ne (fun he => hne (F.left_injective he)) with h | h
  · exact aux i j h hi hj
  · exact aux j i h hj hi

end FnZPositiveCones.CircularDynamics.CircleIntervalFamily
