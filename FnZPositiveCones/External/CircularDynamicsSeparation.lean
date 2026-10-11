module

public import FnZPositiveCones.External.CircularDynamics
public import FnZPositiveCones.External.CircularDynamicsLocal
public import Mathlib.Data.Finset.Max

@[expose] public section

/-! Finite trajectory refinement in the local separation argument. -/
namespace FnZPositiveCones
namespace CircularDynamics
universe u v w

/-- Distinct endpoint colors force an adjacent pair of different colors inside
the same interval. The conclusion excludes all finite-set points from the open
interval; it does not assert that endpoints avoid other trajectories. -/
theorem exists_adjacent_distinct_colors {A : Type u} [LinearOrder A] {C : Type v}
    (S : Finset A) (color : A → C) {a b : A} (ha : a ∈ S) (hb : b ∈ S)
    (hab : a < b) (hc : color a ≠ color b) :
    ∃ u ∈ S, ∃ v ∈ S, a ≤ u ∧ u < v ∧ v ≤ b ∧ color u ≠ color v ∧
      ∀ z ∈ S, ¬(u < z ∧ z < v) := by
  classical
  let T := S.filter (fun z => a < z ∧ color z ≠ color a)
  have hT : T.Nonempty := ⟨b, Finset.mem_filter.mpr ⟨hb, hab, Ne.symm hc⟩⟩
  let v := T.min' hT
  have hv : v ∈ T := T.min'_mem hT
  have hvS : v ∈ S := (Finset.mem_filter.mp hv).1
  have hav : a < v := (Finset.mem_filter.mp hv).2.1
  have hvc : color v ≠ color a := (Finset.mem_filter.mp hv).2.2
  have hvb : v ≤ b := T.min'_le b (Finset.mem_filter.mpr ⟨hb, hab, Ne.symm hc⟩)
  let U := S.filter (fun z => a ≤ z ∧ z < v)
  have hU : U.Nonempty := ⟨a, Finset.mem_filter.mpr ⟨ha, le_rfl, hav⟩⟩
  let u := U.max' hU
  have hu : u ∈ U := U.max'_mem hU
  have huS : u ∈ S := (Finset.mem_filter.mp hu).1
  have hau : a ≤ u := (Finset.mem_filter.mp hu).2.1
  have huv : u < v := (Finset.mem_filter.mp hu).2.2
  have huc : color u = color a := by
    by_contra hne
    have hau' : a < u := lt_of_le_of_ne hau (fun he => hne (congrArg color he.symm))
    have hvu : v ≤ u := T.min'_le u (Finset.mem_filter.mpr ⟨huS, hau', hne⟩)
    exact not_le_of_gt huv hvu
  refine ⟨u, huS, v, hvS, hau, huv, hvb, ?_, ?_⟩
  · simpa only [huc] using Ne.symm hvc
  · intro z hz hzuv
    have hzu : z ≤ u := U.le_max' z (Finset.mem_filter.mpr ⟨hz, hau.trans hzuv.1.le, hzuv.2⟩)
    exact not_le_of_gt hzuv.1 hzu

/-- Every trace of a suffix is already part of the original trace. -/
theorem wordTrace_subset_of_isSuffix {ι : Type u} {X : Type v}
    (ρ : ι → Equiv.Perm X) (x : X) {v w : List (ι × Bool)} (hvw : v.IsSuffix w) :
    ∀ y ∈ wordTrace ρ x v, y ∈ wordTrace ρ x w := by
  obtain ⟨p, rfl⟩ := hvw
  induction p with
  | nil => exact fun _ h => h
  | cons s p ih =>
      intro y hy
      exact List.mem_cons_of_mem _ (ih y hy)

/-- A trajectory in a coordinate chart can be refined within the same finite
family, with its labels retained, using the real order of its points. -/
theorem exists_adjacent_colored_labels {A : Type u} {C : Type v}
    (S : Finset A) (coordinate : A → ℝ) (color : A → C)
    (hinj : Set.InjOn coordinate (S : Set A))
    {a b : A} (ha : a ∈ S) (hb : b ∈ S)
    (hab : coordinate a < coordinate b) (hc : color a ≠ color b) :
    ∃ u ∈ S, ∃ v ∈ S,
      coordinate a ≤ coordinate u ∧ coordinate u < coordinate v ∧ coordinate v ≤ coordinate b ∧
      color u ≠ color v ∧ ∀ z ∈ S, ¬(coordinate u < coordinate z ∧ coordinate z < coordinate v) := by
  classical
  let : LinearOrder {a // a ∈ S} := LinearOrder.lift' (fun a => coordinate a.val)
    (fun a b he => Subtype.ext (hinj a.property b.property he))
  let a' : {a // a ∈ S} := ⟨a, ha⟩
  let b' : {a // a ∈ S} := ⟨b, hb⟩
  obtain ⟨u, _, v, _, hau, huv, hvb, hcuv, hgap⟩ :=
    exists_adjacent_distinct_colors Finset.univ (fun z : {a // a ∈ S} => color z.val)
      (a := a') (b := b') (Finset.mem_univ _) (Finset.mem_univ _) hab hc
  refine ⟨u.val, u.property, v.val, v.property, hau, huv, hvb, hcuv, ?_⟩
  intro z hz
  exact hgap ⟨z, hz⟩ (Finset.mem_univ _)

/-- The actual supported move used after trajectory separation: cross one endpoint
past the other, fix every forbidden finite trace point, and keep the displacement
uniformly small. The closed interval must avoid the forbidden points. -/
theorem exists_small_crossing_fixing_finset (F : Finset ℝ) (a b ε : ℝ)
    (hab : a < b) (hε : b - a < ε)
    (havoid : ∀ y ∈ F, y ∉ Set.Icc a b) :
    ∃ e : ℝ ≃o ℝ, b < e a ∧ (∀ y ∈ F, e y = y) ∧ ∀ y, dist (e y) y < ε := by
  have hclosed : IsClosed (F : Set ℝ) := F.finite_toSet.isClosed
  have ha : a ∈ (F : Set ℝ)ᶜ := by
    intro hf
    exact havoid a hf ⟨le_rfl, hab.le⟩
  have hb : b ∈ (F : Set ℝ)ᶜ := by
    intro hf
    exact havoid b hf ⟨hab.le, le_rfl⟩
  obtain ⟨ra, hra, hba⟩ := Metric.mem_nhds_iff.mp (hclosed.isOpen_compl.mem_nhds ha)
  obtain ⟨rb, hrb, hbb⟩ := Metric.mem_nhds_iff.mp (hclosed.isOpen_compl.mem_nhds hb)
  let δ := min ra (min rb ((ε - (b - a)) / 2)) / 2
  have hd : 0 < δ := by dsimp [δ]; positivity
  have hda : δ < ra := by
    have := min_le_left ra (min rb ((ε - (b - a)) / 2))
    dsimp [δ] at *
    linarith
  have hdb : δ < rb := by
    have hh := (min_le_right ra (min rb ((ε - (b - a)) / 2))).trans
      (min_le_left rb ((ε - (b - a)) / 2))
    dsimp [δ] at *
    linarith
  have hde : 2 * δ < ε - (b - a) := by
    have hh := (min_le_right ra (min rb ((ε - (b - a)) / 2))).trans
      (min_le_right rb ((ε - (b - a)) / 2))
    dsimp [δ] at *
    linarith
  have hfree : ∀ y ∈ F, y ∉ Set.Ioo (a - δ) (b + δ) := by
    intro y hy hiy
    by_cases hya : y < a
    · have hball : y ∈ Metric.ball a ra := by
        rw [Metric.mem_ball, Real.dist_eq, abs_of_neg (sub_neg.mpr hya)]
        linarith [hiy.1]
      exact hba hball hy
    · by_cases hyb : b < y
      · have hball : y ∈ Metric.ball b rb := by
          rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (sub_pos.mpr hyb)]
          linarith [hiy.2]
        exact hbb hball hy
      · exact havoid y hy ⟨le_of_not_gt hya, le_of_not_gt hyb⟩
  obtain ⟨e, hea, hfix, hsmall⟩ := exists_supported_real_orderIso_small
    (a - δ) a (b + δ / 2) (b + δ) ε (by linarith) (by linarith)
      (by linarith) (by linarith) (by linarith)
  refine ⟨e, ?_, fun y hy => hfix y (hfree y hy), hsmall⟩
  rw [hea]
  linarith

end CircularDynamics
end FnZPositiveCones
