module

public import FnZPositiveCones.External.CircularDynamicsSeparation

@[expose] public section

/-! Mixed colors in a compact interval force an actual accumulation point
when no differently colored full-orbit adjacent pair is allowed there. -/

namespace FnZPositiveCones.CircularDynamics
universe u

/-- This statement uses adjacency in the whole set `S`. Adjacency in a finite
trace family is used only after compactness has made `S ∩ [a,b]` finite. -/
theorem exists_accPt_between_of_no_mixed_adjacent {C : Type u}
    (S : Set ℝ) (color : ℝ → C) {a b : ℝ}
    (ha : a ∈ S) (hb : b ∈ S) (hab : a < b) (hcolor : color a ≠ color b)
    (haacc : ¬ AccPt a (Filter.principal S)) (hbacc : ¬ AccPt b (Filter.principal S))
    (hbetween : ∀ u ∈ S, ∀ v ∈ S, a ≤ u → u < v → v ≤ b → color u ≠ color v →
      ∃ z ∈ S, u < z ∧ z < v) :
    ∃ x ∈ Set.Ioo a b, AccPt x (Filter.principal S) := by
  classical
  by_contra hnone
  have hfinite : (S ∩ Set.Icc a b).Finite := by
    by_contra hfin
    have hinfinite : (S ∩ Set.Icc a b).Infinite := hfin
    obtain ⟨x, hxab, hx⟩ := hinfinite.exists_accPt_of_subset_isCompact
      isCompact_Icc (Set.inter_subset_right : S ∩ Set.Icc a b ⊆ Set.Icc a b)
    have hxS : AccPt x (Filter.principal S) :=
      hx.mono (Filter.principal_mono.mpr Set.inter_subset_left)
    have hxa : x ≠ a := fun he => haacc (he ▸ hxS)
    have hxb : x ≠ b := fun he => hbacc (he ▸ hxS)
    exact hnone ⟨x, ⟨lt_of_le_of_ne hxab.1 (Ne.symm hxa),
      lt_of_le_of_ne hxab.2 hxb⟩, hxS⟩
  obtain ⟨u, hu, v, hv, hau, huv, hvb, hc, hgap⟩ :=
    exists_adjacent_distinct_colors hfinite.toFinset color
      (a := a) (b := b)
      (hfinite.mem_toFinset.mpr ⟨ha, le_rfl, hab.le⟩)
      (hfinite.mem_toFinset.mpr ⟨hb, hab.le, le_rfl⟩) hab hcolor
  have huS : u ∈ S := (hfinite.mem_toFinset.mp hu).1
  have hvS : v ∈ S := (hfinite.mem_toFinset.mp hv).1
  obtain ⟨z, hzS, huz, hzv⟩ := hbetween u huS v hvS hau huv hvb hc
  exact hgap z (hfinite.mem_toFinset.mpr
    ⟨hzS, hau.trans huz.le, hzv.le.trans hvb⟩) ⟨huz, hzv⟩

end FnZPositiveCones.CircularDynamics
