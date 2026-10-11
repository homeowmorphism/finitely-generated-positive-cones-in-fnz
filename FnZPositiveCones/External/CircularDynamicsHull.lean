module

public import FnZPositiveCones.External.CircularDynamicsDomains

@[expose] public section

/-! Actual gap-filled color domains, rather than an arbitrary finite arc cover. -/
namespace FnZPositiveCones
namespace CircularDynamics

/-- Fill precisely the intervals whose endpoints and all intervening points of
`K` have one color. This includes singleton colored points. -/
def colorFilledHull {C : Type*} (K : Set ℝ) (color : ℝ → C) (c : C) : Set ℝ :=
  {x | ∃ a ∈ K, ∃ b ∈ K, a ≤ x ∧ x ≤ b ∧
    ∀ z ∈ K, z ∈ Set.Icc a b → color z = c}

theorem mem_colorFilledHull_of_mem {C : Type*} {K : Set ℝ} {color : ℝ → C}
    {x : ℝ} (hx : x ∈ K) : x ∈ colorFilledHull K color (color x) := by
  refine ⟨x, hx, x, hx, le_rfl, le_rfl, ?_⟩
  intro z _ hz
  exact congrArg color (le_antisymm hz.2 hz.1)

theorem colorFilledHull_inter {C : Type*} (K : Set ℝ) (color : ℝ → C) (c : C) :
    colorFilledHull K color c ∩ K = {x | x ∈ K ∧ color x = c} := by
  ext x
  constructor
  · rintro ⟨⟨a, ha, b, hb, hax, hxb, hmono⟩, hx⟩
    exact ⟨hx, hmono x hx ⟨hax, hxb⟩⟩
  · rintro ⟨hx, hc⟩
    exact ⟨hc ▸ mem_colorFilledHull_of_mem hx, hx⟩

/-- Filling same-color gaps never creates an intersection of two color domains. -/
theorem colorFilledHull_disjoint {C : Type*} (K : Set ℝ) (color : ℝ → C)
    {c d : C} (hcd : c ≠ d) :
    Disjoint (colorFilledHull K color c) (colorFilledHull K color d) := by
  apply Set.disjoint_left.mpr
  rintro x ⟨a, ha, b, hb, hax, hxb, hm⟩ ⟨u, hu, v, hv, hux, hxv, hn⟩
  have hzK : max a u ∈ K := by
    rcases le_total a u with h | h
    · simpa only [max_eq_right h] using hu
    · simpa only [max_eq_left h] using ha
  have hzc : color (max a u) = c := hm _ hzK
    ⟨le_max_left _ _, max_le (hax.trans hxb) (hux.trans hxb)⟩
  have hzd : color (max a u) = d := hn _ hzK
    ⟨le_max_right _ _, max_le (hax.trans hxv) (hux.trans hxv)⟩
  exact hcd (hzc.symm.trans hzd)

/-- The actual filled domain is a finite union of closed intervals. Unlike a
finite cover, this equality includes every monochrome complementary gap. -/
theorem colorFilledHull_finite_intervals {C : Type*} (K : Set ℝ) (hK : IsCompact K)
    (color : ℝ → C)
    (hlocal : ∀ x ∈ K, ∃ ε > 0, ∀ y ∈ K, dist x y < ε → color x = color y)
    (c : C) : ∃ F : Finset (ℝ × ℝ),
      colorFilledHull K color c = ⋃ p ∈ F, Set.Icc p.1 p.2 := by
  classical
  obtain ⟨I, finI, a, b, hab, hcover, hmono, hdisj⟩ :=
    exists_finite_monochrome_intervals K hK color hlocal
  let : Fintype I := finI
  let valid : I × I → Prop := fun ij => a ij.1 ≤ b ij.2 ∧
    ∀ z ∈ K, z ∈ Set.Icc (a ij.1) (b ij.2) → color z = c
  let S := Finset.univ.filter valid
  let F := S.image (fun ij => (a ij.1, b ij.2))
  refine ⟨F, ?_⟩
  ext x
  constructor
  · rintro ⟨u, hu, v, hv, hux, hxv, hm⟩
    obtain ⟨i, hui⟩ := hcover u hu
    obtain ⟨j, hvj⟩ := hcover v hv
    have huC : color u = c := hm u hu ⟨le_rfl, hux.trans hxv⟩
    have hvC : color v = c := hm v hv ⟨hux.trans hxv, le_rfl⟩
    have haC : color (a i) = c := (hmono i u hu hui).symm.trans huC
    have hbC : color (a j) = c := (hmono j v hv hvj).symm.trans hvC
    have hvld : valid (i, j) := by
      refine ⟨hui.1.trans (hux.trans (hxv.trans hvj.2)), ?_⟩
      intro z hz hzab
      by_cases hzu : z ≤ u
      · exact (hmono i z hz ⟨hzab.1, hzu.trans hui.2⟩).trans haC
      · by_cases hvz : v ≤ z
        · exact (hmono j z hz ⟨hvj.1.trans hvz, hzab.2⟩).trans hbC
        · exact hm z hz ⟨(lt_of_not_ge hzu).le, (lt_of_not_ge hvz).le⟩
    apply Set.mem_iUnion.mpr
    refine ⟨(a i, b j), Set.mem_iUnion.mpr ⟨?_, hui.1.trans hux, hxv.trans hvj.2⟩⟩
    exact Finset.mem_image.mpr ⟨(i, j), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvld⟩, rfl⟩
  · intro hx
    obtain ⟨p, hp, hxp⟩ := Set.mem_iUnion₂.mp hx
    obtain ⟨⟨i, j⟩, hij, rfl⟩ := Finset.mem_image.mp hp
    have hvld := (Finset.mem_filter.mp hij).2
    exact ⟨a i, (hab i).1, b j, (hab j).2.1, hxp.1, hxp.2, hvld.2⟩

/-- Compactness of each actual filled color domain follows from the proved
finite interval decomposition. -/
theorem isCompact_colorFilledHull {C : Type*} (K : Set ℝ) (hK : IsCompact K)
    (color : ℝ → C)
    (hlocal : ∀ x ∈ K, ∃ ε > 0, ∀ y ∈ K, dist x y < ε → color x = color y)
    (c : C) : IsCompact (colorFilledHull K color c) := by
  obtain ⟨F, hF⟩ := colorFilledHull_finite_intervals K hK color hlocal c
  rw [hF]
  exact F.finite_toSet.isCompact_biUnion (fun _ _ => isCompact_Icc)


/-- Increasing transport of the closed set and its colors transports the full
gap-filled domain. Both forward and inverse set membership are explicit. -/
theorem mapsTo_colorFilledHull {C D : Type*} (K L : Set ℝ)
    (color : ℝ → C) (targetColor : ℝ → D) (c : C) (d : D) (f : ℝ ≃o ℝ)
    (hf : Set.MapsTo f K L) (hi : Set.MapsTo f.symm L K)
    (hcolor : ∀ x ∈ K, color x = c → targetColor (f x) = d) :
    Set.MapsTo f (colorFilledHull K color c) (colorFilledHull L targetColor d) := by
  rintro x ⟨a, ha, b, hb, hax, hxb, hm⟩
  refine ⟨f a, hf ha, f b, hf hb, f.monotone hax, f.monotone hxb, ?_⟩
  intro z hz hzi
  have hpre : f.symm z ∈ Set.Icc a b := by
    constructor
    · exact (f.le_iff_le).mp (by simpa using hzi.1)
    · exact (f.le_iff_le).mp (by simpa using hzi.2)
  simpa using hcolor (f.symm z) (hi hz) (hm _ (hi hz) hpre)

end CircularDynamics
end FnZPositiveCones
