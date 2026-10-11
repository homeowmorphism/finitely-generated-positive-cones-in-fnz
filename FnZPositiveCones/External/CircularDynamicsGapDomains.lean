module

public import FnZPositiveCones.External.CircularDynamicsHull

@[expose] public section

/-! Complementary gaps and the canonical filled color domains. -/
namespace FnZPositiveCones
namespace CircularDynamics

/-- Inside a genuine complementary interval, membership in a filled domain is
exactly the equality of the two endpoint colors. This identifies the principal
gaps used in the source's finite cutoff construction. -/
theorem realGap_mem_colorFilledHull_iff {C : Type*} (K : Set ℝ) (color : ℝ → C)
    {a b x : ℝ} (hgap : IsRealGap K a b) (hx : x ∈ Set.Ioo a b) (c : C) :
    x ∈ colorFilledHull K color c ↔ color a = c ∧ color b = c := by
  constructor
  · rintro ⟨u, hu, v, hv, hux, hxv, hm⟩
    have hua : u ≤ a := by
      by_contra h
      exact hgap.2.2.2 u hu ⟨lt_of_not_ge h, hux.trans_lt hx.2⟩
    have hbv : b ≤ v := by
      by_contra h
      exact hgap.2.2.2 v hv ⟨hx.1.trans_le hxv, lt_of_not_ge h⟩
    exact ⟨hm a hgap.1 ⟨hua, hgap.2.2.1.le.trans hbv⟩,
      hm b hgap.2.1 ⟨hua.trans hgap.2.2.1.le, hbv⟩⟩
  · rintro ⟨ha, hb⟩
    refine ⟨a, hgap.1, b, hgap.2.1, hx.1.le, hx.2.le, ?_⟩
    intro z hz hzi
    rcases eq_or_lt_of_le hzi.1 with he | he
    · exact he ▸ ha
    rcases eq_or_lt_of_le hzi.2 with he' | he'
    · exact he'.symm ▸ hb
    · exact False.elim (hgap.2.2.2 z hz ⟨he, he'⟩)

/-- A differently colored actual gap is disjoint from every filled color domain. -/
theorem realGap_disjoint_colorFilledHull {C : Type*} (K : Set ℝ) (color : ℝ → C)
    {a b : ℝ} (hgap : IsRealGap K a b) (hcolor : color a ≠ color b) (c : C) :
    Disjoint (Set.Ioo a b) (colorFilledHull K color c) := by
  apply Set.disjoint_left.mpr
  intro x hx hxd
  have hc := (realGap_mem_colorFilledHull_iff K color hgap hx c).mp hxd
  exact hcolor (hc.1.trans hc.2.symm)

/-- Filling a same-color complementary gap includes its two endpoints as well. -/
theorem realGap_Icc_subset_colorFilledHull {C : Type*} (K : Set ℝ) (color : ℝ → C)
    {a b : ℝ} (hgap : IsRealGap K a b) (hcolor : color a = color b) :
    Set.Icc a b ⊆ colorFilledHull K color (color a) := by
  intro x hx
  rcases eq_or_lt_of_le hx.1 with he | he
  · exact he ▸ mem_colorFilledHull_of_mem hgap.1
  rcases eq_or_lt_of_le hx.2 with he' | he'
  · have hb := mem_colorFilledHull_of_mem (color := color) hgap.2.1
    rw [← hcolor] at hb
    exact he'.symm ▸ hb
  · exact (realGap_mem_colorFilledHull_iff K color hgap ⟨he, he'⟩ _).mpr ⟨rfl, hcolor.symm⟩

end CircularDynamics
end FnZPositiveCones
