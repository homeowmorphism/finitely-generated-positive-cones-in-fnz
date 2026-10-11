module

public import FnZPositiveCones.External.OrderedActionsGaps
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

@[expose] public section

/-! Discreteness of cyclic real orbits and the tight-realization successor adapter. -/
namespace FnZPositiveCones
namespace OrderedActions
universe u
variable {G : Type u} [Group G]

/-- Every orbit of an increasing cyclic action on the line has a right-hand
empty interval, even if the action is not faithful. -/
theorem cyclic_real_orbit_right_gap [IsCyclic G] (ρ : G →* (ℝ ≃o ℝ)) (x : ℝ) :
    ∃ ε > 0, ∀ g, ¬ (x < ρ g x ∧ ρ g x < x + ε) := by
  obtain ⟨a, ha⟩ := IsCyclic.exists_generator (α := G)
  have hpos (b : G) (hb : x < ρ b x) (hgen : ∀ g, g ∈ Subgroup.zpowers b) :
      ∃ ε > 0, ∀ g, ¬ (x < ρ g x ∧ ρ g x < x + ε) := by
    refine ⟨ρ b x - x, sub_pos.mpr hb, ?_⟩
    intro g hg
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hgen g)
    rw [map_zpow] at hg
    have hm := realAut_orbit_strictMono (ρ b) x hb
    have hn0 : (0 : ℤ) < n := hm.lt_iff_lt.mp (by simpa using hg.1)
    have hn1 : n < (1 : ℤ) := hm.lt_iff_lt.mp (by simpa using hg.2)
    omega
  by_cases hfix : ρ a x = x
  · have hp : ∀ n : ℤ, ((ρ a) ^ n) x = x := by
      have hinv : (ρ a)⁻¹ x = x := by
        apply (ρ a).injective
        simpa only [RelIso.apply_inv_self] using hfix.symm
      intro n
      induction n using Int.induction_on with
      | zero => simp
      | succ n ih => simp only [zpow_add, zpow_one, realAut_mul_apply, ih, hfix]
      | pred n ih => simp only [zpow_sub, zpow_one, realAut_mul_apply, hinv, ih]
    refine ⟨1, zero_lt_one, ?_⟩
    intro g hg
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp (ha g)
    rw [map_zpow, hp] at hg
    exact lt_irrefl _ hg.1
  · rcases lt_or_gt_of_ne hfix with hneg | hpos'
    · apply hpos a⁻¹
      · have hh := (ρ a).symm.strictMono hneg
        rw [map_inv]
        change x < (ρ a).symm x
        simpa only [(ρ a).symm_apply_apply] using hh
      · intro g
        obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (ha g)
        apply Subgroup.mem_zpowers_iff.mpr
        exact ⟨-n, by simpa only [inv_zpow, zpow_neg, inv_inv] using hn⟩
    · exact hpos a hpos' ha

end OrderedActions

namespace TightRealization
universe u
variable {G : Type u} [Group G] {O : LeftGroupOrder G}

/-- A real orbit's empty right neighborhood gives an actual least-positive
element, using the checked gap property of a tight realization. -/
theorem exists_leastPositive_of_right_gap (R : TightRealization O)
    {ε : ℝ} (hε : 0 < ε)
    (hgap : ∀ g, ¬ (R.base < R.action g R.base ∧ R.action g R.base < R.base + ε)) :
    ∃ a : G, O.IsLeastPositive a := by
  let := O.order
  have hd : Disjoint (Set.Ioo R.base (R.base + ε))
      (closure (Set.range (fun g => R.action g R.base))) := by
    apply Disjoint.closure_right _ isOpen_Ioo
    apply Set.disjoint_left.mpr
    rintro _ hx ⟨g, rfl⟩
    exact hgap g hx
  have hx : R.base + ε / 2 ∈ Set.Ioo R.base (R.base + ε) := by constructor <;> linarith
  obtain ⟨g, h, hg, hh, hgh⟩ := R.orbit_gap (R.base + ε / 2)
    (fun hc => Set.disjoint_left.mp hd hx hc)
  have hbase : R.base ∈ closure (Set.range (fun g => R.action g R.base)) :=
    subset_closure ⟨1, by simp⟩
  have hlo : R.base ≤ R.action g R.base := by
    by_contra hn
    exact Set.disjoint_left.mp hgh ⟨lt_of_not_ge hn, hx.1.trans hh⟩ hbase
  have hgeq : R.action g R.base = R.base := by
    by_contra hn
    exact hgap g ⟨lt_of_le_of_ne hlo (Ne.symm hn), hg.trans hx.2⟩
  have hgone : g = 1 := R.orbit_injective (by simpa using hgeq)
  subst g
  have hcov := R.orbit_gap_covBy (hg.trans hh) hgh
  refine ⟨h, hcov.1, ?_⟩
  intro k hk
  exact le_of_not_gt (fun hkh => hcov.2 hk hkh)

end TightRealization
end FnZPositiveCones
