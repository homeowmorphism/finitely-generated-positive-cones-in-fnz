module

public import FnZPositiveCones.External.NoncofinalPrimitiveEntry

@[expose] public section

/-! Hölder's theorem for a group acting freely by increasing real automorphisms. -/
namespace FnZPositiveCones

universe u
variable {G : Type u} [Group G]

/-- A bi-invariant order in which every positive element is cofinal is commutative. -/
theorem LeftGroupOrder.commute_of_positive_cofinal (O : LeftGroupOrder G)
    (hr : ∀ a b c : G, O.order.le a b → O.order.le (a * c) (b * c))
    (hc : ∀ z : G, O.order.lt 1 z → O.IsCofinal z) (a b : G) : Commute a b := by
  classical
  let := O.order
  have hrlt (a b c : G) (h : a < b) : a * c < b * c :=
    lt_of_le_of_ne (hr a b c h.le) (fun he => h.ne (mul_right_cancel he))
  by_cases hd : ∀ ε : G, 1 < ε → ∃ z : G, 1 < z ∧ z < ε
  · have hsmall (ε : G) (hε : 1 < ε) : ∃ z : G, 1 < z ∧ z * z < ε := by
      obtain ⟨y, hy, hyε⟩ := hd ε hε
      have hyε' : 1 < y⁻¹ * ε := (O.lt_iff_one_lt y ε).mp hyε
      obtain ⟨z, hz, hzy⟩ := hd (min y (y⁻¹ * ε)) (lt_min hy hyε')
      refine ⟨z, hz, (hrlt z y z (hzy.trans_le (min_le_left _ _))).trans ?_⟩
      simpa only [mul_inv_cancel_left] using
        O.mul_lt_mul_left y (hzy.trans_le (min_le_right _ _))
    have hnot (a b : G) : ¬ a * b < b * a := by
      intro hab
      let ε := (a * b)⁻¹ * (b * a)
      have hε : 1 < ε := (O.lt_iff_one_lt _ _).mp hab
      obtain ⟨z, hz, hzz⟩ := hsmall ε hε
      obtain ⟨m, hm, _⟩ := O.exists_unique_power_floor hz (hc z hz) a
      obtain ⟨n, hn, _⟩ := O.exists_unique_power_floor hz (hc z hz) b
      have hlo : z ^ (m + n) ≤ a * b := by
        rw [zpow_add]
        exact (hr _ _ _ hm.1).trans (O.mul_le_mul_left _ _ a hn.1)
      have hup : b * a < z ^ (n + 1) * z ^ (m + 1) :=
        (hrlt _ _ _ hn.2).trans (O.mul_lt_mul_left _ hm.2)
      have he : z ^ (n + 1) * z ^ (m + 1) = z ^ (m + n) * (z * z) := by
        rw [← zpow_two z, ← zpow_add, ← zpow_add]
        congr 1
        omega
      rw [he] at hup
      have hbound : b * a < (a * b) * (z * z) := hup.trans_le (hr _ _ _ hlo)
      have hh := O.mul_lt_mul_left (a * b) hzz
      have heε : (a * b) * ε = b * a := by dsimp [ε]; group
      rw [heε] at hh
      exact (hbound.trans hh).false
    exact show a * b = b * a from le_antisymm (le_of_not_gt (hnot b a)) (le_of_not_gt (hnot a b))
  · push Not at hd
    obtain ⟨z, hz, hleast⟩ := hd
    have hpowers (g : G) : ∃ m : ℤ, g = z ^ m := by
      have hmem := O.fundamentalRepresentative_mem hz (hc z hz) g
      have he : O.fundamentalRepresentative hz (hc z hz) g = 1 := by
        apply le_antisymm _ hmem.1
        by_contra h
        exact (not_lt_of_ge (hleast _ (lt_of_not_ge h))) hmem.2
      refine ⟨O.powerFloor hz (hc z hz) g, ?_⟩
      have hh := congrArg (fun x : G => z ^ O.powerFloor hz (hc z hz) g * x) he
      simpa only [LeftGroupOrder.fundamentalRepresentative, ← mul_assoc, ← zpow_add,
        add_neg_cancel, zpow_zero, one_mul, mul_one] using hh
    obtain ⟨m, rfl⟩ := hpowers a
    obtain ⟨n, rfl⟩ := hpowers b
    exact (Commute.refl z).zpow_zpow m n

namespace OrderedActions
open NoncofinalDynamics

/-- Freeness at every point makes each real orbit map injective. -/
theorem orbit_injective_of_free (ρ : G →* (ℝ ≃o ℝ))
    (hf : ∀ g : G, g ≠ 1 → ∀ x : ℝ, ρ g x ≠ x) (x : ℝ) :
    Function.Injective (fun g => ρ g x) := by
  intro g h he
  by_contra hne
  apply hf (h⁻¹ * g) (by intro hh; exact hne (inv_mul_eq_one.mp hh).symm) x
  simp only [act_mul, he, act_inv_act]

/-- A strict comparison between two transformations holds at every point. -/
theorem action_lt_everywhere_of_free (ρ : G →* (ℝ ≃o ℝ))
    (hf : ∀ g : G, g ≠ 1 → ∀ x : ℝ, ρ g x ≠ x)
    {g h : G} {x : ℝ} (hx : ρ g x < ρ h x) (y : ℝ) : ρ g y < ρ h y := by
  have hne : g⁻¹ * h ≠ 1 := by
    intro he
    have he' := inv_mul_eq_one.mp he
    exact hx.ne (congrArg (fun k => ρ k x) he')
  have hp : x < ρ (g⁻¹ * h) x := by
    simpa only [act_mul, act_inv_act] using (ρ g⁻¹).strictMono hx
  have hh := NoncofinalPrimitiveEntry.positive_everywhere_of_no_fixed
    (ρ (g⁻¹ * h)) (hf _ hne) hp y
  simpa only [act_mul, act_act_inv] using (ρ g).strictMono hh

/-- Hölder's theorem: a group acting freely on the line is abelian. The
hypothesis applies to every point and contains no commutativity assumption. -/
theorem commute_of_free_real_action (ρ : G →* (ℝ ≃o ℝ))
    (hf : ∀ g : G, g ≠ 1 → ∀ x : ℝ, ρ g x ≠ x) (g h : G) : Commute g h := by
  classical
  let O : LeftGroupOrder G := {
    order := LinearOrder.lift' (fun g => ρ g 0) (orbit_injective_of_free ρ hf 0)
    mul_le_mul_left := by
      intro a b c hab
      change ρ (c * a) 0 ≤ ρ (c * b) 0
      change ρ a 0 ≤ ρ b 0 at hab
      simpa only [act_mul] using (ρ c).monotone hab }
  apply O.commute_of_positive_cofinal
  · intro a b c hab
    change ρ a 0 ≤ ρ b 0 at hab
    change ρ (a * c) 0 ≤ ρ (b * c) 0
    rcases hab.eq_or_lt with he | hlt
    · have he' := orbit_injective_of_free ρ hf 0 he
      subst b
      rfl
    · simpa only [act_mul] using (action_lt_everywhere_of_free ρ hf hlt (ρ c 0)).le
  · intro z hz
    by_contra hnc
    obtain ⟨x, hx⟩ := exists_fixed_of_not_cofinal ρ O z 0 (fun _ _ => Iff.rfl) hnc
    exact hf z (by intro he; subst z; change ρ 1 0 < ρ 1 0 at hz; exact (lt_irrefl _) hz) x hx

end OrderedActions
end FnZPositiveCones
