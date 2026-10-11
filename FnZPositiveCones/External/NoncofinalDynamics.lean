module

public import FnZPositiveCones.External.FiniteCentral

@[expose] public section

/-!
# Central power intervals in actions on the line

This makes the convex subgroup in MMRT Proposition 4.12, Claim 1, explicit
in a given order-realizing action. Composition acts on the left throughout.
-/

namespace FnZPositiveCones
namespace NoncofinalDynamics

universe u
variable {G : Type u} [Group G]
variable (ρ : G →* (ℝ ≃o ℝ))

@[simp] theorem act_one (x : ℝ) : ρ 1 x = x := by rw [map_one]; rfl

@[simp] theorem act_mul (g h : G) (x : ℝ) : ρ (g * h) x = ρ g (ρ h x) := by
  rw [map_mul]
  rfl

@[simp] theorem act_inv_act (g : G) (x : ℝ) : ρ g⁻¹ (ρ g x) = x := by
  rw [← act_mul, inv_mul_cancel, act_one]

@[simp] theorem act_act_inv (g : G) (x : ℝ) : ρ g (ρ g⁻¹ x) = x := by
  rw [← act_mul, mul_inv_cancel, act_one]

/-- Positive motion makes the integer orbit strictly increasing. -/
theorem zpow_orbit_strictMono (z : G) (x : ℝ) (hx : x < ρ z x) :
    StrictMono (fun k : ℤ => ρ (z ^ k) x) := by
  apply strictMono_int_of_lt_succ
  intro k
  simpa only [zpow_add, zpow_one, act_mul] using (ρ (z ^ k)).strictMono hx

/-- The open interval swept out by all positive and negative central powers. -/
def powerInterval (z : G) (x : ℝ) : Set ℝ :=
  {y | ∃ m n : ℤ, ρ (z ^ m) x < y ∧ y < ρ (z ^ n) x}

theorem mem_powerInterval (z : G) (x : ℝ) (hx : x < ρ z x) :
    x ∈ powerInterval ρ z x := by
  have hm := zpow_orbit_strictMono ρ z x hx
  refine ⟨-1, 1, ?_, ?_⟩
  · simpa using hm (show (-1 : ℤ) < 0 by omega)
  · simpa using hm (show (0 : ℤ) < 1 by omega)

theorem powerInterval_ordConnected (z : G) (x : ℝ) :
    Set.OrdConnected (powerInterval ρ z x) := by
  constructor
  rintro y ⟨m, n, hm, hn⟩ w ⟨p, q, hp, hq⟩ v ⟨hyv, hvw⟩
  exact ⟨m, q, hm.trans_le hyv, hvw.trans_lt hq⟩

theorem powerInterval_isOpen (z : G) (x : ℝ) : IsOpen (powerInterval ρ z x) := by
  have he : powerInterval ρ z x = ⋃ m : ℤ, ⋃ n : ℤ,
      Set.Ioo (ρ (z ^ m) x) (ρ (z ^ n) x) := by
    ext y
    simp only [powerInterval, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_Ioo]
  rw [he]
  exact isOpen_iUnion fun _ => isOpen_iUnion fun _ => isOpen_Ioo

/-- A point fixed by the generator is fixed by every integer power. -/
theorem fixed_zpow (z : G) {y : ℝ} (hy : ρ z y = y) (k : ℤ) : ρ (z ^ k) y = y := by
  apply zpow_induction_left (g := z) (P := fun g => ρ g y = y) (by simp)
  · intro g hg
    simp only [act_mul, hg, hy]
  · intro g hg
    rw [act_mul, hg]
    have h := act_inv_act ρ z y
    rwa [hy] at h

/-- The swept interval contains no fixed point of its defining element. -/
theorem powerInterval_has_no_fixed (z : G) (x : ℝ) {y : ℝ}
    (hy : y ∈ powerInterval ρ z x) : ρ z y ≠ y := by
  rintro hfix
  obtain ⟨m, n, hm, hn⟩ := hy
  rcases le_total x y with hxy | hyx
  · have h := (ρ (z ^ n)).monotone hxy
    rw [fixed_zpow ρ z hfix n] at h
    exact not_lt_of_ge h hn
  · have h := (ρ (z ^ m)).monotone hyx
    rw [fixed_zpow ρ z hfix m] at h
    exact not_lt_of_ge h hm

private theorem image_zpow_orbit (z : G) (x : ℝ) :
    ρ z '' Set.range (fun k : ℤ => ρ (z ^ k) x) =
      Set.range (fun k : ℤ => ρ (z ^ k) x) := by
  ext y
  constructor
  · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
    exact ⟨1 + k, by simp only [zpow_add, zpow_one, act_mul]⟩
  · rintro ⟨k, rfl⟩
    refine ⟨ρ (z ^ (k - 1)) x, ⟨k - 1, rfl⟩, ?_⟩
    calc
      ρ z (ρ (z ^ (k - 1)) x) = ρ (z ^ (1 + (k - 1))) x := by
        simp only [zpow_add, zpow_one, act_mul]
      _ = ρ (z ^ k) x := by rw [show 1 + (k - 1) = k by omega]

/-- A finite supremum of the integer orbit is a fixed point. -/
theorem orbit_sSup_fixed (z : G) (x : ℝ)
    (hb : BddAbove (Set.range (fun k : ℤ => ρ (z ^ k) x))) :
    ρ z (sSup (Set.range (fun k : ℤ => ρ (z ^ k) x))) =
      sSup (Set.range (fun k : ℤ => ρ (z ^ k) x)) := by
  rw [(ρ z).map_csSup' (Set.range_nonempty _) hb, image_zpow_orbit]

/-- A finite infimum of the integer orbit is a fixed point. -/
theorem orbit_sInf_fixed (z : G) (x : ℝ)
    (hb : BddBelow (Set.range (fun k : ℤ => ρ (z ^ k) x))) :
    ρ z (sInf (Set.range (fun k : ℤ => ρ (z ^ k) x))) =
      sInf (Set.range (fun k : ℤ => ρ (z ^ k) x)) := by
  rw [(ρ z).map_csInf' (Set.range_nonempty _) hb, image_zpow_orbit]

/-- The swept interval is exactly the component of the complement of the fixed
points containing the basepoint. This checks the interval used in MMRT Claim 1. -/
theorem powerInterval_eq_fixedPoint_component (z : G) (x : ℝ) (hx : x < ρ z x) :
    powerInterval ρ z x = connectedComponentIn {y : ℝ | ρ z y ≠ y} x := by
  apply Set.Subset.antisymm
  · exact (powerInterval_ordConnected ρ z x).isPreconnected.subset_connectedComponentIn
      (mem_powerInterval ρ z x hx) (fun _ hy => powerInterval_has_no_fixed ρ z x hy)
  · intro y hy
    have hxcomp : x ∈ connectedComponentIn {y : ℝ | ρ z y ≠ y} x :=
      mem_connectedComponentIn (ne_of_gt hx)
    have hconn := (isPreconnected_connectedComponentIn
      (F := {y : ℝ | ρ z y ≠ y}) (x := x)).ordConnected
    have hlower : ∃ m : ℤ, ρ (z ^ m) x < y := by
      by_contra h
      have hb : BddBelow (Set.range (fun k : ℤ => ρ (z ^ k) x)) := by
        refine ⟨y, ?_⟩
        rintro _ ⟨k, rfl⟩
        exact le_of_not_gt (fun hk => h ⟨k, hk⟩)
      have hyl : y ≤ sInf (Set.range (fun k : ℤ => ρ (z ^ k) x)) := by
        apply le_csInf (Set.range_nonempty _)
        rintro _ ⟨k, rfl⟩
        exact le_of_not_gt (fun hk => h ⟨k, hk⟩)
      have hlx : sInf (Set.range (fun k : ℤ => ρ (z ^ k) x)) ≤ x :=
        csInf_le hb ⟨0, by simp⟩
      have hlcomp := hconn.out hy hxcomp ⟨hyl, hlx⟩
      exact (connectedComponentIn_subset _ _ hlcomp) (orbit_sInf_fixed ρ z x hb)
    have hupper : ∃ n : ℤ, y < ρ (z ^ n) x := by
      by_contra h
      have hb : BddAbove (Set.range (fun k : ℤ => ρ (z ^ k) x)) := by
        refine ⟨y, ?_⟩
        rintro _ ⟨k, rfl⟩
        exact le_of_not_gt (fun hk => h ⟨k, hk⟩)
      have huy : sSup (Set.range (fun k : ℤ => ρ (z ^ k) x)) ≤ y := by
        apply csSup_le (Set.range_nonempty _)
        rintro _ ⟨k, rfl⟩
        exact le_of_not_gt (fun hk => h ⟨k, hk⟩)
      have hxu : x ≤ sSup (Set.range (fun k : ℤ => ρ (z ^ k) x)) :=
        le_csSup hb ⟨0, by simp⟩
      have hucomp := hconn.out hxcomp hy ⟨hxu, huy⟩
      exact (connectedComponentIn_subset _ _ hucomp) (orbit_sSup_fixed ρ z x hb)
    obtain ⟨m, hm⟩ := hlower
    obtain ⟨n, hn⟩ := hupper
    exact ⟨m, n, hm, hn⟩

theorem commute_zpow_apply (z : G) (hcentral : ∀ g : G, Commute z g)
    (g : G) (k : ℤ) (x : ℝ) :
    ρ g (ρ (z ^ k) x) = ρ (z ^ k) (ρ g x) := by
  rw [← act_mul, ← act_mul, ← ((hcentral g).zpow_left k).eq]

/-- A translate whose basepoint stays in the power interval maps the whole interval
into itself. This uses only centrality and bounds, not normality of the stabilizer. -/
theorem mapsTo_powerInterval (z : G) (hcentral : ∀ g : G, Commute z g)
    (x : ℝ) (g : G) (hg : ρ g x ∈ powerInterval ρ z x) :
    Set.MapsTo (ρ g) (powerInterval ρ z x) (powerInterval ρ z x) := by
  obtain ⟨a, b, ha, hb⟩ := hg
  rintro y ⟨m, n, hm, hn⟩
  refine ⟨m + a, n + b, ?_, ?_⟩
  · have h1 := (ρ (z ^ m)).strictMono ha
    have h2 := (ρ g).strictMono hm
    rw [commute_zpow_apply ρ z hcentral] at h2
    have h := h1.trans h2
    simpa only [← act_mul, ← zpow_add] using h
  · have h1 := (ρ g).strictMono hn
    have h2 := (ρ (z ^ n)).strictMono hb
    rw [commute_zpow_apply ρ z hcentral] at h1
    have h := h1.trans h2
    simpa only [← act_mul, ← zpow_add] using h

/-- The order-realizing orbit identifies membership in the algebraic bounded
subgroup with membership of its basepoint image in the open power interval. -/
theorem mem_bounded_iff_act_mem_powerInterval (O : LeftGroupOrder G)
    (z : G) (hcentral : ∀ g : G, Commute z g) (x : ℝ)
    (hreal : ∀ g h : G, O.order.le g h ↔ ρ g x ≤ ρ h x)
    (hz : O.order.lt 1 z) (g : G) :
    g ∈ O.centralBoundedSubgroup z hcentral ↔ ρ g x ∈ powerInterval ρ z x := by
  let := O.order
  have hlt (a b : G) : a < b ↔ ρ a x < ρ b x := by
    rw [lt_iff_not_ge, hreal, not_le]
  constructor
  · rintro ⟨m, n, hm, hn⟩
    have hmono := O.zpow_strictMono hz
    exact ⟨m - 1, n + 1,
      (hlt _ _).mp ((hmono (by omega : m - 1 < m)).trans_le hm),
      (hlt _ _).mp (hn.trans_lt (hmono (by omega : n < n + 1)))⟩
  · rintro ⟨m, n, hm, hn⟩
    exact ⟨m, n, (hreal _ _).mpr hm.le, (hreal _ _).mpr hn.le⟩

/-- The stabilizer of the swept interval is exactly the central bounded subgroup,
as required in MMRT's first claim. -/
theorem image_powerInterval_eq_iff_mem_bounded (O : LeftGroupOrder G)
    (z : G) (hcentral : ∀ g : G, Commute z g) (x : ℝ)
    (hreal : ∀ g h : G, O.order.le g h ↔ ρ g x ≤ ρ h x)
    (hz : O.order.lt 1 z) (g : G) :
    ρ g '' powerInterval ρ z x = powerInterval ρ z x ↔
      g ∈ O.centralBoundedSubgroup z hcentral := by
  let := O.order
  have hx : x < ρ z x := by
    have hnot : ¬ O.order.le z 1 := not_le_of_gt hz
    rw [hreal] at hnot
    simpa using lt_of_not_ge hnot
  constructor
  · intro he
    apply (mem_bounded_iff_act_mem_powerInterval ρ O z hcentral x hreal hz g).mpr
    rw [← he]
    exact ⟨x, mem_powerInterval ρ z x hx, rfl⟩
  · intro hg
    have hg' := (mem_bounded_iff_act_mem_powerInterval ρ O z hcentral x hreal hz g).mp hg
    have hgi := (mem_bounded_iff_act_mem_powerInterval ρ O z hcentral x hreal hz g⁻¹).mp
      ((O.centralBoundedSubgroup z hcentral).inv_mem hg)
    apply Set.Subset.antisymm
    · exact Set.image_subset_iff.mpr (mapsTo_powerInterval ρ z hcentral x g hg')
    · intro y hy
      exact ⟨ρ g⁻¹ y, mapsTo_powerInterval ρ z hcentral x g⁻¹ hgi hy, act_act_inv ρ g y⟩

/-- Noncofinality in an order-realizing orbit forces an actual real fixed point.
This proves the needed direction of MMRT Remark 4.8 without a dynamical axiom. -/
theorem exists_fixed_of_not_cofinal (O : LeftGroupOrder G) (z : G) (x : ℝ)
    (hreal : ∀ g h : G, O.order.le g h ↔ ρ g x ≤ ρ h x)
    (hnon : ¬ O.IsCofinal z) : ∃ y : ℝ, ρ z y = y := by
  by_contra hnone
  apply hnon
  intro g
  have hlower : ∃ m : ℤ, ρ (z ^ m) x < ρ g x := by
    by_contra h
    have hb : BddBelow (Set.range (fun k : ℤ => ρ (z ^ k) x)) := by
      refine ⟨ρ g x, ?_⟩
      rintro _ ⟨k, rfl⟩
      exact le_of_not_gt (fun hk => h ⟨k, hk⟩)
    exact hnone ⟨_, orbit_sInf_fixed ρ z x hb⟩
  have hupper : ∃ n : ℤ, ρ g x < ρ (z ^ n) x := by
    by_contra h
    have hb : BddAbove (Set.range (fun k : ℤ => ρ (z ^ k) x)) := by
      refine ⟨ρ g x, ?_⟩
      rintro _ ⟨k, rfl⟩
      exact le_of_not_gt (fun hk => h ⟨k, hk⟩)
    exact hnone ⟨_, orbit_sSup_fixed ρ z x hb⟩
  obtain ⟨m, hm⟩ := hlower
  obtain ⟨n, hn⟩ := hupper
  exact ⟨m, n, (hreal _ _).mpr hm.le, (hreal _ _).mpr hn.le⟩

/-- Centrality preserves the entire real fixed-point set under the action. -/
theorem image_central_fixedPoints (z : G) (hcentral : ∀ g : G, Commute z g) (g : G) :
    ρ g '' {y : ℝ | ρ z y = y} = {y : ℝ | ρ z y = y} := by
  have hmap (a : G) {y : ℝ} (hy : ρ z y = y) : ρ z (ρ a y) = ρ a y := by
    rw [← act_mul, (hcentral a).eq, act_mul, hy]
  apply Set.Subset.antisymm
  · rintro _ ⟨y, hy, rfl⟩
    exact hmap g hy
  · intro y hy
    exact ⟨ρ g⁻¹ y, hmap g⁻¹ hy, act_act_inv ρ g y⟩

/-- A nonempty central fixed-point set cannot be bounded above when the action
has no global fixed point. This is the initial bounded-component step in MMRT. -/
theorem central_fixedPoints_not_bddAbove (z : G) (hcentral : ∀ g : G, Commute z g)
    (hfix : ∃ y : ℝ, ρ z y = y) (hglobal : ∀ y : ℝ, ∃ g : G, ρ g y ≠ y) :
    ¬ BddAbove {y : ℝ | ρ z y = y} := by
  intro hb
  obtain ⟨g, hg⟩ := hglobal (sSup {y : ℝ | ρ z y = y})
  apply hg
  exact ((ρ g).map_csSup' (s := {y : ℝ | ρ z y = y}) hfix hb).trans
    (congrArg sSup (image_central_fixedPoints ρ z hcentral g))

/-- The same fixed-point set is unbounded below. -/
theorem central_fixedPoints_not_bddBelow (z : G) (hcentral : ∀ g : G, Commute z g)
    (hfix : ∃ y : ℝ, ρ z y = y) (hglobal : ∀ y : ℝ, ∃ g : G, ρ g y ≠ y) :
    ¬ BddBelow {y : ℝ | ρ z y = y} := by
  intro hb
  obtain ⟨g, hg⟩ := hglobal (sInf {y : ℝ | ρ z y = y})
  apply hg
  exact ((ρ g).map_csInf' (s := {y : ℝ | ρ z y = y}) hfix hb).trans
    (congrArg sInf (image_central_fixedPoints ρ z hcentral g))

/-- The component around a moving basepoint is bounded on both sides in the
noncofinal central case. -/
theorem powerInterval_bounded (z : G) (hcentral : ∀ g : G, Commute z g) (x : ℝ)
    (hfix : ∃ y : ℝ, ρ z y = y) (hglobal : ∀ y : ℝ, ∃ g : G, ρ g y ≠ y) :
    BddBelow (powerInterval ρ z x) ∧ BddAbove (powerInterval ρ z x) := by
  have hlo := central_fixedPoints_not_bddBelow ρ z hcentral hfix hglobal
  have hhi := central_fixedPoints_not_bddAbove ρ z hcentral hfix hglobal
  obtain ⟨l, hlf, hlx⟩ := (not_bddBelow_iff.mp hlo) x
  obtain ⟨r, hrf, hxr⟩ := (not_bddAbove_iff.mp hhi) x
  constructor
  · refine ⟨l, ?_⟩
    rintro y ⟨m, n, hm, hn⟩
    have h := (ρ (z ^ m)).strictMono hlx
    rw [fixed_zpow ρ z hlf m] at h
    exact (h.trans hm).le
  · refine ⟨r, ?_⟩
    rintro y ⟨m, n, hm, hn⟩
    have h := (ρ (z ^ n)).strictMono hxr
    rw [fixed_zpow ρ z hrf n] at h
    exact (hn.trans h).le

/-- The stabilizer of the actual component from MMRT is precisely the already
checked convex bounded-power subgroup. -/
theorem image_fixedPoint_component_eq_iff_mem_bounded (O : LeftGroupOrder G)
    (z : G) (hcentral : ∀ g : G, Commute z g) (x : ℝ)
    (hreal : ∀ g h : G, O.order.le g h ↔ ρ g x ≤ ρ h x)
    (hz : O.order.lt 1 z) (g : G) :
    ρ g '' connectedComponentIn {y : ℝ | ρ z y ≠ y} x =
        connectedComponentIn {y : ℝ | ρ z y ≠ y} x ↔
      g ∈ O.centralBoundedSubgroup z hcentral := by
  let := O.order
  have hx : x < ρ z x := by
    have hnot : ¬ O.order.le z 1 := not_le_of_gt hz
    rw [hreal] at hnot
    simpa using lt_of_not_ge hnot
  rw [← powerInterval_eq_fixedPoint_component ρ z x hx]
  exact image_powerInterval_eq_iff_mem_bounded ρ O z hcentral x hreal hz g

end NoncofinalDynamics
end FnZPositiveCones
