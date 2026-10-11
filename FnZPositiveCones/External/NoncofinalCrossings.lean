module

public import FnZPositiveCones.External.NoncofinalDynamics

@[expose] public section

/-!
# Crossings from overlapping cyclic-orbit intervals

This checks the interval argument in Deroin–Navas–Rivas, Proposition 3.2.26,
used by MMRT Lemma 4.11. The argument applies to arbitrary ordered spaces:
no completeness, real-line topology, or normality of a stabilizer is assumed.
-/

namespace FnZPositiveCones.NoncofinalCrossings

universe u v
variable {X : Type u} [LinearOrder X]

/-- The convex hull of an integer orbit, retaining the fixed-point singleton case. -/
def orbitInterval (f : X ≃o X) (x : X) : Set X :=
  {y | ∃ m n : ℤ, (f ^ m) x ≤ y ∧ y ≤ (f ^ n) x}

@[simp] theorem mem_orbitInterval_self (f : X ≃o X) (x : X) :
    x ∈ orbitInterval f x := ⟨0, 0, by simp, by simp⟩

theorem orbitInterval_ordConnected (f : X ≃o X) (x : X) :
    Set.OrdConnected (orbitInterval f x) := by
  constructor
  rintro y ⟨m, n, hm, hn⟩ z ⟨p, q, hp, hq⟩ t ⟨hyt, htz⟩
  exact ⟨m, q, hm.trans hyt, htz.trans hq⟩

theorem mem_orbitInterval_symm (f : X ≃o X) {x y : X}
    (h : y ∈ orbitInterval f x) : x ∈ orbitInterval f y := by
  obtain ⟨m, n, hm, hn⟩ := h
  refine ⟨-n, -m, ?_, ?_⟩
  · simpa only [zpow_neg, RelIso.inv_apply_self] using (f ^ (-n)).monotone hn
  · simpa only [zpow_neg, RelIso.inv_apply_self] using (f ^ (-m)).monotone hm

theorem mem_orbitInterval_trans (f : X ≃o X) {x y z : X}
    (hxy : y ∈ orbitInterval f x) (hyz : z ∈ orbitInterval f y) :
    z ∈ orbitInterval f x := by
  obtain ⟨m, n, hm, hn⟩ := hxy
  obtain ⟨p, q, hp, hq⟩ := hyz
  refine ⟨p + m, q + n, ?_, ?_⟩
  · simpa only [zpow_add, RelIso.mul_apply] using ((f ^ p).monotone hm).trans hp
  · simpa only [zpow_add, RelIso.mul_apply] using hq.trans ((f ^ q).monotone hn)

theorem orbitInterval_eq_of_mem (f : X ≃o X) {x y : X}
    (h : y ∈ orbitInterval f x) : orbitInterval f y = orbitInterval f x := by
  ext z
  exact ⟨mem_orbitInterval_trans f h,
    mem_orbitInterval_trans f (mem_orbitInterval_symm f h)⟩

theorem zpow_mem_orbitInterval (f : X ≃o X) (x : X) (n : ℤ) :
    (f ^ n) x ∈ orbitInterval f x := ⟨n, n, le_rfl, le_rfl⟩

theorem orbitInterval_zpow_mem (f : X ≃o X) {x y : X}
    (hy : y ∈ orbitInterval f x) (n : ℤ) : (f ^ n) y ∈ orbitInterval f x :=
  mem_orbitInterval_trans f hy (zpow_mem_orbitInterval f y n)

theorem fixed_zpow (f : X ≃o X) {x : X} (h : f x = x) (n : ℤ) : (f ^ n) x = x := by
  apply zpow_induction_left (g := f) (P := fun g => g x = x) (by simp)
  · intro g hg
    change f (g x) = x
    rw [hg, h]
  · intro g hg
    change f⁻¹ (g x) = x
    rw [hg]
    exact f.injective (by simpa using h.symm)

theorem orbitInterval_eq_singleton_of_fixed (f : X ≃o X) {x : X} (h : f x = x) :
    orbitInterval f x = {x} := by
  ext y
  constructor
  · rintro ⟨m, n, hm, hn⟩
    rw [fixed_zpow f h m] at hm
    rw [fixed_zpow f h n] at hn
    exact le_antisymm hn hm
  · rintro rfl
    exact mem_orbitInterval_self f _

/-- A nontrivial cyclic orbit has integer iterates strictly above every point in its hull. -/
theorem exists_zpow_gt_of_mem (f : X ≃o X) {x y : X} (hx : f x ≠ x)
    (hy : y ∈ orbitInterval f x) : ∃ n : ℤ, y < (f ^ n) x := by
  obtain ⟨_, n, _, hn⟩ := hy
  rcases lt_or_gt_of_ne hx with hf | hf
  · have hi : x < f⁻¹ x := f.strictMono.lt_iff_lt.mp (by simpa using hf)
    refine ⟨n - 1, hn.trans_lt ?_⟩
    simpa only [sub_eq_add_neg, zpow_add, zpow_neg_one, RelIso.mul_apply] using
      (f ^ n).strictMono hi
  · refine ⟨n + 1, hn.trans_lt ?_⟩
    simpa only [zpow_add, zpow_one, RelIso.mul_apply] using (f ^ n).strictMono hf

/-- The dual iterate statement, without any density assumption on the ordered space. -/
theorem exists_zpow_lt_of_mem (f : X ≃o X) {x y : X} (hx : f x ≠ x)
    (hy : y ∈ orbitInterval f x) : ∃ n : ℤ, (f ^ n) x < y := by
  obtain ⟨m, _, hm, _⟩ := hy
  rcases lt_or_gt_of_ne hx with hf | hf
  · refine ⟨m + 1, (show (f ^ (m + 1)) x < (f ^ m) x from ?_).trans_le hm⟩
    simpa only [zpow_add, zpow_one, RelIso.mul_apply] using (f ^ m).strictMono hf
  · have hi : f⁻¹ x < x := f.strictMono.lt_iff_lt.mp (by simpa using hf)
    refine ⟨m - 1, (show (f ^ (m - 1)) x < (f ^ m) x from ?_).trans_le hm⟩
    simpa only [sub_eq_add_neg, zpow_add, zpow_neg_one, RelIso.mul_apply] using
      (f ^ m).strictMono hi

/-- The source definition of a crossing for two order-preserving automorphisms. -/
structure Crossing (f g : X ≃o X) (u v w : X) : Prop where
  left_lt_middle : u < w
  middle_lt_right : w < v
  left_bounded : ∀ n : ℕ, (g ^ n) u < v
  right_bounded : ∀ n : ℕ, u < (f ^ n) v
  crosses : ∃ N M : ℕ, (f ^ N) v < w ∧ w < (g ^ M) u

/-- Partially overlapping cyclic orbit intervals yield an actual crossing of powers.
The crossing exponents are one after choosing the two suitable integer powers. -/
theorem crossing_of_partial_overlap (f g : X ≃o X) (x y u v w : X)
    (hu : u ∈ orbitInterval f x) (hu' : u ∉ orbitInterval g y)
    (hv : v ∈ orbitInterval g y) (hv' : v ∉ orbitInterval f x)
    (hwf : w ∈ orbitInterval f x) (hwg : w ∈ orbitInterval g y)
    (huw : u < w) (hwv : w < v) :
    ∃ m n : ℤ, Crossing (g ^ n) (f ^ m) u v w := by
  have hI := orbitInterval_eq_of_mem f hu
  have hJ := orbitInterval_eq_of_mem g hv
  have hwu : w ∈ orbitInterval f u := hI.symm ▸ hwf
  have hwv' : w ∈ orbitInterval g v := hJ.symm ▸ hwg
  have hfu : f u ≠ u := by
    intro h
    rw [orbitInterval_eq_singleton_of_fixed f h] at hwu
    exact huw.ne' hwu
  have hgv : g v ≠ v := by
    intro h
    rw [orbitInterval_eq_singleton_of_fixed g h] at hwv'
    exact hwv.ne hwv'
  obtain ⟨m, hm⟩ := exists_zpow_gt_of_mem f hfu hwu
  obtain ⟨n, hn⟩ := exists_zpow_lt_of_mem g hgv hwv'
  refine ⟨m, n, huw, hwv, ?_, ?_, ⟨1, 1, by simpa using hn, by simpa using hm⟩⟩
  · intro k
    have hk : ((f ^ m) ^ k) u ∈ orbitInterval f x := by
      rw [← zpow_natCast, ← zpow_mul]
      exact orbitInterval_zpow_mem f hu _
    by_contra h
    apply hv'
    exact (orbitInterval_ordConnected f x).out hu hk ⟨huw.le.trans hwv.le, le_of_not_gt h⟩
  · intro k
    have hk : ((g ^ n) ^ k) v ∈ orbitInterval g y := by
      rw [← zpow_natCast, ← zpow_mul]
      exact orbitInterval_zpow_mem g hv _
    by_contra h
    apply hu'
    exact (orbitInterval_ordConnected g y).out hk hv ⟨le_of_not_gt h, huw.le.trans hwv.le⟩

/-- Convexity orders the witnesses of partial overlap. -/
theorem between_of_partial_overlap {S T : Set X} (hS : Set.OrdConnected S)
    (hT : Set.OrdConnected T) {u v w : X}
    (hu : u ∈ S) (hu' : u ∉ T) (hv : v ∈ T) (hv' : v ∉ S)
    (hwS : w ∈ S) (hwT : w ∈ T) (huv : u < v) : u < w ∧ w < v := by
  constructor
  · by_contra h
    exact hu' (hT.out hwT hv ⟨le_of_not_gt h, huv.le⟩)
  · by_contra h
    exact hv' (hS.out hu hwS ⟨huv.le, le_of_not_gt h⟩)

section Action

variable {G : Type v} [Group G] (ρ : G →* (X ≃o X))

/-- Absence of crossings for the actual group action, without faithfulness assumptions. -/
def NoCrossings : Prop := ∀ f g : G, ∀ u v w : X, ¬ Crossing (ρ f) (ρ g) u v w

/-- DNR Proposition 3.2.26: cyclic-orbit intervals in a crossing-free action
are pairwise disjoint or nested. Partial overlap constructs a forbidden crossing,
rather than being excluded by an auxiliary interval hypothesis. -/
theorem orbitIntervals_laminar (hno : NoCrossings ρ) (f g : G) (x y : X) :
    Disjoint (orbitInterval (ρ f) x) (orbitInterval (ρ g) y) ∨
      orbitInterval (ρ f) x ⊆ orbitInterval (ρ g) y ∨
        orbitInterval (ρ g) y ⊆ orbitInterval (ρ f) x := by
  classical
  by_cases hd : Disjoint (orbitInterval (ρ f) x) (orbitInterval (ρ g) y)
  · exact Or.inl hd
  right
  by_cases hfg : orbitInterval (ρ f) x ⊆ orbitInterval (ρ g) y
  · exact Or.inl hfg
  right
  by_contra hgf
  obtain ⟨w, hwf, hwg⟩ := Set.not_disjoint_iff.mp hd
  obtain ⟨u, hu, hu'⟩ := Set.not_subset.mp hfg
  obtain ⟨v, hv, hv'⟩ := Set.not_subset.mp hgf
  have huv : u ≠ v := fun he => hu' (he ▸ hv)
  rcases lt_or_gt_of_ne huv with hlt | hgt
  · obtain ⟨huw, hwv⟩ := between_of_partial_overlap
      (orbitInterval_ordConnected (ρ f) x) (orbitInterval_ordConnected (ρ g) y)
      hu hu' hv hv' hwf hwg hlt
    obtain ⟨m, n, hc⟩ := crossing_of_partial_overlap (ρ f) (ρ g) x y u v w
      hu hu' hv hv' hwf hwg huw hwv
    exact hno (g ^ n) (f ^ m) u v w (by simpa only [map_zpow] using hc)
  · obtain ⟨hvw, hwu⟩ := between_of_partial_overlap
      (orbitInterval_ordConnected (ρ g) y) (orbitInterval_ordConnected (ρ f) x)
      hv hv' hu hu' hwg hwf hgt
    obtain ⟨m, n, hc⟩ := crossing_of_partial_overlap (ρ g) (ρ f) y x v u w
      hv hv' hu hu' hwg hwf hvw hwu
    exact hno (f ^ n) (g ^ m) v u w (by simpa only [map_zpow] using hc)

/-- A nested cyclic interval is preserved at every point of its containing interval.
The conclusion uses laminarity for all group elements and all basepoints. -/
theorem orbitInterval_mapsTo (hno : NoCrossings ρ) (f g : G) (x : X)
    (hsub : orbitInterval (ρ f) x ⊆ orbitInterval (ρ g) x) (n : ℤ) :
    Set.MapsTo ((ρ f) ^ n) (orbitInterval (ρ g) x) (orbitInterval (ρ g) x) := by
  intro z hz
  have hn := zpow_mem_orbitInterval (ρ f) z n
  rcases orbitIntervals_laminar ρ hno f g z x with hd | hfg | hgf
  · exact False.elim (Set.disjoint_left.mp hd (mem_orbitInterval_self (ρ f) z) hz)
  · exact hfg hn
  · have hx : x ∈ orbitInterval (ρ f) z := hgf (mem_orbitInterval_self (ρ g) x)
    have he := orbitInterval_eq_of_mem (ρ f) hx
    rw [← he] at hn
    exact hsub hn

/-- Automorphisms preserving a set in both directions form an actual subgroup. -/
def preservingSubgroup (S : Set X) : Subgroup G where
  carrier := {g | Set.MapsTo (ρ g) S S ∧ Set.MapsTo (ρ g⁻¹) S S}
  one_mem' := by
    constructor <;> intro x hx <;> simpa using hx
  mul_mem' := by
    intro g h hg hh
    constructor
    · intro x hx
      simpa only [map_mul, RelIso.mul_apply] using hg.1 (hh.1 hx)
    · intro x hx
      simpa only [mul_inv_rev, map_mul, RelIso.mul_apply] using hh.2 (hg.2 hx)
  inv_mem' := by
    intro g hg
    exact ⟨hg.2, by simpa only [inv_inv] using hg.1⟩

/-- A bounded integer orbit is the explicit negation-of-cofinality witness. -/
def Noncofinal (g : G) : Prop :=
  ∃ x y : X, x < y ∧ ∀ n : ℤ, ((ρ g) ^ n) x < y

theorem noncofinal_of_mem_preservingSubgroup {S : Set X} {x y : X} (hx : x ∈ S)
    (hbound : ∀ z ∈ S, z < y) {g : G} (hg : g ∈ preservingSubgroup ρ S) :
    Noncofinal ρ g := by
  refine ⟨x, y, hbound x hx, ?_⟩
  intro n
  have hn := (preservingSubgroup ρ S).zpow_mem hg n
  have hmem : ρ (g ^ n) x ∈ S := hn.1 hx
  exact hbound _ (by simpa only [map_zpow] using hmem)

/-- The elements with bounded cyclic orbits are closed under products when crossings are absent. -/
theorem noncofinal_mul (hno : NoCrossings ρ) {g h : G}
    (hg : Noncofinal ρ g) (hh : Noncofinal ρ h) : Noncofinal ρ (g * h) := by
  obtain ⟨xg, yg, hxg, hg⟩ := hg
  obtain ⟨xh, yh, hxh, hh⟩ := hh
  let x := min xg xh
  let y := max yg yh
  have hg' (n : ℤ) : ((ρ g) ^ n) x < y :=
    (((ρ g) ^ n).monotone (min_le_left xg xh)).trans_lt
      ((hg n).trans_le (le_max_left yg yh))
  have hh' (n : ℤ) : ((ρ h) ^ n) x < y :=
    (((ρ h) ^ n).monotone (min_le_right xg xh)).trans_lt
      ((hh n).trans_le (le_max_right yg yh))
  have hb_g : ∀ z ∈ orbitInterval (ρ g) x, z < y := by
    rintro z ⟨m, n, hm, hn⟩
    exact hn.trans_lt (hg' n)
  have hb_h : ∀ z ∈ orbitInterval (ρ h) x, z < y := by
    rintro z ⟨m, n, hm, hn⟩
    exact hn.trans_lt (hh' n)
  have hmem (a b : G) (hab : orbitInterval (ρ a) x ⊆ orbitInterval (ρ b) x) :
      a ∈ preservingSubgroup ρ (orbitInterval (ρ b) x) := by
    constructor
    · simpa only [zpow_one] using orbitInterval_mapsTo ρ hno a b x hab 1
    · simpa only [map_inv, zpow_neg_one] using orbitInterval_mapsTo ρ hno a b x hab (-1)
  rcases orbitIntervals_laminar ρ hno g h x x with hd | hgh | hhg
  · exact False.elim (Set.disjoint_left.mp hd (mem_orbitInterval_self _ _) (mem_orbitInterval_self _ _))
  · exact noncofinal_of_mem_preservingSubgroup ρ (mem_orbitInterval_self _ _) hb_h
      ((preservingSubgroup ρ _).mul_mem (hmem g h hgh) (hmem h h Set.Subset.rfl))
  · exact noncofinal_of_mem_preservingSubgroup ρ (mem_orbitInterval_self _ _) hb_g
      ((preservingSubgroup ρ _).mul_mem (hmem g g Set.Subset.rfl) (hmem h g hhg))

theorem noncofinal_inv {g : G} (hg : Noncofinal ρ g) : Noncofinal ρ g⁻¹ := by
  obtain ⟨x, y, hxy, hg⟩ := hg
  refine ⟨x, y, hxy, ?_⟩
  intro n
  simpa only [map_inv, inv_zpow, ← zpow_neg] using hg (-n)

/-- Noncofinality is invariant under conjugacy, independently of the crossing hypothesis. -/
theorem noncofinal_conj {g : G} (hg : Noncofinal ρ g) (h : G) :
    Noncofinal ρ (h * g * h⁻¹) := by
  obtain ⟨x, y, hxy, hg⟩ := hg
  refine ⟨ρ h x, ρ h y, (ρ h).strictMono hxy, ?_⟩
  intro n
  have hi := (ρ h).strictMono (hg n)
  simpa only [map_mul, map_inv, conj_zpow, RelIso.mul_apply, RelIso.inv_apply_self] using hi

/-- DNR Proposition 3.2.26, with an explicit carrier and checked subgroup laws. -/
def noncofinalSubgroup [Nontrivial X] (hno : NoCrossings ρ) : Subgroup G where
  carrier := {g | Noncofinal ρ g}
  one_mem' := by
    obtain ⟨x, y, hxy⟩ := exists_pair_lt X
    exact ⟨x, y, hxy, by intro n; simpa using hxy⟩
  mul_mem' := noncofinal_mul ρ hno
  inv_mem' := noncofinal_inv ρ

instance noncofinalSubgroup_normal [Nontrivial X] (hno : NoCrossings ρ) :
    (noncofinalSubgroup ρ hno).Normal where
  conj_mem _g hg h := noncofinal_conj ρ hg h

end Action

section Real

variable {G : Type v} [Group G] (ρ : G →* (ℝ ≃o ℝ))

/-- On the real line, an element is noncofinal precisely when it has a fixed point. -/
theorem noncofinal_iff_exists_fixed (g : G) :
    Noncofinal ρ g ↔ ∃ x : ℝ, ρ g x = x := by
  constructor
  · rintro ⟨x, y, _, hbound⟩
    have hb : BddAbove (Set.range (fun n : ℤ => ρ (g ^ n) x)) := by
      refine ⟨y, ?_⟩
      rintro _ ⟨n, rfl⟩
      simpa only [map_zpow] using (hbound n).le
    exact ⟨_, NoncofinalDynamics.orbit_sSup_fixed ρ g x hb⟩
  · rintro ⟨x, hx⟩
    refine ⟨x, x + 1, by linarith, ?_⟩
    intro n
    rw [fixed_zpow (ρ g) hx n]
    linarith

end Real

end FnZPositiveCones.NoncofinalCrossings
