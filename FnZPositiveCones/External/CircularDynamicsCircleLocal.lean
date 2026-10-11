module

public import FnZPositiveCones.External.CircularDynamicsSeparation
public import Mathlib.Algebra.Order.Floor.Ring
public import FnZPositiveCones.External.OrderedActionsCircle
public import Mathlib.Analysis.Normed.Group.AddCircle

@[expose] public section

/-! Periodizing a supported local increasing map to a translation-equivariant map. -/
namespace FnZPositiveCones
namespace CircularDynamics

/-- Repeat the same map on each integer band. -/
noncomputable def periodicMap (e : ℝ ≃o ℝ) (x : ℝ) : ℝ :=
  (⌊x⌋ : ℝ) + e (Int.fract x)

theorem orderIso_maps_unitIco (e : ℝ ≃o ℝ) (h0 : e 0 = 0) (h1 : e 1 = 1)
    {x : ℝ} (hx : x ∈ Set.Ico 0 1) : e x ∈ Set.Ico 0 1 := by
  constructor
  · simpa only [h0] using e.monotone hx.1
  · simpa only [h1] using e.strictMono hx.2

theorem periodicMap_floor (e : ℝ ≃o ℝ) (h0 : e 0 = 0) (h1 : e 1 = 1) (x : ℝ) :
    ⌊periodicMap e x⌋ = ⌊x⌋ := by
  have he := orderIso_maps_unitIco e h0 h1 ⟨Int.fract_nonneg x, Int.fract_lt_one x⟩
  simp only [periodicMap, Int.floor_intCast_add, Int.floor_eq_zero_iff.mpr he, add_zero]

theorem periodicMap_fract (e : ℝ ≃o ℝ) (h0 : e 0 = 0) (h1 : e 1 = 1) (x : ℝ) :
    Int.fract (periodicMap e x) = e (Int.fract x) := by
  have he := orderIso_maps_unitIco e h0 h1 ⟨Int.fract_nonneg x, Int.fract_lt_one x⟩
  simp only [periodicMap, Int.fract_intCast_add, Int.fract_eq_self.mpr he]

theorem periodicMap_apply_mem (e : ℝ ≃o ℝ) {x : ℝ} (hx : x ∈ Set.Ico 0 1) :
    periodicMap e x = e x := by
  simp only [periodicMap, Int.floor_eq_zero_iff.mpr hx, Int.cast_zero, zero_add,
    Int.fract_eq_self.mpr hx]

theorem periodicMap_strictMono (e : ℝ ≃o ℝ) (h0 : e 0 = 0) (h1 : e 1 = 1) :
    StrictMono (periodicMap e) := by
  intro x y hxy
  have hx := orderIso_maps_unitIco e h0 h1 ⟨Int.fract_nonneg x, Int.fract_lt_one x⟩
  have hy := orderIso_maps_unitIco e h0 h1 ⟨Int.fract_nonneg y, Int.fract_lt_one y⟩
  have hfl := Int.floor_mono hxy.le
  by_cases he : ⌊x⌋ = ⌊y⌋
  · have hf : Int.fract x < Int.fract y := by
      have hx' := Int.floor_add_fract x
      have hy' := Int.floor_add_fract y
      rw [he] at hx'
      linarith
    change (⌊x⌋ : ℝ) + e (Int.fract x) < (⌊y⌋ : ℝ) + e (Int.fract y)
    rw [he]
    linarith [e.strictMono hf]
  · have hlt : ⌊x⌋ + 1 ≤ ⌊y⌋ := by omega
    have hcast : (⌊x⌋ : ℝ) + 1 ≤ (⌊y⌋ : ℝ) := by exact_mod_cast hlt
    change (⌊x⌋ : ℝ) + e (Int.fract x) < (⌊y⌋ : ℝ) + e (Int.fract y)
    linarith [hx.2, hy.1]

/-- The inverse of periodization is the periodization of the inverse. -/
theorem periodicMap_symm_apply_apply (e : ℝ ≃o ℝ) (h0 : e 0 = 0) (h1 : e 1 = 1) (x : ℝ) :
    periodicMap e.symm (periodicMap e x) = x := by
  change (⌊periodicMap e x⌋ : ℝ) + e.symm (Int.fract (periodicMap e x)) = x
  rw [periodicMap_floor e h0 h1, periodicMap_fract e h0 h1, e.symm_apply_apply, Int.floor_add_fract]

/-- The periodically repeated local map is an actual order automorphism of the line. -/
noncomputable def periodicOrderIso (e : ℝ ≃o ℝ) (h0 : e 0 = 0) (h1 : e 1 = 1) : ℝ ≃o ℝ where
  toFun := periodicMap e
  invFun := periodicMap e.symm
  left_inv := periodicMap_symm_apply_apply e h0 h1
  right_inv := periodicMap_symm_apply_apply e.symm
    (e.symm_apply_eq.mpr h0.symm) (e.symm_apply_eq.mpr h1.symm)
  map_rel_iff' := (periodicMap_strictMono e h0 h1).le_iff_le

/-- Translation by one commutes with the periodic local motion. -/
theorem periodicOrderIso_add_one (e : ℝ ≃o ℝ) (h0 : e 0 = 0) (h1 : e 1 = 1) (x : ℝ) :
    periodicOrderIso e h0 h1 (x + 1) = periodicOrderIso e h0 h1 x + 1 := by
  change periodicMap e (x + 1) = periodicMap e x + 1
  simp only [periodicMap, Int.floor_add_one, Int.cast_add, Int.cast_one, Int.fract_add_one]
  ring

/-- Periodization preserves the same uniform displacement bound. -/
theorem periodicOrderIso_dist (e : ℝ ≃o ℝ) (h0 : e 0 = 0) (h1 : e 1 = 1) (x : ℝ) :
    dist (periodicOrderIso e h0 h1 x) x = dist (e (Int.fract x)) (Int.fract x) := by
  change dist (periodicMap e x) x = _
  rw [Real.dist_eq, Real.dist_eq]
  unfold periodicMap
  have hx := Int.floor_add_fract x
  congr 1
  linarith

/-- A supported interval move inside the fundamental interval yields a periodic
motion, hence a genuine local circle motion after quotient descent. -/
theorem exists_periodic_supported_move (a b c d ε : ℝ)
    (ha : 0 ≤ a) (hd : d ≤ 1) (hab : a < b) (hbd : b < d)
    (hac : a < c) (hcd : c < d) (hε : d - a < ε) :
    ∃ H : ℝ ≃o ℝ, H b = c ∧ (∀ x, H (x + 1) = H x + 1) ∧
      (∀ x ∈ Set.Ico (0 : ℝ) 1, x ∉ Set.Ioo a d → H x = x) ∧
      ∀ x, dist (H x) x < ε := by
  obtain ⟨e, heb, hfix, hsmall⟩ := exists_supported_real_orderIso_small a b c d ε hab hbd hac hcd hε
  have h0 : e 0 = 0 := hfix 0 (by intro h; linarith [h.1])
  have h1 : e 1 = 1 := hfix 1 (by intro h; linarith [h.2])
  refine ⟨periodicOrderIso e h0 h1, ?_, periodicOrderIso_add_one e h0 h1, ?_, ?_⟩
  · change periodicMap e b = c
    rw [periodicMap_apply_mem e ⟨by linarith, by linarith⟩, heb]
  · intro x hx hxa
    change periodicMap e x = x
    rw [periodicMap_apply_mem e hx, hfix x hxa]
  · intro x
    rw [periodicOrderIso_dist]
    exact hsmall _

/-- A small periodic perturbation crosses the chosen pair while preserving a
finite collection of fundamental-interval trace points. -/
theorem exists_periodic_crossing_fixing_finset (F : Finset ℝ) (a b ε : ℝ)
    (ha : 0 < a) (hab : a < b) (hb : b < 1) (hε : b - a < ε)
    (hF : ∀ y ∈ F, y ∈ Set.Ico (0 : ℝ) 1)
    (havoid : ∀ y ∈ F, y ∉ Set.Icc a b) :
    ∃ H : ℝ ≃o ℝ, b < H a ∧ H a < 1 ∧ (∀ y ∈ F, H y = y) ∧
      (∀ y, H (y + 1) = H y + 1) ∧ ∀ y, dist (H y) y < ε := by
  classical
  let F' := F ∪ {0, 1}
  have havoid' : ∀ y ∈ F', y ∉ Set.Icc a b := by
    intro y hy
    rcases Finset.mem_union.mp hy with hy | hy
    · exact havoid y hy
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl
      · intro hi; linarith [hi.1]
      · intro hi; linarith [hi.2]
  obtain ⟨e, hcross, hfix, hsmall⟩ := exists_small_crossing_fixing_finset F' a b ε hab hε havoid'
  have h0 : e 0 = 0 := hfix 0 (by simp [F'])
  have h1 : e 1 = 1 := hfix 1 (by simp [F'])
  have hpa : periodicOrderIso e h0 h1 a = e a := periodicMap_apply_mem e ⟨ha.le, hab.trans hb⟩
  refine ⟨periodicOrderIso e h0 h1, hpa ▸ hcross, ?_, ?_, periodicOrderIso_add_one e h0 h1, ?_⟩
  · rw [hpa]
    simpa only [h1] using e.strictMono (hab.trans hb)
  · intro y hy
    change periodicMap e y = y
    rw [periodicMap_apply_mem e (hF y hy), hfix y (Finset.mem_union_left _ hy)]
  · intro y
    rw [periodicOrderIso_dist]
    exact hsmall _

/-- The integer quotient cannot increase distance. -/
theorem circle_dist_coe_le (x y : ℝ) :
    dist (x : AddCircle (1 : ℝ)) (y : AddCircle (1 : ℝ)) ≤ dist x y := by
  rw [dist_eq_norm, ← QuotientAddGroup.mk_sub, dist_eq_norm]
  exact QuotientAddGroup.norm_mk_le_norm

/-- A uniformly small periodic real motion descends to a uniformly small circle motion. -/
theorem circlePerm_dist_lt (H : ℝ ≃o ℝ) (hH : ∀ y, H (y + 1) = H y + 1)
    {ε : ℝ} (hsmall : ∀ y, dist (H y) y < ε) (x : AddCircle (1 : ℝ)) :
    dist (OrderedActions.circlePerm H hH x) x < ε := by
  induction x using QuotientAddGroup.induction_on with
  | H x =>
      rw [OrderedActions.circlePerm_coe]
      exact (circle_dist_coe_le (H x) x).trans_lt (hsmall x)

/-- The local interval motion descends to an actual circular-order-preserving
continuous permutation of the standard circle, with explicit support and metric bound. -/
theorem exists_supported_circle_move (a b c d ε : ℝ)
    (ha : 0 ≤ a) (hd : d ≤ 1) (hab : a < b) (hbd : b < d)
    (hac : a < c) (hcd : c < d) (hε : d - a < ε) :
    ∃ h : Equiv.Perm (AddCircle (1 : ℝ)), PreservesCircular h ∧ Continuous h ∧
      h (b : AddCircle (1 : ℝ)) = (c : AddCircle (1 : ℝ)) ∧
      (∀ y ∈ Set.Ico (0 : ℝ) 1, y ∉ Set.Ioo a d → h (y : AddCircle (1 : ℝ)) = y) ∧
      ∀ y, dist (h y) y < ε := by
  obtain ⟨H, hbc, hH, hfix, hsmall⟩ := exists_periodic_supported_move a b c d ε ha hd hab hbd hac hcd hε
  refine ⟨OrderedActions.circlePerm H hH, OrderedActions.circlePerm_btw_iff H hH,
    OrderedActions.circlePerm_continuous H hH, ?_, ?_, circlePerm_dist_lt H hH hsmall⟩
  · rw [OrderedActions.circlePerm_coe, hbc]
  · intro y hy hya
    rw [OrderedActions.circlePerm_coe, hfix y hy hya]

/-- The finite-trace crossing move is also available on the actual circle, with
no abstract local-mobility hypothesis. Its images stay in the stated real chart. -/
theorem exists_circle_crossing_fixing_finset (F : Finset ℝ) (a b ε : ℝ)
    (ha : 0 < a) (hab : a < b) (hb : b < 1) (hε : b - a < ε)
    (hF : ∀ y ∈ F, y ∈ Set.Ico (0 : ℝ) 1)
    (havoid : ∀ y ∈ F, y ∉ Set.Icc a b) :
    ∃ (h : Equiv.Perm (AddCircle (1 : ℝ))) (c : ℝ),
      PreservesCircular h ∧ Continuous h ∧ b < c ∧ c < 1 ∧
      h (a : AddCircle (1 : ℝ)) = (c : AddCircle (1 : ℝ)) ∧
      (∀ y ∈ F, h (y : AddCircle (1 : ℝ)) = y) ∧ ∀ y, dist (h y) y < ε := by
  obtain ⟨H, hcross, htop, hfix, hH, hsmall⟩ :=
    exists_periodic_crossing_fixing_finset F a b ε ha hab hb hε hF havoid
  refine ⟨OrderedActions.circlePerm H hH, H a, OrderedActions.circlePerm_btw_iff H hH,
    OrderedActions.circlePerm_continuous H hH, hcross, htop, rfl, ?_, circlePerm_dist_lt H hH hsmall⟩
  intro y hy
  rw [OrderedActions.circlePerm_coe, hfix y hy]

/-- In the fundamental chart, orientation relative to zero is the real order. -/
theorem circle_sbtw_coe_zero_iff (a b : ℝ) (ha : 0 < a) (ha1 : a < 1)
    (hb : 0 < b) (hb1 : b < 1) :
    sbtw (a : AddCircle (1 : ℝ)) (b : AddCircle (1 : ℝ)) 0 ↔ a < b := by
  have hbtw (u v : ℝ) (hu : 0 < u) (hu1 : u < 1) (hv : 0 < v) (hv1 : v < 1) :
      btw (0 : AddCircle (1 : ℝ)) (u : AddCircle (1 : ℝ)) (v : AddCircle (1 : ℝ)) ↔ u ≤ v := by
    change btw ((0 : ℝ) : AddCircle (1 : ℝ)) (u : AddCircle (1 : ℝ)) (v : AddCircle (1 : ℝ)) ↔ _
    rw [QuotientAddGroup.btw_coe_iff,
      (toIcoMod_eq_self (show (0 : ℝ) < 1 by norm_num)).mpr (by simpa using And.intro hu.le hu1),
      (toIocMod_eq_self (show (0 : ℝ) < 1 by norm_num)).mpr (by simpa using And.intro hv hv1.le)]
  have hrev : btw (b : AddCircle (1 : ℝ)) (a : AddCircle (1 : ℝ)) 0 ↔ b ≤ a :=
    btw_cyclic.trans (hbtw b a hb hb1 ha ha1)
  rw [sbtw_cyclic, sbtw_iff_btw_not_btw, hbtw a b ha ha1 hb hb1, hrev]
  exact ⟨fun h => lt_of_not_ge h.2, fun h => ⟨h.le, not_le_of_gt h⟩⟩

end CircularDynamics
end FnZPositiveCones
