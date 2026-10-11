module

public import FnZPositiveCones.External.CircularTopology
public import Mathlib.Order.Interval.Set.IsoIoo
public import Mathlib.Topology.Order.OrderClosed
public import Mathlib.Topology.Instances.Real.Lemmas

@[expose] public section

/-! Supported increasing perturbations, used in the local orbit argument. -/
namespace FnZPositiveCones
namespace CircularDynamics

/-- Affine normalization of a nonempty real open interval. -/
noncomputable def normalizeIoo (a d : ℝ) (had : a < d) :
    Set.Ioo a d ≃o Set.Ioo (-1 : ℝ) 1 where
  toFun x := ⟨(2 * x.1 - a - d) / (d - a), by
    have hd : 0 < d - a := sub_pos.mpr had
    constructor
    · apply (lt_div_iff₀ hd).mpr
      linarith [x.2.1]
    · apply (div_lt_iff₀ hd).mpr
      linarith [x.2.2]⟩
  invFun y := ⟨((d - a) * y.1 + a + d) / 2, by
    have hp := mul_lt_mul_of_pos_left y.2.1 (sub_pos.mpr had)
    have hq := mul_lt_mul_of_pos_left y.2.2 (sub_pos.mpr had)
    constructor <;> linarith⟩
  left_inv x := by
    apply Subtype.ext
    dsimp
    have hd : d - a ≠ 0 := sub_ne_zero.mpr (ne_of_gt had)
    field_simp [hd]
    ring
  right_inv y := by
    apply Subtype.ext
    dsimp
    have hd : d - a ≠ 0 := sub_ne_zero.mpr (ne_of_gt had)
    field_simp
    ring
  map_rel_iff' := by
    intro x y
    change (2 * x.1 - a - d) / (d - a) ≤ (2 * y.1 - a - d) / (d - a) ↔ x.1 ≤ y.1
    rw [div_le_div_iff_of_pos_right (sub_pos.mpr had)]
    constructor <;> intro h <;> linarith

/-- Every nonempty real open interval has an explicit order isomorphism with the line. -/
noncomputable def realIooOrderIso (a d : ℝ) (had : a < d) : Set.Ioo a d ≃o ℝ :=
  (normalizeIoo a d had).trans (orderIsoIooNegOneOne ℝ).symm

/-- Extend an increasing interval permutation by the identity outside the interval. -/
noncomputable def extendIooPerm (a d : ℝ) (e : Set.Ioo a d ≃o Set.Ioo a d) : Equiv.Perm ℝ := by
  classical
  exact Equiv.Perm.extendDomain e.toEquiv (Equiv.refl _)

theorem extendIooPerm_apply_mem (a d : ℝ) (e : Set.Ioo a d ≃o Set.Ioo a d)
    (x : ℝ) (hx : x ∈ Set.Ioo a d) :
    extendIooPerm a d e x = (e ⟨x, hx⟩).val := by
  classical
  exact Equiv.Perm.extendDomain_apply_subtype e.toEquiv (Equiv.refl _) hx

theorem extendIooPerm_apply_not_mem (a d : ℝ) (e : Set.Ioo a d ≃o Set.Ioo a d)
    (x : ℝ) (hx : x ∉ Set.Ioo a d) : extendIooPerm a d e x = x := by
  classical
  exact Equiv.Perm.extendDomain_apply_not_subtype e.toEquiv (Equiv.refl _) hx

/-- The extension remains strictly increasing across both endpoints. -/
theorem extendIooPerm_strictMono (a d : ℝ) (e : Set.Ioo a d ≃o Set.Ioo a d) :
    StrictMono (extendIooPerm a d e) := by
  intro x y hxy
  by_cases hx : x ∈ Set.Ioo a d
  · rw [extendIooPerm_apply_mem a d e x hx]
    by_cases hy : y ∈ Set.Ioo a d
    · rw [extendIooPerm_apply_mem a d e y hy]
      exact e.strictMono hxy
    · rw [extendIooPerm_apply_not_mem a d e y hy]
      have hd : d ≤ y := by
        by_contra h
        exact hy ⟨hx.1.trans hxy, lt_of_not_ge h⟩
      exact (e ⟨x, hx⟩).2.2.trans_le hd
  · rw [extendIooPerm_apply_not_mem a d e x hx]
    by_cases hy : y ∈ Set.Ioo a d
    · rw [extendIooPerm_apply_mem a d e y hy]
      have ha : x ≤ a := by
        by_contra h
        exact hx ⟨lt_of_not_ge h, hxy.trans hy.2⟩
      exact ha.trans_lt (e ⟨y, hy⟩).2.1
    · rw [extendIooPerm_apply_not_mem a d e y hy]
      exact hxy

/-- The supported interval perturbation as an actual order automorphism of the line. -/
noncomputable def extendIooOrderIso (a d : ℝ) (e : Set.Ioo a d ≃o Set.Ioo a d) : ℝ ≃o ℝ where
  toEquiv := extendIooPerm a d e
  map_rel_iff' := (extendIooPerm_strictMono a d e).le_iff_le

/-- Move any interior point to any other interior point while fixing the complement
of the chosen interval. All maps and their inverses are checked order isomorphisms. -/
theorem exists_supported_real_orderIso (a b c d : ℝ)
    (hab : a < b) (hbd : b < d) (hac : a < c) (hcd : c < d) :
    ∃ e : ℝ ≃o ℝ, e b = c ∧ ∀ x ∉ Set.Ioo a d, e x = x := by
  let q := realIooOrderIso a d (hab.trans hbd)
  let pb : Set.Ioo a d := ⟨b, hab, hbd⟩
  let pc : Set.Ioo a d := ⟨c, hac, hcd⟩
  let e : Set.Ioo a d ≃o Set.Ioo a d :=
    (q.trans (OrderIso.addRight (q pc - q pb))).trans q.symm
  refine ⟨extendIooOrderIso a d e, ?_, ?_⟩
  · change extendIooPerm a d e b = c
    rw [extendIooPerm_apply_mem a d e b ⟨hab, hbd⟩]
    have he : e pb = pc := by
      change q.symm (q pb + (q pc - q pb)) = pc
      rw [show q pb + (q pc - q pb) = q pc by ring, q.symm_apply_apply]
    exact congrArg Subtype.val he
  · intro x hx
    exact extendIooPerm_apply_not_mem a d e x hx

/-- Support in an interval bounds the displacement everywhere by its length. -/
theorem supported_real_orderIso_displacement (a d : ℝ) (had : a < d)
    (e : ℝ ≃o ℝ) (hfix : ∀ x ∉ Set.Ioo a d, e x = x) (x : ℝ) :
    |e x - x| < d - a := by
  have hea : e a = a := hfix a (by simp)
  have hed : e d = d := hfix d (by simp)
  by_cases hx : x ∈ Set.Ioo a d
  · have hel : a < e x := by simpa only [hea] using e.strictMono hx.1
    have her : e x < d := by simpa only [hed] using e.strictMono hx.2
    rw [abs_lt]
    constructor <;> linarith [hx.1, hx.2]
  · rw [hfix x hx, sub_self, abs_zero]
    exact sub_pos.mpr had

/-- The local move can be uniformly smaller than any interval-length bound. -/
theorem exists_supported_real_orderIso_small (a b c d ε : ℝ)
    (hab : a < b) (hbd : b < d) (hac : a < c) (hcd : c < d) (hε : d - a < ε) :
    ∃ e : ℝ ≃o ℝ, e b = c ∧ (∀ x ∉ Set.Ioo a d, e x = x) ∧
      ∀ x, dist (e x) x < ε := by
  obtain ⟨e, he, hfix⟩ := exists_supported_real_orderIso a b c d hab hbd hac hcd
  refine ⟨e, he, hfix, fun x => ?_⟩
  rw [Real.dist_eq]
  exact (supported_real_orderIso_displacement a d (hab.trans hbd) e hfix x).trans hε

end CircularDynamics
end FnZPositiveCones
