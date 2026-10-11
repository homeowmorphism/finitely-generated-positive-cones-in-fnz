module

public import FnZPositiveCones.Cone.Topology

@[expose] public section

/-! Ordered actions: extending rational order automorphisms to the real line. -/
namespace FnZPositiveCones.OrderedActions

noncomputable def ratCutImage (f : ℚ ≃o ℚ) (x : ℝ) : Set ℝ :=
  {y | ∃ q : ℚ, (q : ℝ) ≤ x ∧ y = (f q : ℝ)}

theorem ratCutImage_nonempty (f : ℚ ≃o ℚ) (x : ℝ) : (ratCutImage f x).Nonempty := by
  obtain ⟨q, hq⟩ := exists_rat_lt x
  exact ⟨f q, q, hq.le, rfl⟩

theorem ratCutImage_bddAbove (f : ℚ ≃o ℚ) (x : ℝ) : BddAbove (ratCutImage f x) := by
  obtain ⟨r, hr⟩ := exists_rat_gt x
  refine ⟨f r, ?_⟩
  rintro _ ⟨q, hq, rfl⟩
  exact_mod_cast f.monotone (show q ≤ r by exact_mod_cast hq.trans hr.le)

noncomputable def ratExtendFun (f : ℚ ≃o ℚ) (x : ℝ) : ℝ := sSup (ratCutImage f x)

theorem ratExtendFun_monotone (f : ℚ ≃o ℚ) : Monotone (ratExtendFun f) := by
  intro x y hxy
  exact csSup_le_csSup (ratCutImage_bddAbove f y) (ratCutImage_nonempty f x)
    (by rintro _ ⟨q, hq, rfl⟩; exact ⟨q, hq.trans hxy, rfl⟩)

@[simp] theorem ratExtendFun_ratCast (f : ℚ ≃o ℚ) (q : ℚ) : ratExtendFun f q = (f q : ℝ) := by
  apply le_antisymm
  · apply csSup_le (ratCutImage_nonempty f q)
    rintro _ ⟨r, hr, rfl⟩
    exact_mod_cast f.monotone (show r ≤ q by exact_mod_cast hr)
  · exact le_csSup (ratCutImage_bddAbove f q) ⟨q, le_rfl, rfl⟩

theorem ratExtendFun_strictMono (f : ℚ ≃o ℚ) : StrictMono (ratExtendFun f) := by
  intro x y hxy
  obtain ⟨q, hxq, hqy⟩ := exists_rat_btwn hxy
  obtain ⟨r, hqr, hry⟩ := exists_rat_btwn hqy
  have hqr' : q < r := by exact_mod_cast hqr
  have hf : (f q : ℝ) < (f r : ℝ) := by exact_mod_cast f.strictMono hqr'
  calc
    ratExtendFun f x ≤ ratExtendFun f q := ratExtendFun_monotone f hxq.le
    _ = (f q : ℝ) := ratExtendFun_ratCast f q
    _ < (f r : ℝ) := hf
    _ = ratExtendFun f r := (ratExtendFun_ratCast f r).symm
    _ ≤ ratExtendFun f y := ratExtendFun_monotone f hry.le

theorem ratExtendFun_inverse (f : ℚ ≃o ℚ) (x : ℝ) :
    ratExtendFun f.symm (ratExtendFun f x) = x := by
  apply le_antisymm
  · by_contra hn
    obtain ⟨q, hxq, hqz⟩ := exists_rat_btwn (lt_of_not_ge hn)
    have h := ratExtendFun_strictMono f.symm (ratExtendFun_strictMono f hxq)
    simp only [ratExtendFun_ratCast, OrderIso.symm_apply_apply] at h
    exact h.not_ge hqz.le
  · by_contra hn
    obtain ⟨q, hzq, hqx⟩ := exists_rat_btwn (lt_of_not_ge hn)
    have h := ratExtendFun_strictMono f.symm (ratExtendFun_strictMono f hqx)
    simp only [ratExtendFun_ratCast, OrderIso.symm_apply_apply] at h
    exact h.not_ge hzq.le

/-- Every rational order automorphism extends to an actual real order automorphism. -/
noncomputable def ratExtension (f : ℚ ≃o ℚ) : ℝ ≃o ℝ where
  toFun := ratExtendFun f
  invFun := ratExtendFun f.symm
  left_inv := ratExtendFun_inverse f
  right_inv := ratExtendFun_inverse f.symm
  map_rel_iff' := (ratExtendFun_strictMono f).le_iff_le

@[simp] theorem ratExtension_ratCast (f : ℚ ≃o ℚ) (q : ℚ) :
    ratExtension f q = (f q : ℝ) := ratExtendFun_ratCast f q

theorem realOrderIso_ext_rat {f g : ℝ ≃o ℝ} (h : ∀ q : ℚ, f q = g q) : f = g := by
  apply DFunLike.ext'
  exact Rat.denseRange_cast.equalizer f.continuous g.continuous (funext h)

/-- Rational extension respects composition, so it extends group representations. -/
noncomputable def ratExtensionHom : (ℚ ≃o ℚ) →* (ℝ ≃o ℝ) where
  toFun := ratExtension
  map_one' := by apply realOrderIso_ext_rat; intro q; simp
  map_mul' f g := by apply realOrderIso_ext_rat; intro q; simp

end FnZPositiveCones.OrderedActions
