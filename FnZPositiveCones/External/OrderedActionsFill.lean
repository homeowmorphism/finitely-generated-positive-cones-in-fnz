module

public import FnZPositiveCones.External.OrderedActions

@[expose] public section

namespace FnZPositiveCones.OrderedActions
open Order
universe u v
variable {A : Type u} {B : Type v} [LinearOrder A] [LinearOrder B]

theorem isSuccPrelimit_map_iff (e : A ≃o B) (a : A) :
    IsSuccPrelimit (e a) ↔ IsSuccPrelimit a := by
  constructor
  · intro h b hb
    exact h (e b) ((apply_covBy_apply_iff e).mpr hb)
  · intro h b hb
    have : e.symm b ⋖ a := by
      simpa only [OrderIso.symm_apply_apply] using (apply_covBy_apply_iff e.symm).mpr hb
    exact h (e.symm b) this

theorem isPredPrelimit_map_iff (e : A ≃o B) (a : A) :
    IsPredPrelimit (e a) ↔ IsPredPrelimit a := by
  constructor
  · intro h b hb
    exact h (e b) ((apply_covBy_apply_iff e).mpr hb)
  · intro h b hb
    have : a ⋖ e.symm b := by
      simpa only [OrderIso.symm_apply_apply] using (apply_covBy_apply_iff e.symm).mpr hb
    exact h (e.symm b) this

/-- Order automorphisms extend functorially across exactly the jumps filled by mathlib. -/
def fillOrderIso (e : A ≃o B) : Order.Fill A ≃o Order.Fill B where
  toFun x := ⟨toLex (e (ofLex x.val).1, (ofLex x.val).2), by
    simpa only [ofLex_toLex, isSuccPrelimit_map_iff, isPredPrelimit_map_iff] using x.property⟩
  invFun y := ⟨toLex (e.symm (ofLex y.val).1, (ofLex y.val).2), by
    simpa only [ofLex_toLex, isSuccPrelimit_map_iff, isPredPrelimit_map_iff] using y.property⟩
  left_inv x := by apply Subtype.ext; simp
  right_inv x := by apply Subtype.ext; simp
  map_rel_iff' := by
    intro x y
    change (Prod.Lex.prodLexCongr e (OrderIso.refl ℚ)) x.val ≤
      (Prod.Lex.prodLexCongr e (OrderIso.refl ℚ)) y.val ↔ x.val ≤ y.val
    exact (Prod.Lex.prodLexCongr e (OrderIso.refl ℚ)).le_iff_le

@[simp] theorem fillOrderIso_some (e : A ≃o B) (a : A) :
    fillOrderIso e (Order.Fill.some a) = Order.Fill.some (e a) := rfl

instance fill_noMin [NoMinOrder A] : NoMinOrder (Order.Fill A) where
  exists_lt x := by
    obtain ⟨a, ha⟩ := exists_lt (ofLex x.val).1
    refine ⟨Order.Fill.some a, ?_⟩
    change toLex (a, (0 : ℚ)) < x.val
    exact Prod.Lex.left _ _ ha

instance fill_noMax [NoMaxOrder A] : NoMaxOrder (Order.Fill A) where
  exists_gt x := by
    obtain ⟨a, ha⟩ := exists_gt (ofLex x.val).1
    refine ⟨Order.Fill.some a, ?_⟩
    change x.val < toLex (a, (0 : ℚ))
    exact Prod.Lex.left _ _ ha

instance fill_nonempty [Nonempty A] : Nonempty (Order.Fill A) :=
  Nonempty.map Order.Fill.some inferInstance

instance fill_countable [Countable A] : Countable (Order.Fill A) :=
  Function.Injective.countable (f := fun x : Order.Fill A => ofLex x.val) (by
    intro x y h
    apply Subtype.ext
    exact ofLex.injective h)

/-- Filled countable orders with no endpoints have the rational order type. -/
noncomputable def fillRatIso [Countable A] [NoMinOrder A] [NoMaxOrder A] [Nonempty A] :
    Order.Fill A ≃o ℚ := Classical.choice (Order.iso_of_countable_dense _ _)

/-- The induced group homomorphism on automorphism groups. -/
def fillOrderIsoHom : (A ≃o A) →* (Order.Fill A ≃o Order.Fill A) where
  toFun := fillOrderIso
  map_one' := by ext x; rfl
  map_mul' f g := by ext x; rfl

/-- Conjugating an action across a specified order isomorphism. -/
def conjugateOrderIso (e : A ≃o B) : (A ≃o A) →* (B ≃o B) where
  toFun f := e.symm.trans (f.trans e)
  map_one' := by ext b; simp
  map_mul' f g := by ext b; simp

theorem fill_gap (y : Order.Fill A) (hy : ∀ a, y ≠ Order.Fill.some a) :
    ∃ a b : A, a ⋖ b ∧ Order.Fill.some a < y ∧ y < Order.Fill.some b := by
  have hq : (ofLex y.val).2 ≠ 0 := by
    intro h
    apply hy (ofLex y.val).1
    apply Subtype.ext
    apply ofLex.injective
    exact Prod.ext rfl h
  rcases lt_or_gt_of_ne hq with hneg | hpos
  · obtain ⟨a, ha⟩ := Order.not_isSuccPrelimit_iff.mp
      (fun h => not_le_of_gt hneg (y.property.1 h))
    refine ⟨a, (ofLex y.val).1, ha, ?_, ?_⟩
    · exact Prod.Lex.left _ _ ha.lt
    · change y.val < toLex ((ofLex y.val).1, (0 : ℚ))
      simpa only [Prod.Lex.lt_iff, ofLex_toLex, lt_self_iff_false, false_or,
        true_and] using hneg
  · obtain ⟨b, hb⟩ := Order.not_isPredPrelimit_iff.mp
      (fun h => not_le_of_gt hpos (y.property.2 h))
    refine ⟨(ofLex y.val).1, b, hb, ?_, ?_⟩
    · change toLex ((ofLex y.val).1, (0 : ℚ)) < y.val
      simpa only [Prod.Lex.lt_iff, ofLex_toLex, lt_self_iff_false, false_or,
        true_and] using hpos
    · exact Prod.Lex.left _ _ hb.lt

section RealModel
variable [Countable A] [NoMinOrder A] [NoMaxOrder A] [Nonempty A]

/-- Embedding into the real line, with only the original order gaps filled. -/
noncomputable def realModel : A ↪o ℝ :=
  Order.Fill.some.trans ((fillRatIso (A := A)).toOrderEmbedding.trans Rat.castOrderEmbedding)

@[simp] theorem realModel_apply (a : A) :
    realModel a = ((fillRatIso (A := A) (Order.Fill.some a) : ℚ) : ℝ) := rfl

/-- Transport of an ordered action to the real line. -/
noncomputable def realModelHom : (A ≃o A) →* (ℝ ≃o ℝ) :=
  ratExtensionHom.comp ((conjugateOrderIso (fillRatIso (A := A))).comp fillOrderIsoHom)

@[simp] theorem realModelHom_apply (f : A ≃o A) (a : A) :
    realModelHom f (realModel a) = realModel (f a) := by
  change ratExtension ((fillRatIso (A := A)).symm.trans
    ((fillOrderIso f).trans (fillRatIso (A := A))))
    ((fillRatIso (A := A) (Order.Fill.some a) : ℚ) : ℝ) = _
  rw [ratExtension_ratCast]
  simp [realModel_apply]

theorem continuous_realModel [TopologicalSpace A] [OrderTopology A] :
    Continuous (realModel (A := A)) :=
  Rat.continuous_coe_real.comp ((fillRatIso (A := A)).continuous.comp Order.Fill.continuous_some)

theorem realModel_unbounded_above (x : ℝ) : ∃ a : A, x < realModel a := by
  obtain ⟨q, hq⟩ := exists_rat_gt x
  let y := (fillRatIso (A := A)).symm q
  obtain ⟨a, ha⟩ := exists_gt (ofLex y.val).1
  have hy : y < Order.Fill.some a := Prod.Lex.left _ _ ha
  have hqa : q < fillRatIso (Order.Fill.some a) := by
    simpa only [y, OrderIso.apply_symm_apply] using (fillRatIso (A := A)).strictMono hy
  exact ⟨a, hq.trans (by change (q : ℝ) < ((fillRatIso (Order.Fill.some a) : ℚ) : ℝ); exact_mod_cast hqa)⟩

theorem realModel_unbounded_below (x : ℝ) : ∃ a : A, realModel a < x := by
  obtain ⟨q, hq⟩ := exists_rat_lt x
  let y := (fillRatIso (A := A)).symm q
  obtain ⟨a, ha⟩ := exists_lt (ofLex y.val).1
  have hy : Order.Fill.some a < y := Prod.Lex.left _ _ ha
  have haq : fillRatIso (Order.Fill.some a) < q := by
    simpa only [y, OrderIso.apply_symm_apply] using (fillRatIso (A := A)).strictMono hy
  exact ⟨a, (show realModel a < (q : ℝ) by change ((fillRatIso (Order.Fill.some a) : ℚ) : ℝ) < (q : ℝ); exact_mod_cast haq).trans hq⟩

/-- Every gap of the orbit closure is bounded by adjacent original elements. -/
theorem realModel_gap {x : ℝ} (hx : x ∉ closure (Set.range (realModel (A := A)))) :
    ∃ a b : A, a ⋖ b ∧ realModel a < x ∧ x < realModel b := by
  obtain ⟨l, u, hxl, hlu⟩ := mem_nhds_iff_exists_Ioo_subset.mp
    (isClosed_closure.isOpen_compl.mem_nhds hx)
  obtain ⟨r, hlr, hru⟩ := exists_rat_btwn (hxl.1.trans hxl.2)
  let y := (fillRatIso (A := A)).symm r
  have hyr : ∀ a, y ≠ Order.Fill.some a := by
    intro a ha
    have hr : (r : ℝ) = realModel a := by
      have h := congrArg (fillRatIso (A := A)) ha
      simp only [y, OrderIso.apply_symm_apply] at h
      change (r : ℝ) = ((fillRatIso (Order.Fill.some a) : ℚ) : ℝ)
      exact_mod_cast h
    have := hlu ⟨hlr, hru⟩
    rw [hr] at this
    exact this (subset_closure ⟨a, rfl⟩)
  obtain ⟨a, b, hab, hay, hyb⟩ := fill_gap y hyr
  have har : realModel a < (r : ℝ) := by
    have := (fillRatIso (A := A)).strictMono hay
    simp only [y, OrderIso.apply_symm_apply] at this
    change ((fillRatIso (Order.Fill.some a) : ℚ) : ℝ) < (r : ℝ)
    exact_mod_cast this
  have hrb : (r : ℝ) < realModel b := by
    have := (fillRatIso (A := A)).strictMono hyb
    simp only [y, OrderIso.apply_symm_apply] at this
    change (r : ℝ) < ((fillRatIso (Order.Fill.some b) : ℚ) : ℝ)
    exact_mod_cast this
  refine ⟨a, b, hab, ?_, ?_⟩
  · by_contra h
    have : realModel a ∈ Set.Ioo l u := ⟨hxl.1.trans_le (le_of_not_gt h), har.trans hru⟩
    exact hlu this (subset_closure ⟨a, rfl⟩)
  · by_contra h
    have : realModel b ∈ Set.Ioo l u := ⟨hlr.trans hrb, (le_of_not_gt h).trans_lt hxl.2⟩
    exact hlu this (subset_closure ⟨b, rfl⟩)

theorem realModel_gap_disjoint {a b : A} (hab : a ⋖ b) :
    Disjoint (Set.Ioo (realModel a) (realModel b))
      (closure (Set.range (realModel (A := A)))) := by
  apply Disjoint.closure_right _ isOpen_Ioo
  rw [Set.disjoint_left]
  rintro _ ⟨hax, hxb⟩ ⟨c, rfl⟩
  exact hab.2 ((realModel (A := A)).lt_iff_lt.mp hax)
    ((realModel (A := A)).lt_iff_lt.mp hxb)

/-- The complement consists exactly of intervals between adjacent orbit points. -/
theorem realModel_not_mem_closure_iff (x : ℝ) :
    x ∉ closure (Set.range (realModel (A := A))) ↔
      ∃ a b : A, a ⋖ b ∧ realModel a < x ∧ x < realModel b := by
  constructor
  · exact realModel_gap
  · rintro ⟨a, b, hab, ha, hb⟩ hx
    exact Set.disjoint_left.mp (realModel_gap_disjoint hab) ⟨ha, hb⟩ hx

end RealModel

end FnZPositiveCones.OrderedActions
