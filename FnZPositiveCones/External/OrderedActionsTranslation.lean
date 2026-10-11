module

public import FnZPositiveCones.External.OrderedActionsRealization
public import FnZPositiveCones.External.Cofinal

@[expose] public section

namespace FnZPositiveCones.OrderedActions

@[simp] theorem realAut_mul_apply (f g : ℝ ≃o ℝ) (x : ℝ) : (f * g) x = f (g x) := rfl
@[simp] theorem realAut_one_apply (x : ℝ) : (1 : ℝ ≃o ℝ) x = x := rfl

theorem realAut_zpow_add_apply (f : ℝ ≃o ℝ) (m n : ℤ) (x : ℝ) :
    (f ^ (m + n)) x = (f ^ m) ((f ^ n) x) := by rw [zpow_add, realAut_mul_apply]

theorem realAut_zpow_cancel (f : ℝ ≃o ℝ) (m : ℤ) (x : ℝ) :
    (f ^ (-m)) ((f ^ m) x) = x := by
  rw [← realAut_zpow_add_apply, neg_add_cancel, zpow_zero, realAut_one_apply]

theorem realAut_orbit_strictMono (f : ℝ ≃o ℝ) (b : ℝ) (hb : b < f b) :
    StrictMono (fun k : ℤ => (f ^ k) b) := by
  apply strictMono_int_of_lt_succ
  intro k
  simpa only [zpow_add, zpow_one, realAut_mul_apply] using (f ^ k).strictMono hb

/-- A positive automorphism with cofinal integer orbit has an integer floor everywhere. -/
theorem realAut_exists_floor (f : ℝ ≃o ℝ) (b : ℝ) (hb : b < f b)
    (hc : ∀ x : ℝ, ∃ m n : ℤ, (f ^ m) b ≤ x ∧ x ≤ (f ^ n) b) (x : ℝ) :
    ∃ k : ℤ, (f ^ k) b ≤ x ∧ x < (f ^ (k + 1)) b := by
  obtain ⟨m, n, hm, hn⟩ := hc x
  have hmono := realAut_orbit_strictMono f b hb
  obtain ⟨k, hk, hmax⟩ := Int.exists_greatest_of_bdd
    (P := fun k => (f ^ k) b ≤ x)
    ⟨n, fun k hk => hmono.le_iff_le.mp (hk.trans hn)⟩ ⟨m, hm⟩
  refine ⟨k, hk, lt_of_not_ge (fun hh => ?_)⟩
  have := hmax (k + 1) hh
  omega

/-- Evaluation of a band coordinate using integer powers. -/
def bandEval (f : ℝ ≃o ℝ) (b : ℝ) (p : ℤ ×ₗ Set.Ico b (f b)) : ℝ :=
  (f ^ (ofLex p).1) (ofLex p).2.val

theorem bandEval_strictMono (f : ℝ ≃o ℝ) (b : ℝ) (hb : b < f b) :
    StrictMono (bandEval f b) := by
  intro p q hpq
  rcases Prod.Lex.lt_iff.mp hpq with hlt | ⟨he, hlt⟩
  · have hk : (ofLex p).1 + 1 ≤ (ofLex q).1 := by omega
    calc
      bandEval f b p < (f ^ (ofLex p).1) (f b) :=
        (f ^ (ofLex p).1).strictMono (ofLex p).2.property.2
      _ = (f ^ ((ofLex p).1 + 1)) b := by
        rw [realAut_zpow_add_apply, zpow_one]
      _ ≤ (f ^ (ofLex q).1) b := (realAut_orbit_strictMono f b hb).monotone hk
      _ ≤ bandEval f b q := (f ^ (ofLex q).1).monotone (ofLex q).2.property.1
  · dsimp only [bandEval]
    rw [he]
    exact (f ^ (ofLex q).1).strictMono hlt

theorem bandEval_surjective (f : ℝ ≃o ℝ) (b : ℝ) (hb : b < f b)
    (hc : ∀ x : ℝ, ∃ m n : ℤ, (f ^ m) b ≤ x ∧ x ≤ (f ^ n) b) :
    Function.Surjective (bandEval f b) := by
  intro x
  obtain ⟨k, hk, hku⟩ := realAut_exists_floor f b hb hc x
  have hy : (f ^ (-k)) x ∈ Set.Ico b (f b) := by
    constructor
    · have := (f ^ (-k)).monotone hk
      simpa only [realAut_zpow_cancel] using this
    · have := (f ^ (-k)).strictMono hku
      rw [← realAut_zpow_add_apply, neg_add_cancel_left, zpow_one] at this
      exact this
  refine ⟨toLex (k, ⟨(f ^ (-k)) x, hy⟩), ?_⟩
  change (f ^ k) ((f ^ (-k)) x) = x
  rw [← realAut_zpow_add_apply, add_neg_cancel, zpow_zero, realAut_one_apply]

/-- The line is the ordered sequence of fundamental half-open bands. -/
noncomputable def bandOrderIso (f : ℝ ≃o ℝ) (b : ℝ) (hb : b < f b)
    (hc : ∀ x : ℝ, ∃ m n : ℤ, (f ^ m) b ≤ x ∧ x ≤ (f ^ n) b) :
    (ℤ ×ₗ Set.Ico b (f b)) ≃o ℝ :=
  (bandEval_strictMono f b hb).orderIsoOfSurjective (bandEval f b)
    (bandEval_surjective f b hb hc)

/-- Affine coordinate in one fundamental band. -/
noncomputable def bandAffine (f : ℝ ≃o ℝ) (b : ℝ) (hb : b < f b) :
    Set.Ico b (f b) ≃o Set.Ico (0 : ℝ) 1 where
  toFun x := ⟨(x.val - b) / (f b - b), by
    constructor
    · exact div_nonneg (sub_nonneg.mpr x.property.1) (sub_pos.mpr hb).le
    · apply (div_lt_iff₀ (sub_pos.mpr hb)).mpr
      linarith [x.property.2]⟩
  invFun y := ⟨b + (f b - b) * y.val, by
    constructor
    · nlinarith [y.property.1]
    · nlinarith [y.property.2]⟩
  left_inv x := by
    apply Subtype.ext
    dsimp
    have hh : f b - b ≠ 0 := sub_ne_zero.mpr (ne_of_gt hb)
    field_simp [hh]
    ring
  right_inv y := by
    apply Subtype.ext
    dsimp
    have hh : f b - b ≠ 0 := sub_ne_zero.mpr (ne_of_gt hb)
    field_simp [hh]
    ring
  map_rel_iff' := by
    intro x y
    change (x.val - b) / (f b - b) ≤ (y.val - b) / (f b - b) ↔ x.val ≤ y.val
    rw [div_le_div_iff_of_pos_right (sub_pos.mpr hb), sub_le_sub_iff_right]

def unitBandEval (p : ℤ ×ₗ Set.Ico (0 : ℝ) 1) : ℝ := (ofLex p).1 + (ofLex p).2.val

theorem unitBandEval_strictMono : StrictMono unitBandEval := by
  intro p q hpq
  rcases Prod.Lex.lt_iff.mp hpq with hlt | ⟨he, hlt⟩
  · have hk : (ofLex p).1 + 1 ≤ (ofLex q).1 := by omega
    have hk' : ((ofLex p).1 : ℝ) + 1 ≤ (ofLex q).1 := by exact_mod_cast hk
    dsimp only [unitBandEval]
    linarith [(ofLex p).2.property.2, (ofLex q).2.property.1]
  · dsimp only [unitBandEval]
    rw [he]
    have hh : (ofLex p).2.val < (ofLex q).2.val := hlt
    linarith

theorem unitBandEval_surjective : Function.Surjective unitBandEval := by
  intro x
  have hy : x - (⌊x⌋ : ℤ) ∈ Set.Ico (0 : ℝ) 1 := by
    constructor
    · exact sub_nonneg.mpr (Int.floor_le x)
    · linarith [Int.lt_floor_add_one x]
  refine ⟨toLex (⌊x⌋, ⟨x - (⌊x⌋ : ℤ), hy⟩), ?_⟩
  change (⌊x⌋ : ℤ) + (x - (⌊x⌋ : ℤ)) = x
  ring

noncomputable def unitBandOrderIso : (ℤ ×ₗ Set.Ico (0 : ℝ) 1) ≃o ℝ :=
  unitBandEval_strictMono.orderIsoOfSurjective unitBandEval unitBandEval_surjective

/-- Conjugate a positive cofinal real automorphism to unit translation. -/
noncomputable def normalizeTranslation (f : ℝ ≃o ℝ) (b : ℝ) (hb : b < f b)
    (hc : ∀ x : ℝ, ∃ m n : ℤ, (f ^ m) b ≤ x ∧ x ≤ (f ^ n) b) : ℝ ≃o ℝ :=
  (bandOrderIso f b hb hc).symm.trans
    ((Prod.Lex.prodLexCongr (OrderIso.refl ℤ) (bandAffine f b hb)).trans unitBandOrderIso)

theorem normalizeTranslation_band (f : ℝ ≃o ℝ) (b : ℝ) (hb : b < f b)
    (hc : ∀ x : ℝ, ∃ m n : ℤ, (f ^ m) b ≤ x ∧ x ≤ (f ^ n) b)
    (p : ℤ ×ₗ Set.Ico b (f b)) :
    normalizeTranslation f b hb hc (bandEval f b p) =
      (ofLex p).1 + ((ofLex p).2.val - b) / (f b - b) := by
  change unitBandOrderIso ((Prod.Lex.prodLexCongr (OrderIso.refl ℤ) (bandAffine f b hb))
    ((bandOrderIso f b hb hc).symm ((bandOrderIso f b hb hc) p))) = _
  rw [OrderIso.symm_apply_apply]
  rfl

@[simp] theorem normalizeTranslation_base (f : ℝ ≃o ℝ) (b : ℝ) (hb : b < f b)
    (hc : ∀ x : ℝ, ∃ m n : ℤ, (f ^ m) b ≤ x ∧ x ≤ (f ^ n) b) :
    normalizeTranslation f b hb hc b = 0 := by
  have hh := normalizeTranslation_band f b hb hc (toLex (0, ⟨b, le_rfl, hb⟩))
  simpa only [bandEval, ofLex_toLex, zpow_zero, realAut_one_apply,
    Int.cast_zero, sub_self, zero_div, add_zero] using hh

theorem normalizeTranslation_conjugates (f : ℝ ≃o ℝ) (b : ℝ) (hb : b < f b)
    (hc : ∀ x : ℝ, ∃ m n : ℤ, (f ^ m) b ≤ x ∧ x ≤ (f ^ n) b) (x : ℝ) :
    normalizeTranslation f b hb hc (f x) = normalizeTranslation f b hb hc x + 1 := by
  obtain ⟨p, rfl⟩ := bandEval_surjective f b hb hc x
  have hh : f (bandEval f b p) = bandEval f b
      (toLex ((ofLex p).1 + 1, (ofLex p).2)) := by
    dsimp only [bandEval, ofLex_toLex]
    rw [show (ofLex p).1 + 1 = 1 + (ofLex p).1 by omega,
      realAut_zpow_add_apply, zpow_one]
  rw [hh, normalizeTranslation_band, normalizeTranslation_band]
  simp only [ofLex_toLex, Int.cast_add, Int.cast_one]
  ring

end FnZPositiveCones.OrderedActions

namespace FnZPositiveCones
universe u
variable {G : Type u} [Group G] {O : LeftGroupOrder G}

namespace TightRealization

/-- Transport a tight realization by a change of coordinate on the line. -/
noncomputable def conjugate (R : TightRealization O) (e : ℝ ≃o ℝ) : TightRealization O := by
  let ρ := (OrderedActions.conjugateOrderIso e).comp R.action
  have ha (g : G) (x : ℝ) : ρ g (e x) = e (R.action g x) := by
    simp [ρ, OrderedActions.conjugateOrderIso]
  have hrange : Set.range (fun g => ρ g (e R.base)) = e '' Set.range (fun g => R.action g R.base) := by
    simp only [ha]
    exact Set.range_comp e (fun g => R.action g R.base)
  have hclosure : closure (Set.range (fun g => ρ g (e R.base))) =
      e '' closure (Set.range (fun g => R.action g R.base)) := by
    rw [hrange]
    exact (e.toHomeomorph.image_closure _).symm
  refine {
    action := ρ
    base := e R.base
    order_iff := ?_
    unbounded_above := ?_
    unbounded_below := ?_
    orbit_gap := ?_ }
  · intro g h
    rw [ha, ha, e.le_iff_le]
    exact R.order_iff g h
  · intro x
    obtain ⟨g, hg⟩ := R.unbounded_above (e.symm x)
    refine ⟨g, ?_⟩
    rw [ha]
    simpa only [e.apply_symm_apply] using e.strictMono hg
  · intro x
    obtain ⟨g, hg⟩ := R.unbounded_below (e.symm x)
    refine ⟨g, ?_⟩
    rw [ha]
    simpa only [e.apply_symm_apply] using e.strictMono hg
  · intro x hx
    have hx' : e.symm x ∉ closure (Set.range (fun g => R.action g R.base)) := by
      intro h
      apply hx
      rw [hclosure]
      exact ⟨e.symm x, h, e.apply_symm_apply x⟩
    obtain ⟨g, h, hg, hh, hgap⟩ := R.orbit_gap (e.symm x) hx'
    refine ⟨g, h, ?_, ?_, ?_⟩
    · rw [ha]
      simpa only [e.apply_symm_apply] using e.strictMono hg
    · rw [ha]
      simpa only [e.apply_symm_apply] using e.strictMono hh
    · rw [ha, ha, hclosure, Set.disjoint_left]
      rintro y ⟨hgy, hyh⟩ ⟨z, hz, rfl⟩
      exact Set.disjoint_left.mp hgap ⟨e.lt_iff_lt.mp hgy, e.lt_iff_lt.mp hyh⟩ hz

@[simp] theorem conjugate_action (R : TightRealization O) (e : ℝ ≃o ℝ) (g : G) (x : ℝ) :
    (R.conjugate e).action g x = e (R.action g (e.symm x)) := rfl

@[simp] theorem conjugate_base (R : TightRealization O) (e : ℝ ≃o ℝ) :
    (R.conjugate e).base = e R.base := rfl

theorem cofinal_orbit (R : TightRealization O) (z : G) (hc : O.IsCofinal z) :
    ∀ x : ℝ, ∃ m n : ℤ, ((R.action z) ^ m) R.base ≤ x ∧ x ≤ ((R.action z) ^ n) R.base := by
  intro x
  obtain ⟨g, hg⟩ := R.unbounded_below x
  obtain ⟨h, hh⟩ := R.unbounded_above x
  obtain ⟨m, _, hm, _⟩ := hc g
  obtain ⟨_, n, _, hn⟩ := hc h
  have hm' := (R.order_iff _ _).mp hm
  have hn' := (R.order_iff _ _).mp hn
  rw [map_zpow] at hm' hn'
  exact ⟨m, n, hm'.trans hg.le, hh.le.trans hn'⟩

/-- A positive cofinal element acts as unit translation after a checked coordinate change. -/
theorem exists_translation (R : TightRealization O) (z : G) (hz : O.order.lt 1 z)
    (hc : O.IsCofinal z) :
    ∃ S : TightRealization O, S.base = 0 ∧ ∀ x : ℝ, S.action z x = x + 1 := by
  have hp : R.base < R.action z R.base := by
    let := O.order
    have h := (not_congr (R.order_iff z 1)).mp (not_le_of_gt hz)
    simpa only [map_one, OrderedActions.realAut_one_apply, not_le] using h
  let e := OrderedActions.normalizeTranslation (R.action z) R.base hp (R.cofinal_orbit z hc)
  refine ⟨R.conjugate e, ?_, ?_⟩
  · exact OrderedActions.normalizeTranslation_base _ _ _ _
  · intro x
    rw [conjugate_action]
    have hh := OrderedActions.normalizeTranslation_conjugates (R.action z) R.base hp
      (R.cofinal_orbit z hc) (e.symm x)
    exact hh.trans (congrArg (fun y : ℝ => y + 1) (e.apply_symm_apply x))

end TightRealization
end FnZPositiveCones
