module

public import FnZPositiveCones.External.OrderedActionsTranslation
public import Mathlib.Topology.Instances.AddCircle.Real
public import Mathlib.Dynamics.Circle.RotationNumber.TranslationNumber

@[expose] public section

namespace FnZPositiveCones.OrderedActions

/-- Regard a unit-translation-equivariant order automorphism as a degree-one lift. -/
def degreeOneLift (f : ℝ ≃o ℝ) (hf : ∀ x : ℝ, f (x + 1) = f x + 1) : CircleDeg1Lift where
  toFun := f
  monotone' := f.monotone
  map_add_one' := hf

theorem degreeOne_add_int (f : ℝ ≃o ℝ) (hf : ∀ x : ℝ, f (x + 1) = f x + 1)
    (x : ℝ) (m : ℤ) : f (x + m) = f x + m :=
  (degreeOneLift f hf).map_add_int x m

theorem degreeOne_symm (f : ℝ ≃o ℝ) (hf : ∀ x : ℝ, f (x + 1) = f x + 1) :
    ∀ x : ℝ, f.symm (x + 1) = f.symm x + 1 := by
  intro x
  apply f.injective
  simp only [f.apply_symm_apply, hf]

/-- Descent through the integer quotient, with its equivalence relation checked. -/
def circleMap (f : ℝ ≃o ℝ) (hf : ∀ x : ℝ, f (x + 1) = f x + 1) :
    AddCircle (1 : ℝ) → AddCircle (1 : ℝ) :=
  Quotient.map (sa := QuotientAddGroup.leftRel (AddSubgroup.zmultiples (1 : ℝ)))
    (sb := QuotientAddGroup.leftRel (AddSubgroup.zmultiples (1 : ℝ))) f (by
    intro a b hab
    change QuotientAddGroup.leftRel (AddSubgroup.zmultiples (1 : ℝ)) a b at hab
    change QuotientAddGroup.leftRel (AddSubgroup.zmultiples (1 : ℝ)) (f a) (f b)
    rw [QuotientAddGroup.leftRel_apply] at hab ⊢
    obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.mp hab
    have hb : b = a + (m : ℝ) := by
      simp only [zsmul_eq_mul, mul_one] at hm
      linarith
    rw [hb, degreeOne_add_int f hf]
    exact AddSubgroup.mem_zmultiples_iff.mpr ⟨m, by simp [zsmul_eq_mul]⟩)

@[simp] theorem circleMap_coe (f : ℝ ≃o ℝ) (hf : ∀ x : ℝ, f (x + 1) = f x + 1)
    (x : ℝ) : circleMap f hf (x : AddCircle (1 : ℝ)) = (f x : AddCircle (1 : ℝ)) := rfl

/-- The descended map has the descended inverse. -/
def circlePerm (f : ℝ ≃o ℝ) (hf : ∀ x : ℝ, f (x + 1) = f x + 1) :
    Equiv.Perm (AddCircle (1 : ℝ)) where
  toFun := circleMap f hf
  invFun := circleMap f.symm (degreeOne_symm f hf)
  left_inv x := by induction x using QuotientAddGroup.induction_on; simp
  right_inv x := by induction x using QuotientAddGroup.induction_on; simp

@[simp] theorem circlePerm_coe (f : ℝ ≃o ℝ) (hf : ∀ x : ℝ, f (x + 1) = f x + 1)
    (x : ℝ) : circlePerm f hf (x : AddCircle (1 : ℝ)) = (f x : AddCircle (1 : ℝ)) := rfl

theorem degreeOne_toIcoMod (f : ℝ ≃o ℝ) (hf : ∀ x : ℝ, f (x + 1) = f x + 1)
    (a b : ℝ) :
    f (toIcoMod (show (0 : ℝ) < 1 by norm_num) a b) =
      toIcoMod (show (0 : ℝ) < 1 by norm_num) (f a) (f b) := by
  symm
  apply (toIcoMod_eq_iff (show (0 : ℝ) < 1 by norm_num)).mpr
  obtain ⟨hm, n, hn⟩ := (toIcoMod_eq_iff (show (0 : ℝ) < 1 by norm_num)).mp (rfl :
    toIcoMod (show (0 : ℝ) < 1 by norm_num) a b = _)
  refine ⟨⟨f.monotone hm.1, ?_⟩, n, ?_⟩
  · simpa only [hf] using f.strictMono hm.2
  · conv_lhs => rw [hn]
    simpa only [zsmul_eq_mul, mul_one] using degreeOne_add_int f hf
      (toIcoMod (show (0 : ℝ) < 1 by norm_num) a b) n

theorem degreeOne_toIocMod (f : ℝ ≃o ℝ) (hf : ∀ x : ℝ, f (x + 1) = f x + 1)
    (a b : ℝ) :
    f (toIocMod (show (0 : ℝ) < 1 by norm_num) a b) =
      toIocMod (show (0 : ℝ) < 1 by norm_num) (f a) (f b) := by
  symm
  apply (toIocMod_eq_iff (show (0 : ℝ) < 1 by norm_num)).mpr
  obtain ⟨hm, n, hn⟩ := (toIocMod_eq_iff (show (0 : ℝ) < 1 by norm_num)).mp (rfl :
    toIocMod (show (0 : ℝ) < 1 by norm_num) a b = _)
  refine ⟨⟨f.strictMono hm.1, ?_⟩, n, ?_⟩
  · simpa only [hf] using f.monotone hm.2
  · conv_lhs => rw [hn]
    simpa only [zsmul_eq_mul, mul_one] using degreeOne_add_int f hf
      (toIocMod (show (0 : ℝ) < 1 by norm_num) a b) n

/-- Descent preserves the actual circular order supplied by pinned mathlib. -/
theorem circlePerm_btw_iff (f : ℝ ≃o ℝ) (hf : ∀ x : ℝ, f (x + 1) = f x + 1)
    (a b c : AddCircle (1 : ℝ)) :
    btw (circlePerm f hf a) (circlePerm f hf b) (circlePerm f hf c) ↔ btw a b c := by
  induction a using QuotientAddGroup.induction_on
  induction b using QuotientAddGroup.induction_on
  induction c using QuotientAddGroup.induction_on
  simp only [circlePerm_coe, QuotientAddGroup.btw_coe_iff,
    ← degreeOne_toIcoMod f hf, ← degreeOne_toIocMod f hf, f.le_iff_le]

theorem circlePerm_preserves_btw (f : ℝ ≃o ℝ) (hf : ∀ x : ℝ, f (x + 1) = f x + 1) :
    ∀ a b c : AddCircle (1 : ℝ), btw a b c →
      btw (circlePerm f hf a) (circlePerm f hf b) (circlePerm f hf c) :=
  fun a b c h => (circlePerm_btw_iff f hf a b c).mpr h

theorem circlePerm_continuous (f : ℝ ≃o ℝ) (hf : ∀ x : ℝ, f (x + 1) = f x + 1) :
    Continuous (circlePerm f hf) := by
  apply continuous_coinduced_dom.mpr
  exact (AddCircle.continuous_mk' (1 : ℝ)).comp f.continuous

/-- Descent respects multiplication and hence turns equivariant real actions into circle actions. -/
def circleAction {G : Type*} [Group G] (ρ : G →* (ℝ ≃o ℝ))
    (hρ : ∀ g : G, ∀ x : ℝ, ρ g (x + 1) = ρ g x + 1) :
    G →* Equiv.Perm (AddCircle (1 : ℝ)) where
  toFun g := circlePerm (ρ g) (hρ g)
  map_one' := by
    ext x
    induction x using QuotientAddGroup.induction_on
    simp
  map_mul' g h := by
    ext x
    induction x using QuotientAddGroup.induction_on
    simp only [circlePerm_coe, Equiv.Perm.mul_apply, map_mul, realAut_mul_apply]

theorem circleAction_preserves_btw {G : Type*} [Group G] (ρ : G →* (ℝ ≃o ℝ))
    (hρ : ∀ g : G, ∀ x : ℝ, ρ g (x + 1) = ρ g x + 1) (g : G) :
    ∀ a b c : AddCircle (1 : ℝ), btw a b c →
      btw (circleAction ρ hρ g a) (circleAction ρ hρ g b) (circleAction ρ hρ g c) :=
  circlePerm_preserves_btw _ _

theorem central_translation_equivariant {G : Type*} [Group G] (ρ : G →* (ℝ ≃o ℝ))
    (z : G) (hz : ∀ x : ℝ, ρ z x = x + 1) (hcentral : ∀ g : G, Commute z g) :
    ∀ g : G, ∀ x : ℝ, ρ g (x + 1) = ρ g x + 1 := by
  intro g x
  rw [← hz x, ← realAut_mul_apply, ← map_mul, ← (hcentral g).eq,
    map_mul, realAut_mul_apply, hz]

end FnZPositiveCones.OrderedActions
