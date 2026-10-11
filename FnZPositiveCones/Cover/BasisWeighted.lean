module

public import FnZPositiveCones.Cover.BasisSchreier
public import FnZPositiveCones.Actions.Weighted

@[expose] public section

/-! A labelled action proves independence of the explicit Schreier generators. -/
namespace FnZPositiveCones

variable (d : ℕ) [NeZero d]

abbrev CoverBasisIndex := Fin d ⊕ Unit
abbrev CoverBasisFreeGroup := FreeGroup (CoverBasisIndex d)

def modularTranslation : Equiv.Perm (ZMod d) where
  toFun j := j + 1
  invFun j := j - 1
  left_inv j := by ring
  right_inv j := by ring

def coverWeightedX : weightedPermGroup (ZMod d) (CoverBasisFreeGroup d) :=
  weightedGenerator (modularReflectionX d)
    (fun j => FreeGroup.of (Sum.inl ((modularFinEquiv d).symm j)))

def coverWeightedU : weightedPermGroup (ZMod d) (CoverBasisFreeGroup d) :=
  weightedGenerator (modularTranslation d)
    (fun j => if j.val + 1 = d then FreeGroup.of (Sum.inr ()) else 1)

/-- The original `y` has image `T_u⁻¹*T_x`, giving `y*x` the right transition `T_u`. -/
def coverWeightedLift : FreeGroup (Fin 2) →* weightedPermGroup (ZMod d) (CoverBasisFreeGroup d) :=
  FreeGroup.lift ![(coverWeightedX d)⁻¹, (coverWeightedU d)⁻¹ * coverWeightedX d]

theorem coverWeighted_stateHom :
    weightedStateHom.comp (coverWeightedLift d) = modularReflectionAction d := by
  apply FreeGroup.ext_hom
  intro i
  fin_cases i <;> ext j <;>
    simp [coverWeightedLift, coverWeightedX, coverWeightedU, weightedStateHom,
      weightedStatePerm, weightedGenerator, weightedPerm, modularTranslation,
      modularReflectionAction, modularReflectionX, modularReflectionY]

theorem coverWeighted_state (j : ZMod d) (w : FreeGroup (Fin 2)) :
    weightedStateAction (coverWeightedLift d) j w = modularRightAction d j w := by
  change weightedStateHom (coverWeightedLift d w⁻¹) j = modularReflectionAction d w⁻¹ j
  exact congrArg (fun f : Equiv.Perm (ZMod d) => f j)
    (DFunLike.congr_fun (coverWeighted_stateHom d) w⁻¹)

@[simp] theorem coverWeighted_x (j : ZMod d) (h : CoverBasisFreeGroup d) :
    weightedRightAction (coverWeightedLift d) (j, h) freeX =
      (-j, h * FreeGroup.of (Sum.inl ((modularFinEquiv d).symm j))) := by
  simp [weightedRightAction, coverWeightedLift, freeX, coverWeightedX,
    weightedGenerator, weightedPerm, modularReflectionX]

@[simp] theorem coverWeighted_u (j : ZMod d) (h : CoverBasisFreeGroup d) :
    weightedRightAction (coverWeightedLift d) (j, h) coverU =
      (j + 1, h * if j.val + 1 = d then FreeGroup.of (Sum.inr ()) else 1) := by
  simp [weightedRightAction, coverWeightedLift, coverU, freeX, freeY, coverWeightedU,
    weightedGenerator, weightedPerm, modularTranslation]

def coverWeightedStabilizerMap : coverSubgroup d →*
    weightedStabilizer (coverWeightedLift d) (0 : ZMod d) :=
  Subgroup.inclusion (by
    intro w hw
    change weightedStateAction (coverWeightedLift d) 0 w = 0
    rw [coverWeighted_state]
    exact hw)

def coverBasisWeight : coverSubgroup d →* CoverBasisFreeGroup d :=
  (stabilizerWeightHom (coverWeightedLift d) 0).comp (coverWeightedStabilizerMap d)

theorem coverBasisWeight_apply (w : coverSubgroup d) :
    coverBasisWeight d w = (weightedRightAction (coverWeightedLift d) (0, 1) w.val).2 := rfl

/-- Before the wrap, the tree path has weight one, with any initial accumulator. -/
theorem coverWeighted_u_short (m : ℕ) (hm : m < d) (h : CoverBasisFreeGroup d) :
    weightedRightAction (coverWeightedLift d) (0, h) (coverU ^ m) = ((m : ZMod d), h) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hm' : m < d := by omega
    rw [pow_succ, weightedRightAction_mul, ih hm', coverWeighted_u]
    simp [ZMod.val_natCast_of_lt hm', show m + 1 ≠ d by omega, Nat.cast_add, Nat.cast_one]

/-- The inverse of a short tree path also contributes no weight. -/
theorem coverWeighted_u_short_inverse (m : ℕ) (hm : m < d) (h : CoverBasisFreeGroup d) :
    weightedRightAction (coverWeightedLift d) ((m : ZMod d), h) (coverU ^ m)⁻¹ = (0, h) := by
  have he := weightedRightAction_mul (coverWeightedLift d) (0, h) (coverU ^ m) (coverU ^ m)⁻¹
  rw [mul_inv_cancel, weightedRightAction_one, coverWeighted_u_short d m hm h] at he
  exact he.symm

/-- The full path crosses the wrap exactly once, including when `d = 1`. -/
theorem coverWeighted_u_full (h : CoverBasisFreeGroup d) :
    weightedRightAction (coverWeightedLift d) (0, h) (coverU ^ d) =
      (0, h * FreeGroup.of (Sum.inr ())) := by
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have he : d - 1 + 1 = d := by omega
  have hm : d - 1 < d := by omega
  rw [show coverU ^ d = coverU ^ (d - 1) * coverU by rw [← pow_succ, he]]
  rw [weightedRightAction_mul, coverWeighted_u_short d (d - 1) hm h,
    coverWeighted_u]
  simp only [ZMod.val_natCast_of_lt hm, he, ite_true]
  apply Prod.ext
  · change ((d - 1 : ℕ) : ZMod d) + 1 = 0
    simpa using congrArg (fun n : ℕ => (n : ZMod d)) he
  · rfl

@[simp] theorem coverBasisWeight_a (j : Fin d) :
    coverBasisWeight d (coverBasisA d j) = FreeGroup.of (Sum.inl j) := by
  rw [coverBasisWeight_apply, coverBasisA_coe]
  rw [weightedRightAction_mul, weightedRightAction_mul,
    coverWeighted_u_short d j.val j.isLt, coverWeighted_x]
  have hj : (modularFinEquiv d).symm (j.val : ZMod d) = j :=
    (modularFinEquiv d).symm_apply_apply j
  rw [hj, one_mul, ← coverNegativeIndex_cast d j,
    coverWeighted_u_short_inverse d _ (coverNegativeIndex d j).isLt]

@[simp] theorem coverBasisWeight_c :
    coverBasisWeight d (coverBasisC d) = FreeGroup.of (Sum.inr ()) := by
  rw [coverBasisWeight_apply, coverBasisC_coe, coverWeighted_u_full]
  simp

end FnZPositiveCones
