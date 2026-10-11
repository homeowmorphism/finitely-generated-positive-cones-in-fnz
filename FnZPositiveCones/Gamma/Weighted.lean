module

public import FnZPositiveCones.Actions.Weighted
public import FnZPositiveCones.Gamma.Basic
public import FnZPositiveCones.Gamma.Certificate
public import FnZPositiveCones.Gamma.Schreier

@[expose] public section

/-! The six-state action over the exact presented group. -/
namespace FnZPositiveCones

def sixStateDelta : GammaLetter → Equiv.Perm (Fin 6)
  | .a => Equiv.addRight 2
  | .b => Equiv.addRight (-1)

def sixWeight : GammaLetter → Fin 6 → FnZ 2
  | .a => sixAlpha
  | .b => sixBeta

def sixA : weightedPermGroup (Fin 6) (FnZ 2) :=
  weightedGenerator (sixStateDelta .a) sixAlpha

def sixB : weightedPermGroup (Fin 6) (FnZ 2) :=
  weightedGenerator (sixStateDelta .b) sixBeta

theorem six_transition_relation : sixB * sixA ^ 2 * sixB = sixA := by
  apply Subtype.ext
  apply Equiv.ext
  rintro ⟨s, h⟩
  change (sixB.val (sixA.val (sixA.val (sixB.val (s, h))))) = sixA.val (s, h)
  change (s + (-1) + 2 + 2 + (-1),
    h * sixBeta s * sixAlpha (s + (-1)) * sixAlpha (s + (-1) + 2) *
      sixBeta (s + (-1) + 2 + 2)) = (s + 2, h * sixAlpha s)
  have hs1 : s + (-1) = s - 1 := by abel
  have hs2 : s + (-1) + 2 = s + 1 := by omega
  have hs3 : s + (-1) + 2 + 2 = s + 3 := by omega
  have hs4 : s + (-1) + 2 + 2 + (-1) = s + 2 := by omega
  rw [hs4, hs3, hs2, hs1, sixWeightTable_relations s]
  simp only [mul_assoc]

theorem sixWeighted_relations (r : FreeGroup GammaLetter) (hr : r ∈ gammaRelations) :
    freeWeightedLift sixStateDelta sixWeight r = 1 := by
  have he : r = gammaRelator := by simpa [gammaRelations] using hr
  subst r
  change FreeGroup.lift _ gammaRelator = 1
  simp only [gammaRelator, map_mul, map_pow, map_inv, FreeGroup.lift_apply_of]
  change sixB⁻¹ * (sixA⁻¹)^2 * sixB⁻¹ * (sixA⁻¹)⁻¹ = 1
  have hi := congrArg Inv.inv six_transition_relation
  simp only [mul_inv_rev, ← inv_pow] at hi
  rw [← mul_assoc] at hi
  rw [hi]
  simp

def gamma_weighted_action : Gamma2 →* weightedPermGroup (Fin 6) (FnZ 2) :=
  presentedWeightedLift gammaRelations sixStateDelta sixWeight sixWeighted_relations

@[simp] theorem gamma_weighted_a (s : Fin 6) (h : FnZ 2) :
    weightedRightAction gamma_weighted_action (s, h) aGamma = (s + 2, h * sixAlpha s) :=
  presentedWeightedLift_generator _ _ _ _ _ _ _

@[simp] theorem gamma_weighted_b (s : Fin 6) (h : FnZ 2) :
    weightedRightAction gamma_weighted_action (s, h) bGamma = (s - 1, h * sixBeta s) := by
  rw [sub_eq_add_neg]
  exact presentedWeightedLift_generator gammaRelations sixStateDelta sixWeight
    sixWeighted_relations GammaLetter.b s h

def gammaFiniteResidue (g : Gamma2) : Fin 6 :=
  (ZMod.finEquiv 6).symm (gamma_phi g).toAdd

def gammaStateHom : Gamma2 →* Equiv.Perm (Fin 6) where
  toFun g := Equiv.addRight (gammaFiniteResidue g)
  map_one' := by
    ext s
    simp [gammaFiniteResidue, Equiv.addRight]
  map_mul' g h := by
    ext s
    simp [gammaFiniteResidue, Equiv.addRight, add_comm, add_left_comm]

theorem gamma_weighted_stateHom :
    weightedStateHom.comp gamma_weighted_action = gammaStateHom := by
  apply PresentedGroup.ext
  intro letter
  simp only [MonoidHom.comp_apply, gamma_weighted_action, presentedWeightedLift]
  cases letter <;> apply Equiv.ext <;> intro s
  · change (s + -2 : Fin 6) = s + gammaFiniteResidue aGamma
    have hres : gammaFiniteResidue aGamma = 4 := by
      change (ZMod.finEquiv 6).symm (gamma_phi aGamma).toAdd = 4
      rw [gamma_phi_a]
      decide
    rw [hres]
    rw [show (-2 : Fin 6) = 4 by decide]
  · change (s + -(-1) : Fin 6) = s + gammaFiniteResidue bGamma
    have hres : gammaFiniteResidue bGamma = 1 := by
      change (ZMod.finEquiv 6).symm (gamma_phi bGamma).toAdd = 1
      rw [gamma_phi_b]
      decide
    rw [hres]
    rw [neg_neg]

theorem gamma_weighted_state (s : Fin 6) (g : Gamma2) :
    weightedStateAction gamma_weighted_action s g = s - gammaFiniteResidue g := by
  have he := congrArg (fun f : Gamma2 →* Equiv.Perm (Fin 6) => f g⁻¹ s)
    gamma_weighted_stateHom
  change weightedStateAction gamma_weighted_action s g = _ at he
  rw [he]
  simp [gammaStateHom, gammaFiniteResidue, Equiv.addRight, sub_eq_add_neg]

theorem gamma_weighted_stabilizer : weightedStabilizer gamma_weighted_action 0 = gammaH := by
  ext g
  change weightedStateAction gamma_weighted_action 0 g = 0 ↔ gamma_phi g = 1
  rw [gamma_weighted_state]
  simp [gammaFiniteResidue]

/-- The weight homomorphism is defined on the supplied subgroup, with no chosen words. -/
def gammaWeightHom : gammaH →* FnZ 2 :=
  (stabilizerWeightHom gamma_weighted_action 0).comp
    (Subgroup.inclusion (le_of_eq gamma_weighted_stabilizer.symm))

theorem gammaWeightHom_apply (g : gammaH) :
    gammaWeightHom g = (weightedRightAction gamma_weighted_action (0, 1) g.val).2 := rfl

theorem gammaWeightHom_X : gammaWeightHom gammaX = productX := by
  rw [gammaWeightHom_apply]
  change (weightedRightAction gamma_weighted_action (0, 1) (aGamma * bGamma ^ 2)).2 = _
  simp [pow_two, weightedRightAction_mul, sixAlpha, sixBeta, Fin.reduceSub]

theorem gammaWeightHom_Y : gammaWeightHom gammaY0 = productY := by
  rw [gammaWeightHom_apply]
  change (weightedRightAction gamma_weighted_action (0, 1)
    (aGamma ^ 2 * bGamma ^ 2 * aGamma ^ 2)).2 = _
  simp only [pow_two, weightedRightAction_mul, gamma_weighted_a, gamma_weighted_b,
    Fin.reduceAdd, Fin.reduceSub, sixBeta, one_mul]
  convert sixWeightTable_Y using 1
  simp [pow_two, mul_assoc]

theorem gammaWeightHom_Z : gammaWeightHom gammaZ = productZ := by
  rw [gammaWeightHom_apply]
  change (weightedRightAction gamma_weighted_action (0, 1) (aGamma ^ 3)).2 = _
  simpa [pow_succ, weightedRightAction_mul, sixBeta, Fin.reduceAdd, Fin.reduceSub]
    using sixWeightTable_Z

theorem gammaWeightHom_C : gammaWeightHom gammaC = sixC := by
  rw [gammaWeightHom_apply]
  change (weightedRightAction gamma_weighted_action (0, 1) (bGamma ^ 6)).2 = _
  norm_num [pow_succ, weightedRightAction_mul, sixBeta, Fin.reduceSub,
    show (-1 : Fin 6) = 5 by decide]
  decide +revert

end FnZPositiveCones
