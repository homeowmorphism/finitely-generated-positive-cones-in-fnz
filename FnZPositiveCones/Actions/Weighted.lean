module

public import FnZPositiveCones.Interfaces

@[expose] public section

/-! Weighted permutations with noncommutative accumulators and right actions. -/
namespace FnZPositiveCones

universe u v w
variable {Q : Type u} {D : Type v} [Group D]

/-- One transition and its explicit inverse. -/
def weightedPerm (δ : Equiv.Perm Q) (ω : Q → D) : Equiv.Perm (Q × D) where
  toFun p := (δ p.1, p.2 * ω p.1)
  invFun p := (δ.symm p.1, p.2 * (ω (δ.symm p.1))⁻¹)
  left_inv p := by simp
  right_inv p := by simp

@[simp] theorem weightedPerm_apply (δ : Equiv.Perm Q) (ω : Q → D) (q : Q) (h : D) :
    weightedPerm δ ω (q, h) = (δ q, h * ω q) := rfl

@[simp] theorem weightedPerm_symm_apply (δ : Equiv.Perm Q) (ω : Q → D) (q : Q) (h : D) :
    (weightedPerm δ ω).symm (q, h) = (δ.symm q, h * (ω (δ.symm q))⁻¹) := rfl

def leftAccumulator (c : D) (p : Q × D) : Q × D := (p.1, c * p.2)

/-- Equivariance is closed under composition and inverse, so generator lifts
automatically retain it without choosing word representatives. -/
def weightedPermGroup (Q : Type u) (D : Type v) [Group D] :
    Subgroup (Equiv.Perm (Q × D)) where
  carrier := {f | ∀ c p, f (leftAccumulator c p) = leftAccumulator c (f p)}
  one_mem' := by
    change ∀ c p, (1 : Equiv.Perm (Q × D)) (leftAccumulator c p) = _
    intro c p
    rfl
  mul_mem' := by
    intro f g hf hg c p
    change f (g (leftAccumulator c p)) = leftAccumulator c (f (g p))
    rw [hg, hf]
  inv_mem' := by
    intro f hf c p
    apply f.injective
    change f (f.symm (leftAccumulator c p)) = f (leftAccumulator c (f.symm p))
    rw [f.apply_symm_apply, hf, f.apply_symm_apply]

def weightedGenerator (δ : Equiv.Perm Q) (ω : Q → D) : weightedPermGroup Q D :=
  ⟨weightedPerm δ ω, by
    change ∀ c p, weightedPerm δ ω (leftAccumulator c p) = _
    intro c p
    exact Prod.ext rfl (mul_assoc _ _ _)⟩

theorem weightedPermGroup_fst (f : weightedPermGroup Q D) (q : Q) (h : D) :
    (f.val (q, h)).1 = (f.val (q, 1)).1 := by
  have hf := congrArg Prod.fst (f.property h (q, 1))
  simpa [leftAccumulator] using hf

/-- Forgetting the weight gives an honest permutation of the state space. -/
def weightedStatePerm (f : weightedPermGroup Q D) : Equiv.Perm Q where
  toFun q := (f.val (q, 1)).1
  invFun q := (f.val.symm (q, 1)).1
  left_inv q := by
    change ((f⁻¹).val ((f.val (q, 1)).1, 1)).1 = q
    rw [← weightedPermGroup_fst f⁻¹ _ (f.val (q, 1)).2]
    exact congrArg Prod.fst (f.val.symm_apply_apply (q, 1))
  right_inv q := by
    change (f.val ((f.val.symm (q, 1)).1, 1)).1 = q
    rw [← weightedPermGroup_fst f _ (f.val.symm (q, 1)).2]
    exact congrArg Prod.fst (f.val.apply_symm_apply (q, 1))

def weightedStateHom : weightedPermGroup Q D →* Equiv.Perm Q where
  toFun := weightedStatePerm
  map_one' := by ext q; rfl
  map_mul' f g := by
    ext q
    exact weightedPermGroup_fst f _ _

variable {G : Type w} [Group G]

/-- Inverting the homomorphism argument implements the right-action convention. -/
def weightedRightAction (L : G →* weightedPermGroup Q D) (p : Q × D) (g : G) : Q × D :=
  (L g⁻¹).val p

@[simp] theorem weightedRightAction_one (L : G →* weightedPermGroup Q D) (p : Q × D) :
    weightedRightAction L p 1 = p := by simp [weightedRightAction]

theorem weightedRightAction_mul (L : G →* weightedPermGroup Q D)
    (p : Q × D) (g h : G) :
    weightedRightAction L p (g * h) = weightedRightAction L (weightedRightAction L p g) h := by
  simp [weightedRightAction, mul_inv_rev]

theorem weightedRightAction_equivariant (L : G →* weightedPermGroup Q D)
    (c : D) (p : Q × D) (g : G) :
    weightedRightAction L (leftAccumulator c p) g =
      leftAccumulator c (weightedRightAction L p g) := (L g⁻¹).property c p

def weightedStateAction (L : G →* weightedPermGroup Q D) (q : Q) (g : G) : Q :=
  (weightedRightAction L (q, 1) g).1

theorem weightedRightAction_from_one (L : G →* weightedPermGroup Q D)
    (q : Q) (h : D) (g : G) :
    weightedRightAction L (q, h) g =
      leftAccumulator h (weightedRightAction L (q, 1) g) := by
  simpa [leftAccumulator] using weightedRightAction_equivariant L h (q, 1) g

@[simp] theorem weightedRightAction_fst (L : G →* weightedPermGroup Q D)
    (q : Q) (h : D) (g : G) :
    (weightedRightAction L (q, h) g).1 = weightedStateAction L q g := by
  rw [weightedRightAction_from_one]; rfl

@[simp] theorem weightedStateAction_one (L : G →* weightedPermGroup Q D) (q : Q) :
    weightedStateAction L q 1 = q := by simp [weightedStateAction]

theorem weightedStateAction_mul (L : G →* weightedPermGroup Q D) (q : Q) (g h : G) :
    weightedStateAction L q (g * h) = weightedStateAction L (weightedStateAction L q g) h := by
  unfold weightedStateAction
  rw [weightedRightAction_mul]
  exact weightedRightAction_fst L _ _ _

def weightedStabilizer (L : G →* weightedPermGroup Q D) (q : Q) : Subgroup G where
  carrier := {g | weightedStateAction L q g = q}
  one_mem' := weightedStateAction_one L q
  mul_mem' := by
    intro g h hg hh
    change weightedStateAction L q (g * h) = q
    rw [weightedStateAction_mul, hg, hh]
  inv_mem' := by
    intro g hg
    have h := weightedStateAction_mul L q g g⁻¹
    rw [mul_inv_cancel, weightedStateAction_one, hg] at h
    exact h.symm

/-- On a state stabilizer the accumulated weight is multiplicative. -/
def stabilizerWeightHom (L : G →* weightedPermGroup Q D) (q : Q) :
    weightedStabilizer L q →* D where
  toFun g := (weightedRightAction L (q, 1) g.val).2
  map_one' := by simp
  map_mul' g h := by
    change (weightedRightAction L (q, 1) (g.val * h.val)).2 = _
    rw [weightedRightAction_mul]
    have hg : (weightedRightAction L (q, 1) g.val).1 = q := g.property
    have hp : weightedRightAction L (q, 1) g.val =
        (q, (weightedRightAction L (q, 1) g.val).2) := Prod.ext hg rfl
    conv_lhs => rw [hp, weightedRightAction_from_one]
    rfl

/-- Free generators have exactly the requested weighted right transitions. -/
def freeWeightedLift {ι : Type*} (δ : ι → Equiv.Perm Q) (ω : ι → Q → D) :
    FreeGroup ι →* weightedPermGroup Q D :=
  FreeGroup.lift fun i => (weightedGenerator (δ i) (ω i))⁻¹

@[simp] theorem freeWeightedLift_generator {ι : Type*}
    (δ : ι → Equiv.Perm Q) (ω : ι → Q → D) (i : ι) (q : Q) (h : D) :
    weightedRightAction (freeWeightedLift δ ω) (q, h) (FreeGroup.of i) =
      (δ i q, h * ω i q) := by
  simp [weightedRightAction, freeWeightedLift, weightedGenerator, weightedPerm]

/-- Presented actions require checked relators in the equivariant permutation group. -/
def presentedWeightedLift {ι : Type*} (rels : Set (FreeGroup ι))
    (δ : ι → Equiv.Perm Q) (ω : ι → Q → D)
    (hrels : ∀ r ∈ rels, freeWeightedLift δ ω r = 1) :
    PresentedGroup rels →* weightedPermGroup Q D :=
  PresentedGroup.toGroup hrels

@[simp] theorem presentedWeightedLift_generator {ι : Type*}
    (rels : Set (FreeGroup ι)) (δ : ι → Equiv.Perm Q) (ω : ι → Q → D)
    (hrels : ∀ r ∈ rels, freeWeightedLift δ ω r = 1)
    (i : ι) (q : Q) (h : D) :
    weightedRightAction (presentedWeightedLift rels δ ω hrels) (q, h)
      (PresentedGroup.of i) = (δ i q, h * ω i q) := by
  simp [weightedRightAction, presentedWeightedLift,
    weightedGenerator, weightedPerm]

end FnZPositiveCones
