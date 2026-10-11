module

public import FnZPositiveCones.Interfaces

@[expose] public section

/-! Modular reflection covers of the two-generator free group (D00–D03). -/

namespace FnZPositiveCones

/-- The first marked generator of the rank-two free group. -/
def freeX : FreeGroup (Fin 2) := FreeGroup.of 0
/-- The second marked generator of the rank-two free group. -/
def freeY : FreeGroup (Fin 2) := FreeGroup.of 1

def coverU : FreeGroup (Fin 2) := freeY * freeX

def coverG : FreeGroup (Fin 2) := freeY⁻¹ * freeX⁻¹ * freeY * freeX

/-- Reflection about zero. -/
def modularReflectionX (d : ℕ) : Equiv.Perm (ZMod d) where
  toFun j := -j
  invFun j := -j
  left_inv j := neg_neg j
  right_inv j := neg_neg j

/-- The second reflection is shifted by minus one. -/
def modularReflectionY (d : ℕ) : Equiv.Perm (ZMod d) where
  toFun j := -j - 1
  invFun j := -j - 1
  left_inv j := by ring
  right_inv j := by ring

/-- The left permutation representation used to define the right action.
Both generator images are involutions; inversion of the argument below reverses words. -/
def modularReflectionAction (d : ℕ) [NeZero d] :
    FreeGroup (Fin 2) →* Equiv.Perm (ZMod d) :=
  FreeGroup.lift (fun i => if i = 0 then modularReflectionX d else modularReflectionY d)

/-- Right actions read group words from left to right. -/
def modularRightAction (d : ℕ) [NeZero d] (j : ZMod d)
    (w : FreeGroup (Fin 2)) : ZMod d := modularReflectionAction d w⁻¹ j

@[simp] theorem modularRightAction_one (d : ℕ) [NeZero d] (j : ZMod d) :
    modularRightAction d j 1 = j := by simp [modularRightAction]

theorem modularRightAction_mul (d : ℕ) [NeZero d] (j : ZMod d)
    (w v : FreeGroup (Fin 2)) :
    modularRightAction d j (w * v) = modularRightAction d (modularRightAction d j w) v := by
  simp [modularRightAction, mul_inv_rev]

@[simp] theorem modularRightAction_x (d : ℕ) [NeZero d] (j : ZMod d) :
    modularRightAction d j freeX = -j := by
  simp [modularRightAction, modularReflectionAction, freeX, modularReflectionX]

@[simp] theorem modularRightAction_y (d : ℕ) [NeZero d] (j : ZMod d) :
    modularRightAction d j freeY = -j - 1 := by
  simp [modularRightAction, modularReflectionAction, freeY, modularReflectionY]

@[simp] theorem modularRightAction_x_inv (d : ℕ) [NeZero d] (j : ZMod d) :
    modularRightAction d j freeX⁻¹ = -j := by
  simp [modularRightAction, modularReflectionAction, freeX, modularReflectionX]

@[simp] theorem modularRightAction_y_inv (d : ℕ) [NeZero d] (j : ZMod d) :
    modularRightAction d j freeY⁻¹ = -j - 1 := by
  simp [modularRightAction, modularReflectionAction, freeY, modularReflectionY]

@[simp] theorem modularRightAction_u (d : ℕ) [NeZero d] (j : ZMod d) :
    modularRightAction d j coverU = j + 1 := by
  simp [coverU, modularRightAction_mul, add_comm]

@[simp] theorem modularRightAction_g (d : ℕ) [NeZero d] (j : ZMod d) :
    modularRightAction d j coverG = j + 2 := by
  simp [coverG, modularRightAction_mul]
  ring

@[simp] theorem modularRightAction_u_pow (d : ℕ) [NeZero d] (j : ZMod d) (k : ℕ) :
    modularRightAction d j (coverU ^ k) = j + k := by
  induction k with
  | zero => simp
  | succ k hk => simp [pow_succ, modularRightAction_mul, hk, add_assoc]

@[simp] theorem modularRightAction_g_pow (d : ℕ) [NeZero d] (j : ZMod d) (k : ℕ) :
    modularRightAction d j (coverG ^ k) = j + 2 * k := by
  induction k with
  | zero => simp
  | succ k hk => simp [pow_succ, modularRightAction_mul, hk, mul_add, add_assoc]

/-- The two word computations, together with all their natural powers. -/
theorem modular_word_actions (d : ℕ) [NeZero d] (j : ZMod d) (k : ℕ) :
    modularRightAction d j (coverU ^ k) = j + k ∧
    modularRightAction d j (coverG ^ k) = j + 2 * k :=
  ⟨modularRightAction_u_pow d j k, modularRightAction_g_pow d j k⟩

/-- Reversing an action step requires the group inverse. -/
theorem modularRightAction_eq_iff (d : ℕ) [NeZero d] (j j' : ZMod d)
    (w : FreeGroup (Fin 2)) :
    modularRightAction d j w = j' ↔ j = modularRightAction d j' w⁻¹ := by
  constructor
  · intro h
    rw [← h, ← modularRightAction_mul, mul_inv_cancel, modularRightAction_one]
  · intro h
    rw [h, ← modularRightAction_mul, inv_mul_cancel, modularRightAction_one]

/-- The zero-state stabilizer, retaining the right-action convention. -/
def coverSubgroup (d : ℕ) [NeZero d] : Subgroup (FreeGroup (Fin 2)) where
  carrier := {w | modularRightAction d 0 w = 0}
  one_mem' := by simp
  mul_mem' := by
    intro w v hw hv
    change modularRightAction d 0 (w * v) = 0
    rw [modularRightAction_mul, hw, hv]
  inv_mem' := by
    intro w hw
    exact ((modularRightAction_eq_iff d 0 0 w).mp hw).symm

@[simp] theorem mem_coverSubgroup (d : ℕ) [NeZero d] (w : FreeGroup (Fin 2)) :
    w ∈ coverSubgroup d ↔ modularRightAction d 0 w = 0 := Iff.rfl

/-- Equal orbit states are exactly equal right cosets. -/
theorem modularRightAction_eq_iff_mul_inv_mem (d : ℕ) [NeZero d]
    (w v : FreeGroup (Fin 2)) :
    modularRightAction d 0 w = modularRightAction d 0 v ↔ w * v⁻¹ ∈ coverSubgroup d := by
  rw [mem_coverSubgroup, modularRightAction_mul,
    modularRightAction_eq_iff d _ 0 v⁻¹, inv_inv]

/-- Powers of `u` visit every residue, including for `d = 1`. -/
theorem modularRightAction_transitive (d : ℕ) [NeZero d] (j : ZMod d) :
    ∃ w : FreeGroup (Fin 2), modularRightAction d 0 w = j := by
  refine ⟨coverU ^ j.val, ?_⟩
  simp

/-- Right cosets are identified with their zero-state images, with a checked inverse. -/
def coverRightCosetEquiv (d : ℕ) [NeZero d] :
    Quotient (QuotientGroup.rightRel (coverSubgroup d)) ≃ ZMod d where
  toFun := Quotient.lift (modularRightAction d 0) (by
    intro w v h
    exact ((modularRightAction_eq_iff_mul_inv_mem d v w).mpr
      (QuotientGroup.rightRel_apply.mp h)).symm)
  invFun j := Quotient.mk _ (coverU ^ j.val)
  left_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | h w =>
      apply Quotient.sound
      apply QuotientGroup.rightRel_apply.mpr
      apply (modularRightAction_eq_iff_mul_inv_mem d _ _).mp
      simp
  right_inv j := by
    change modularRightAction d 0 (coverU ^ j.val) = j
    simp

/-- The finite orbit, rather than the infinite ambient group, computes the index. -/
theorem cover_stabilizer_index (d : ℕ) [NeZero d] : (coverSubgroup d).index = d := by
  rw [Subgroup.index_eq_card]
  calc
    Nat.card (FreeGroup (Fin 2) ⧸ coverSubgroup d) = Nat.card (ZMod d) :=
      Nat.card_congr ((QuotientGroup.quotientRightRelEquivQuotientLeftRel
        (coverSubgroup d)).symm.trans (coverRightCosetEquiv d))
    _ = d := by rw [Nat.card_eq_fintype_card, ZMod.card]

/-- Odd modulus makes two a unit by coprimality, including odd composite moduli. -/
theorem two_isUnit_of_odd (d : ℕ) (hd : Odd d) : IsUnit (2 : ZMod d) := by
  exact (ZMod.isUnit_iff_coprime 2 d).mpr (Nat.coprime_two_left.mpr hd)

/-- Natural representatives give a bijection from `Fin d` to `ZMod d`. -/
def modularFinEquiv (d : ℕ) [NeZero d] : Fin d ≃ ZMod d where
  toFun k := (k.val : ZMod d)
  invFun j := ⟨j.val, j.val_lt⟩
  left_inv k := by ext; exact ZMod.val_natCast_of_lt k.isLt
  right_inv j := ZMod.natCast_zmod_val j

/-- Multiplication by two enumerates every residue exactly once for odd positive modulus. -/
theorem doubling_fin_bijective (d : ℕ) [NeZero d] (hd : Odd d) :
    Function.Bijective (fun k : Fin d => (2 : ZMod d) * (k.val : ZMod d)) := by
  exact (IsUnit.isUnit_iff_mulLeft_bijective.mp (two_isUnit_of_odd d hd)).comp
    (modularFinEquiv d).bijective

/-- The orbit of the commutator word is transitive exactly for odd modulus. -/
theorem doubling_orbit_parity (d : ℕ) [NeZero d] :
    (∀ j : ZMod d, ∃ k : ℕ, modularRightAction d 0 (coverG ^ k) = j) ↔ Odd d := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := h 1
    have hu : IsUnit (2 : ZMod d) := IsUnit.of_mul_eq_one (k : ZMod d) (by simpa using hk)
    exact Nat.coprime_two_left.mp ((ZMod.isUnit_iff_coprime 2 d).mp hu)
  · intro hd j
    obtain ⟨k, hk⟩ := (doubling_fin_bijective d hd).surjective j
    exact ⟨k.val, by simpa using hk⟩

/-- Reduction modulo two separates the two translation-by-two orbits for even modulus. -/
def modularParity (d : ℕ) (hd : Even d) : ZMod d →+* ZMod 2 :=
  ZMod.castHom hd.two_dvd (ZMod 2)

/-- Every state is reached by translation by two from either zero or one. -/
theorem doubling_orbit_zero_or_one (d : ℕ) [NeZero d] (j : ZMod d) :
    (∃ k : ℕ, modularRightAction d 0 (coverG ^ k) = j) ∨
    (∃ k : ℕ, modularRightAction d 1 (coverG ^ k) = j) := by
  have hmod : j.val % 2 = 0 ∨ j.val % 2 = 1 := by omega
  rcases hmod with hmod | hmod
  · left
    refine ⟨j.val / 2, ?_⟩
    have hv : 2 * (j.val / 2) = j.val := by omega
    rw [modularRightAction_g_pow, zero_add]
    calc
      (2 : ZMod d) * (j.val / 2 : ℕ) = (j.val : ZMod d) := by
        simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one] using
          congrArg (fun k : ℕ => (k : ZMod d)) hv
      _ = j := ZMod.natCast_zmod_val j
  · right
    refine ⟨j.val / 2, ?_⟩
    have hv : 1 + 2 * (j.val / 2) = j.val := by omega
    rw [modularRightAction_g_pow]
    calc
      (1 : ZMod d) + 2 * (j.val / 2 : ℕ) = (j.val : ZMod d) := by
        simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one] using
          congrArg (fun k : ℕ => (k : ZMod d)) hv
      _ = j := ZMod.natCast_zmod_val j

/-- The two displayed orbits are disjoint whenever the modulus is even. -/
theorem doubling_even_orbits_disjoint (d : ℕ) [NeZero d] (hd : Even d) (k l : ℕ) :
    modularRightAction d 0 (coverG ^ k) ≠ modularRightAction d 1 (coverG ^ l) := by
  intro h
  have hp := congrArg (modularParity d hd) h
  simp only [modularRightAction_g_pow, zero_add, map_mul, map_add, map_ofNat,
    map_natCast, map_one] at hp
  have hp' : (2 : ZMod 2) * (k : ZMod 2) = 1 + 2 * (l : ZMod 2) := hp
  rw [show (2 : ZMod 2) = 0 from rfl, zero_mul, zero_mul, add_zero] at hp'
  exact zero_ne_one hp'

/-- In even degree there are exactly two orbits, represented by zero and one. -/
theorem doubling_even_two_orbits (d : ℕ) [NeZero d] (hd : Even d) :
    (∀ j : ZMod d,
      (∃ k : ℕ, modularRightAction d 0 (coverG ^ k) = j) ∨
      (∃ k : ℕ, modularRightAction d 1 (coverG ^ k) = j)) ∧
    (∀ k l : ℕ,
      modularRightAction d 0 (coverG ^ k) ≠ modularRightAction d 1 (coverG ^ l)) :=
  ⟨doubling_orbit_zero_or_one d, doubling_even_orbits_disjoint d hd⟩

end FnZPositiveCones
