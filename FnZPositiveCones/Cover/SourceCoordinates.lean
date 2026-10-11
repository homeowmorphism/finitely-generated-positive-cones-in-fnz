module

public import FnZPositiveCones.Cover.Modular

@[expose] public section

/-! The explicit relabelling between modular states and the paper's staggered vertices. -/
namespace FnZPositiveCones

def sourceRelabelFn (d : ℕ) (j : Fin d) : Fin d :=
  if h : 2 * j.val < d then ⟨2 * j.val, h⟩
  else ⟨2 * (d - j.val) - 1, by omega⟩

def sourceRelabelInvFn (d : ℕ) (i : Fin d) : Fin d :=
  if h : i.val % 2 = 0 then ⟨i.val / 2, by omega⟩
  else ⟨d - (i.val + 1) / 2, by omega⟩

theorem sourceRelabelFn_val (d : ℕ) (j : Fin d) :
    (sourceRelabelFn d j).val =
      if 2 * j.val < d then 2 * j.val else 2 * (d - j.val) - 1 := by
  unfold sourceRelabelFn
  split_ifs <;> rfl

theorem sourceRelabelInvFn_val (d : ℕ) (i : Fin d) :
    (sourceRelabelInvFn d i).val =
      if i.val % 2 = 0 then i.val / 2 else d - (i.val + 1) / 2 := by
  unfold sourceRelabelInvFn
  split_ifs <;> rfl

theorem sourceRelabel_left_inv (d : ℕ) (j : Fin d) :
    sourceRelabelInvFn d (sourceRelabelFn d j) = j := by
  apply Fin.ext
  simp only [sourceRelabelInvFn_val, sourceRelabelFn_val]
  split_ifs <;> omega

theorem sourceRelabel_right_inv (d : ℕ) (i : Fin d) :
    sourceRelabelFn d (sourceRelabelInvFn d i) = i := by
  apply Fin.ext
  simp only [sourceRelabelInvFn_val, sourceRelabelFn_val]
  split_ifs <;> omega

/-- The even labels increase and the odd labels decrease around the modular orbit. -/
def sourceRelabel (d : ℕ) : Fin d ≃ Fin d where
  toFun := sourceRelabelFn d
  invFun := sourceRelabelInvFn d
  left_inv := sourceRelabel_left_inv d
  right_inv := sourceRelabel_right_inv d

@[simp] theorem sourceRelabel_val (d : ℕ) (j : Fin d) :
    (sourceRelabel d j).val =
      if 2 * j.val < d then 2 * j.val else 2 * (d - j.val) - 1 := by
  change (sourceRelabelFn d j).val = _
  unfold sourceRelabelFn
  split_ifs <;> rfl

/-- Swap `(1,2),(3,4),...`, leaving zero and any unpaired last vertex fixed. -/
def staggeredXFn (d : ℕ) (i : Fin d) : Fin d :=
  if h : i.val % 2 = 0 then
    if hz : i.val = 0 then i else ⟨i.val - 1, by omega⟩
  else if hn : i.val + 1 < d then ⟨i.val + 1, hn⟩ else i

/-- Swap `(0,1),(2,3),...`, leaving any unpaired last vertex fixed. -/
def staggeredYFn (d : ℕ) (i : Fin d) : Fin d :=
  if h : i.val % 2 = 1 then ⟨i.val - 1, by omega⟩
  else if hn : i.val + 1 < d then ⟨i.val + 1, hn⟩ else i

theorem staggeredXFn_val (d : ℕ) (i : Fin d) :
    (staggeredXFn d i).val =
      if i.val % 2 = 0 then (if i.val = 0 then i.val else i.val - 1)
      else if i.val + 1 < d then i.val + 1 else i.val := by
  unfold staggeredXFn
  split_ifs <;> rfl

theorem staggeredYFn_val (d : ℕ) (i : Fin d) :
    (staggeredYFn d i).val =
      if i.val % 2 = 1 then i.val - 1
      else if i.val + 1 < d then i.val + 1 else i.val := by
  unfold staggeredYFn
  split_ifs <;> rfl

theorem staggeredXFn_involutive (d : ℕ) : Function.Involutive (staggeredXFn d) := by
  intro i
  apply Fin.ext
  simp only [staggeredXFn_val]
  split_ifs <;> (first | contradiction | omega)

theorem staggeredYFn_involutive (d : ℕ) : Function.Involutive (staggeredYFn d) := by
  intro i
  apply Fin.ext
  simp only [staggeredYFn_val]
  split_ifs <;> omega

def staggeredX (d : ℕ) : Equiv.Perm (Fin d) :=
  ⟨staggeredXFn d, staggeredXFn d, staggeredXFn_involutive d, staggeredXFn_involutive d⟩

def staggeredY (d : ℕ) : Equiv.Perm (Fin d) :=
  ⟨staggeredYFn d, staggeredYFn d, staggeredYFn_involutive d, staggeredYFn_involutive d⟩

theorem staggeredX_val (d : ℕ) (i : Fin d) :
    (staggeredX d i).val =
      if i.val % 2 = 0 then (if i.val = 0 then i.val else i.val - 1)
      else if i.val + 1 < d then i.val + 1 else i.val := by
  change (staggeredXFn d i).val = _
  simp only [staggeredXFn]
  split_ifs <;> rfl

theorem staggeredY_val (d : ℕ) (i : Fin d) :
    (staggeredY d i).val =
      if i.val % 2 = 1 then i.val - 1
      else if i.val + 1 < d then i.val + 1 else i.val := by
  change (staggeredYFn d i).val = _
  simp only [staggeredYFn]
  split_ifs <;> rfl

theorem staggeredX_swap_pair (d k : ℕ) (hk : 1 ≤ k) (hd : 2 * k < d) :
    staggeredX d ⟨2 * k - 1, by omega⟩ = ⟨2 * k, hd⟩ ∧
      staggeredX d ⟨2 * k, hd⟩ = ⟨2 * k - 1, by omega⟩ := by
  constructor <;> apply Fin.ext <;>
    rw [staggeredX_val] <;> dsimp <;> split_ifs <;> omega

theorem staggeredY_swap_pair (d k : ℕ) (hk : 1 ≤ k) (hd : 2 * k - 1 < d) :
    staggeredY d ⟨2 * k - 2, by omega⟩ = ⟨2 * k - 1, hd⟩ ∧
      staggeredY d ⟨2 * k - 1, hd⟩ = ⟨2 * k - 2, by omega⟩ := by
  constructor <;> apply Fin.ext <;>
    rw [staggeredY_val] <;> dsimp <;> split_ifs <;> omega

/-- Outside the first disjoint family of pairs, exactly these vertices remain fixed. -/
theorem staggeredX_fixed_iff (d : ℕ) (i : Fin d) :
    staggeredX d i = i ↔ i.val = 0 ∨ (i.val + 1 = d ∧ i.val % 2 = 1) := by
  rw [Fin.ext_iff, staggeredX_val]
  have hi := i.isLt
  split_ifs <;> omega

/-- Outside the second disjoint family of pairs, only an unpaired last vertex is fixed. -/
theorem staggeredY_fixed_iff (d : ℕ) (i : Fin d) :
    staggeredY d i = i ↔ i.val + 1 = d ∧ i.val % 2 = 0 := by
  rw [Fin.ext_iff, staggeredY_val]
  have hi := i.isLt
  split_ifs <;> omega

variable (d : ℕ) [NeZero d]

def modularSourceEquiv : ZMod d ≃ Fin d := (modularFinEquiv d).symm.trans (sourceRelabel d)

@[simp] theorem modularSourceEquiv_val (j : ZMod d) :
    (modularSourceEquiv d j).val =
      if 2 * j.val < d then 2 * j.val else 2 * (d - j.val) - 1 := by
  exact sourceRelabel_val d ((modularFinEquiv d).symm j)

theorem source_neg_val (j : ZMod d) :
    (-j).val = if j.val = 0 then 0 else d - j.val := by
  by_cases hj : j = 0
  · simp [hj]
  · let : NeZero j := ⟨hj⟩
    rw [ZMod.val_neg_of_ne_zero j]
    have hv : j.val ≠ 0 := by simpa using hj
    simp [hv]

theorem source_neg_sub_one_val (j : ZMod d) : (-j - 1).val = d - 1 - j.val := by
  have hj := j.val_lt
  have hnat : (d - 1 - j.val) + j.val + 1 = d := by omega
  have he := congrArg (fun n : ℕ => (n : ZMod d)) hnat
  simp only [Nat.cast_add, Nat.cast_one, ZMod.natCast_zmod_val, ZMod.natCast_self] at he
  have hcast : ((d - 1 - j.val : ℕ) : ZMod d) = -j - 1 := by linear_combination he
  rw [← hcast, ZMod.val_natCast_of_lt (by omega)]

/-- Conjugacy with exactly the first staggered family of adjacent swaps. -/
theorem sourceRelabel_conjugates_x (j : ZMod d) :
    modularSourceEquiv d (-j) = staggeredX d (modularSourceEquiv d j) := by
  apply Fin.ext
  have hj := j.val_lt
  simp only [staggeredX_val, modularSourceEquiv_val, source_neg_val]
  split_ifs <;> omega

/-- Conjugacy with exactly the second staggered family of adjacent swaps. -/
theorem sourceRelabel_conjugates_y (j : ZMod d) :
    modularSourceEquiv d (-j - 1) = staggeredY d (modularSourceEquiv d j) := by
  apply Fin.ext
  have hj := j.val_lt
  simp only [staggeredY_val, modularSourceEquiv_val, source_neg_sub_one_val]
  split_ifs <;> omega

/-- The alternating word beginning with `y`, with exactly the given length. -/
def sourceAlternatingWord : ℕ → FreeGroup (Fin 2)
  | 0 => 1
  | i + 1 => sourceAlternatingWord i * (if i % 2 = 0 then freeY else freeX)

/-- Reading the alternating word follows the consecutive source vertices. -/
theorem sourceAlternatingWord_vertex (i : ℕ) (hi : i < d) :
    modularSourceEquiv d (modularRightAction d 0 (sourceAlternatingWord i)) = ⟨i, hi⟩ := by
  induction i with
  | zero =>
    apply Fin.ext
    simp [sourceAlternatingWord, modularSourceEquiv_val, Nat.pos_of_ne_zero (NeZero.ne d)]
  | succ i ih =>
    have hi' : i < d := by omega
    simp only [sourceAlternatingWord, modularRightAction_mul]
    by_cases he : i % 2 = 0
    · simp only [he, ite_true]
      rw [modularRightAction_y, sourceRelabel_conjugates_y, ih hi']
      apply Fin.ext
      rw [staggeredY_val]
      dsimp
      split_ifs <;> omega
    · simp only [he, ite_false]
      rw [modularRightAction_x, sourceRelabel_conjugates_x, ih hi']
      apply Fin.ext
      rw [staggeredX_val]
      dsimp
      split_ifs
      omega

/-- A precise state, hence right-coset, interpretation of the paper's alternating words. -/
theorem sourceAlternatingWord_state (i : Fin d) :
    modularRightAction d 0 (sourceAlternatingWord i.val) = (modularSourceEquiv d).symm i := by
  apply (modularSourceEquiv d).injective
  rw [(modularSourceEquiv d).apply_symm_apply]
  exact sourceAlternatingWord_vertex d i.val i.isLt

end FnZPositiveCones
