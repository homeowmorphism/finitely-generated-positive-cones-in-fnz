module

public import FnZPositiveCones.Gamma.Basic

@[expose] public section

/-!
# The base positive semigroup

The exclusion-of-one proof uses an explicit action on the ordered real line.
This replaces the projective ping-pong argument of Navas, Proposition 3.1,
by a piecewise linear action with the same marked generators.
-/
namespace FnZPositiveCones
namespace BaseConeAction

noncomputable section

def cell (x : ℝ) : ℝ :=
  if x ≤ 1 / 2 then 4 * x / 3 else (2 * x + 1) / 3

def invCell (x : ℝ) : ℝ :=
  if x ≤ 2 / 3 then 3 * x / 4 else (3 * x - 1) / 2

private theorem cell_range {x : ℝ} (hx : 0 ≤ x) (hx' : x < 1) :
    0 ≤ cell x ∧ cell x < 1 := by
  unfold cell
  split_ifs <;> constructor <;> linarith

private theorem invCell_range {x : ℝ} (hx : 0 ≤ x) (hx' : x < 1) :
    0 ≤ invCell x ∧ invCell x < 1 := by
  unfold invCell
  split_ifs <;> constructor <;> linarith

private theorem cell_strictMono : StrictMono cell := by
  intro x y h
  unfold cell
  split_ifs <;> linarith

private theorem invCell_cell (x : ℝ) : invCell (cell x) = x := by
  unfold invCell cell
  split_ifs <;> linarith

private theorem cell_invCell (x : ℝ) : cell (invCell x) = x := by
  unfold invCell cell
  split_ifs <;> linarith

def plMap (x : ℝ) : ℝ := ⌊x⌋ + cell (Int.fract x)
def plInv (x : ℝ) : ℝ := ⌊x⌋ + invCell (Int.fract x)

private theorem plMap_floor (x : ℝ) : ⌊plMap x⌋ = ⌊x⌋ := by
  apply Int.floor_eq_iff.mpr
  have h := cell_range (Int.fract_nonneg x) (Int.fract_lt_one x)
  unfold plMap
  constructor <;> linarith

private theorem plInv_floor (x : ℝ) : ⌊plInv x⌋ = ⌊x⌋ := by
  apply Int.floor_eq_iff.mpr
  have h := invCell_range (Int.fract_nonneg x) (Int.fract_lt_one x)
  unfold plInv
  constructor <;> linarith

private theorem plMap_fract (x : ℝ) : Int.fract (plMap x) = cell (Int.fract x) := by
  rw [Int.fract, plMap_floor, plMap]
  ring

private theorem plInv_fract (x : ℝ) : Int.fract (plInv x) = invCell (Int.fract x) := by
  rw [Int.fract, plInv_floor, plInv]
  ring

private theorem plInv_plMap (x : ℝ) : plInv (plMap x) = x := by
  rw [plInv, plMap_floor, plMap_fract, invCell_cell, Int.floor_add_fract]

private theorem plMap_plInv (x : ℝ) : plMap (plInv x) = x := by
  rw [plMap, plInv_floor, plInv_fract, cell_invCell, Int.floor_add_fract]

private theorem plMap_strictMono : StrictMono plMap := by
  intro x y hxy
  have hf : ⌊x⌋ ≤ ⌊y⌋ := Int.floor_mono hxy.le
  rcases eq_or_lt_of_le hf with he | hl
  · have : Int.fract x < Int.fract y := by unfold Int.fract; rw [he]; linarith
    have := cell_strictMono this
    unfold plMap
    rw [he]
    linarith
  · have hx := cell_range (Int.fract_nonneg x) (Int.fract_lt_one x)
    have hy := cell_range (Int.fract_nonneg y) (Int.fract_lt_one y)
    have hcast : (⌊x⌋ : ℝ) + 1 ≤ ⌊y⌋ := by exact_mod_cast hl
    unfold plMap
    linarith

/-- An explicit increasing period-one piecewise linear reparametrization. -/
noncomputable def reparam : ℝ ≃o ℝ where
  toFun := plMap
  invFun := plInv
  left_inv := by exact plInv_plMap
  right_inv := by exact plMap_plInv
  map_rel_iff' := by exact plMap_strictMono.le_iff_le

@[simp] theorem reparam_inv_apply (x : ℝ) : reparam⁻¹ (reparam x) = x :=
  plInv_plMap x

@[simp] theorem reparam_apply_inv (x : ℝ) : reparam (reparam⁻¹ x) = x :=
  plMap_plInv x

private theorem plMap_add_one (x : ℝ) : plMap (x + 1) = plMap x + 1 := by
  simp only [plMap, Int.floor_add_one, Int.fract_add_one, Int.cast_add, Int.cast_one]
  ring

@[simp] theorem reparam_add_one (x : ℝ) : reparam (x + 1) = reparam x + 1 :=
  plMap_add_one x

private theorem plMap_zero : plMap 0 = 0 := by norm_num [plMap, cell, Int.fract]
private theorem plMap_quarter : plMap (1 / 4) = 1 / 3 := by
  norm_num [plMap, cell, Int.fract]
private theorem plMap_neg_half : plMap (-(1 / 2)) = -(1 / 3) := by
  norm_num [plMap, cell, Int.fract]
private theorem plMap_neg_quarter : plMap (-(1 / 4)) = -(1 / 6) := by
  norm_num [plMap, cell, Int.fract]

/-- Translation by `t`, viewed as an order automorphism. -/
noncomputable def translation (t : ℝ) : ℝ ≃o ℝ where
  toFun := fun x => x + t
  invFun := fun x => x - t
  left_inv := by intro x; dsimp; ring
  right_inv := by intro x; dsimp; ring
  map_rel_iff' := by intro x y; exact add_le_add_iff_right t

@[simp] theorem translation_apply (t x : ℝ) : translation t x = x + t := rfl
@[simp] theorem translation_inv_apply (t x : ℝ) : (translation t)⁻¹ x = x - t := rfl

noncomputable def a : ℝ ≃o ℝ := translation (1 / 3)
noncomputable def h : ℝ ≃o ℝ := reparam * translation (1 / 2) * reparam⁻¹
noncomputable def b : ℝ ≃o ℝ := a * h⁻¹

@[simp] theorem a_apply (x : ℝ) : a x = x + 1 / 3 := rfl

theorem h_square : h ^ 2 = a ^ 3 := by
  ext x
  change reparam (reparam⁻¹ (reparam (reparam⁻¹ x + 1 / 2)) + 1 / 2) =
    ((x + 1 / 3) + 1 / 3) + 1 / 3
  simp only [reparam_inv_apply]
  rw [show reparam⁻¹ x + 1 / 2 + 1 / 2 = reparam⁻¹ x + 1 by ring,
    reparam_add_one, reparam_apply_inv]
  ring

theorem relation : b * a ^ 2 * b = a := by
  calc
    _ = a * h⁻¹ * a ^ 3 * h⁻¹ := by unfold b; group
    _ = a := by rw [← h_square]; group

@[simp] theorem b_zero : b 0 = 0 := by
  change reparam (reparam⁻¹ 0 - 1 / 2) + 1 / 3 = 0
  have h0 : reparam⁻¹ 0 = 0 := by
    apply reparam.injective
    rw [reparam_apply_inv]
    exact plMap_zero.symm
  rw [h0]
  change plMap (0 - 1 / 2) + 1 / 3 = 0
  rw [zero_sub, plMap_neg_half]
  ring

@[simp] theorem b_third : b (1 / 3) = 1 / 6 := by
  change reparam (reparam⁻¹ (1 / 3) - 1 / 2) + 1 / 3 = 1 / 6
  have hq : reparam⁻¹ (1 / 3) = 1 / 4 := by
    apply reparam.injective
    rw [reparam_apply_inv]
    exact plMap_quarter.symm
  rw [hq]
  change plMap (1 / 4 - 1 / 2) + 1 / 3 = 1 / 6
  rw [show (1 / 4 - 1 / 2 : ℝ) = -(1 / 4) by ring, plMap_neg_quarter]
  ring


def generator : GammaLetter → (ℝ ≃o ℝ)
  | .a => a
  | .b => b

 theorem generator_relations (r : FreeGroup GammaLetter) (hr : r ∈ gammaRelations) :
    FreeGroup.lift generator r = 1 := by
  have hr' : r = gammaRelator := by simpa [gammaRelations] using hr
  subst r
  simp only [gammaRelator, map_mul, map_pow, map_inv, FreeGroup.lift_apply_of, generator]
  rw [relation, mul_inv_cancel]

/-- The explicitly checked marked action; injectivity is not required. -/
def representation : Gamma2 →* (ℝ ≃o ℝ) :=
  PresentedGroup.toGroup generator_relations

@[simp] theorem representation_a : representation aGamma = a :=
  PresentedGroup.toGroup.of _

@[simp] theorem representation_b : representation bGamma = b :=
  PresentedGroup.toGroup.of _

/-- Every positive word moves zero right, or fixes zero and moves one third left. -/
def Moves (f : ℝ ≃o ℝ) : Prop :=
  0 < f 0 ∨ (f 0 = 0 ∧ f (1 / 3) < 1 / 3)

 theorem moves_mul {f g : ℝ ≃o ℝ} (hf : Moves f) (hg : Moves g) : Moves (f * g) := by
  change 0 < f (g 0) ∨ (f (g 0) = 0 ∧ f (g (1 / 3)) < 1 / 3)
  rcases hf with hf | ⟨hf0, hf1⟩
  · left
    have hg0 : 0 ≤ g 0 := by rcases hg with h | ⟨h, _⟩ <;> linarith
    exact hf.trans_le (f.monotone hg0)
  · rcases hg with hg | ⟨hg0, hg1⟩
    · left
      simpa only [hf0] using f.strictMono hg
    · right
      constructor
      · rw [hg0, hf0]
      · exact (f.strictMono hg1).trans hf1

 theorem moves_a : Moves a := by left; norm_num
 theorem moves_b : Moves b := by right; constructor; exact b_zero; rw [b_third]; norm_num
 theorem not_moves_one : ¬ Moves (1 : ℝ ≃o ℝ) := by
  change ¬ ((0 : ℝ) < 0 ∨ ((0 : ℝ) = 0 ∧ (1 / 3 : ℝ) < 1 / 3))
  simp

 theorem positive_moves {g : Gamma2} (hg : g ∈ basePositiveClosure) :
    Moves (representation g) := by
  induction hg using Subsemigroup.closure_induction with
  | mem x hx =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · rw [representation_a]; exact moves_a
    · rw [representation_b]; exact moves_b
  | mul x y hx hy ihx ihy =>
    rw [map_mul]
    exact moves_mul ihx ihy

end
end BaseConeAction

/-- E00: exclusion of identity for the exact semigroup generated by a and b. -/
theorem baseOneNotMem : BaseOneNotMemGoal := by
  intro h
  have := BaseConeAction.positive_moves h
  rw [map_one] at this
  exact BaseConeAction.not_moves_one this

theorem base_one_not_mem : BaseOneNotMemGoal := baseOneNotMem

namespace BaseConeNormalForm

local notation "a" => aGamma
local notation "b" => bGamma
local notation "z" => aGamma ^ (3 : ℕ)

def letter : GammaLetter → Gamma2
  | .a => a
  | .b => b

def word (w : List GammaLetter) : Gamma2 := (w.map letter).prod

def middleLetter (c : Bool) : Gamma2 := if c then a * b else b

def middle (w : List Bool) : Gamma2 := (w.map middleLetter).prod

@[simp] theorem word_nil : word [] = 1 := rfl
@[simp] theorem word_append (u v : List GammaLetter) : word (u ++ v) = word u * word v := by
  simp [word]
@[simp] theorem word_singleton (c : GammaLetter) : word [c] = letter c := by simp [word]
@[simp] theorem middle_nil : middle [] = 1 := rfl
@[simp] theorem middle_append (u v : List Bool) : middle (u ++ v) = middle u * middle v := by
  simp [middle]
@[simp] theorem middle_singleton (c : Bool) : middle [c] = middleLetter c := by simp [middle]

/-- Positive words with neither an `aaa` block nor a `baab` block. -/
inductive Reduced : Gamma2 → Prop
  | pure (i : Fin 3) : Reduced (a ^ (i : ℕ))
  | mixed (i j : Fin 3) (v : List Bool) : Reduced (a ^ (i : ℕ) * b * middle v * a ^ (j : ℕ))

 theorem z_commute (g : Gamma2) : Commute z g := gamma_a_cube_commute g

 theorem reduced_mul_a {u : Gamma2} (hu : Reduced u) :
    ∃ v : Gamma2, ∃ k : ℕ, Reduced v ∧ u * a = v * z ^ k := by
  cases hu with
  | pure i =>
    fin_cases i
    · exact ⟨a, 0, by simpa using Reduced.pure 1, by simp⟩
    · exact ⟨a ^ 2, 0, Reduced.pure 2, by simp [pow_two]⟩
    · exact ⟨1, 1, by simpa using Reduced.pure 0, by simp [pow_succ]⟩
  | mixed i j v =>
    fin_cases j
    · refine ⟨a ^ (i : ℕ) * b * middle v * a, 0, ?_, ?_⟩
      · simpa using Reduced.mixed i 1 v
      · simp
    · refine ⟨a ^ (i : ℕ) * b * middle v * a ^ 2, 0, Reduced.mixed i 2 v, ?_⟩
      simp [pow_two, mul_assoc]
    · refine ⟨a ^ (i : ℕ) * b * middle v, 1, ?_, ?_⟩
      · simpa using Reduced.mixed i 0 v
      · simp [pow_succ, mul_assoc]

 theorem reduced_mul_b {u : Gamma2} (hu : Reduced u) :
    ∃ v : Gamma2, ∃ k : ℕ, Reduced v ∧ u * b = v * z ^ k := by
  cases hu with
  | pure i =>
    refine ⟨a ^ (i : ℕ) * b, 0, ?_, by simp⟩
    simpa using Reduced.mixed i 0 []
  | mixed i j v =>
    fin_cases j
    · refine ⟨a ^ (i : ℕ) * b * middle (v ++ [false]), 0, ?_, ?_⟩
      · simpa using Reduced.mixed i 0 (v ++ [false])
      · simp [middleLetter, mul_assoc]
    · refine ⟨a ^ (i : ℕ) * b * middle (v ++ [true]), 0, ?_, ?_⟩
      · simpa using Reduced.mixed i 0 (v ++ [true])
      · simp [middleLetter, mul_assoc]
    · induction v using List.reverseRecOn with
      | nil =>
        simp only [middle_nil, mul_one]
        have hr : a ^ (i : ℕ) * b * a ^ 2 * b = a ^ (i : ℕ) * a := by
          rw [mul_assoc, mul_assoc, ← mul_assoc b, gamma_relation]
        rw [hr]
        exact reduced_mul_a (Reduced.pure i)
      | append_singleton v c _ =>
        cases c
        · refine ⟨a ^ (i : ℕ) * b * middle v * a, 0, ?_, ?_⟩
          · simpa using Reduced.mixed i 1 v
          · simp only [middle_append, middle_singleton, middleLetter, Bool.false_eq_true,
              ↓reduceIte, pow_zero, mul_one]
            calc
              _ = a ^ (i : ℕ) * b * middle v * (b * a ^ 2 * b) := by group
              _ = _ := by rw [gamma_relation]
        · refine ⟨a ^ (i : ℕ) * b * middle v * a ^ 2, 0, Reduced.mixed i 2 v, ?_⟩
          simp only [middle_append, middle_singleton, middleLetter, ↓reduceIte,
            pow_zero, mul_one]
          calc
            _ = a ^ (i : ℕ) * b * middle v * a * (b * a ^ 2 * b) := by group
            _ = _ := by rw [gamma_relation]; simp [pow_two, mul_assoc]

 theorem normalize_word (w : List GammaLetter) :
    ∃ u : Gamma2, ∃ k : ℕ, Reduced u ∧ word w = u * z ^ k := by
  induction w using List.reverseRecOn with
  | nil => exact ⟨1, 0, by simpa using Reduced.pure 0, by simp⟩
  | append_singleton w c ih =>
    obtain ⟨u, k, hu, he⟩ := ih
    have hc : ∃ v : Gamma2, ∃ j : ℕ, Reduced v ∧ u * letter c = v * z ^ j := by
      cases c
      · exact reduced_mul_a hu
      · exact reduced_mul_b hu
    obtain ⟨v, j, hv, hj⟩ := hc
    refine ⟨v, j + k, hv, ?_⟩
    rw [word_append, word_singleton, he]
    calc
      u * z ^ k * letter c = u * letter c * z ^ k := by
        rw [mul_assoc, (z_commute (letter c)).pow_left k |>.eq, ← mul_assoc]
      _ = v * z ^ (j + k) := by rw [hj, pow_add, mul_assoc]

 theorem inverse_a_fraction : a⁻¹ = word [.a, .a] * z ^ (-1 : ℤ) := by
  simp [word, letter]
  group

 theorem inverse_b_fraction : b⁻¹ = word [.a, .a, .b, .a, .a] * z ^ (-1 : ℤ) := by
  calc
    b⁻¹ = a ^ 2 * b * a⁻¹ := by rw [← gamma_inverse_mul_a]; group
    _ = word [.a, .a, .b, .a, .a] * z ^ (-1 : ℤ) := by
      simp [word, letter, pow_two]
      group

/-- Navas Proposition 1.1, proved directly in the supplied presentation. -/
 theorem positive_fraction (g : Gamma2) :
    ∃ w : List GammaLetter, ∃ k : ℤ, g = word w * z ^ k := by
  obtain ⟨g, rfl⟩ := PresentedGroup.mk_surjective gammaRelations g
  induction g using FreeGroup.induction_on with
  | one => exact ⟨[], 0, by simp⟩
  | of c => exact ⟨[c], 0, by cases c <;> simp [letter, aGamma, bGamma, PresentedGroup.of]⟩
  | inv_of c _ =>
    cases c
    · exact ⟨[.a, .a], -1, by simpa [aGamma, PresentedGroup.of] using inverse_a_fraction⟩
    · exact ⟨[.a, .a, .b, .a, .a], -1,
        by simpa [bGamma, PresentedGroup.of] using inverse_b_fraction⟩
  | mul g h ihg ihh =>
    obtain ⟨w, i, hi⟩ := ihg
    obtain ⟨v, j, hj⟩ := ihh
    refine ⟨w ++ v, i + j, ?_⟩
    rw [map_mul, hi, hj, word_append, zpow_add]
    calc
      _ = word w * (z ^ i * word v) * z ^ j := by group
      _ = _ := by rw [(z_commute (word v)).zpow_left i |>.eq]; group

/-- The normal-form theorem needed for the sign decomposition. -/
 theorem reduced_fraction (g : Gamma2) :
    ∃ u : Gamma2, ∃ k : ℤ, Reduced u ∧ g = u * z ^ k := by
  obtain ⟨w, k, hk⟩ := positive_fraction g
  obtain ⟨u, j, hu, hj⟩ := normalize_word w
  refine ⟨u, (j : ℤ) + k, hu, ?_⟩
  rw [hk, hj, zpow_add, zpow_natCast, mul_assoc]

/-- A temporary monoid containing the identity and the strict positive semigroup. -/
def nonnegative : Submonoid Gamma2 where
  carrier := {g | g = 1 ∨ g ∈ basePositiveClosure}
  one_mem' := Or.inl rfl
  mul_mem' := by
    rintro x y (rfl | hx) (rfl | hy)
    · exact Or.inl (by simp)
    · exact Or.inr (by simpa using hy)
    · exact Or.inr (by simpa using hx)
    · exact Or.inr (basePositiveClosure.mul_mem hx hy)

 theorem a_nonnegative : a ∈ nonnegative := Or.inr aGamma_mem_basePositiveClosure
 theorem b_nonnegative : b ∈ nonnegative := Or.inr bGamma_mem_basePositiveClosure
 theorem z_nonnegative : z ∈ nonnegative := nonnegative.pow_mem a_nonnegative 3

 theorem middle_nonnegative (v : List Bool) : middle v ∈ nonnegative := by
  induction v with
  | nil => exact nonnegative.one_mem
  | cons c v ih =>
    change middleLetter c * middle v ∈ nonnegative
    apply nonnegative.mul_mem _ ih
    cases c
    · exact b_nonnegative
    · exact nonnegative.mul_mem a_nonnegative b_nonnegative

 theorem reduced_nonnegative {u : Gamma2} (hu : Reduced u) : u ∈ nonnegative := by
  cases hu with
  | pure i => exact nonnegative.pow_mem a_nonnegative i
  | mixed i j v =>
    exact nonnegative.mul_mem
      (nonnegative.mul_mem
        (nonnegative.mul_mem (nonnegative.pow_mem a_nonnegative i) b_nonnegative)
        (middle_nonnegative v)) (nonnegative.pow_mem a_nonnegative j)

 theorem inverse_middle_conjugate (v : List Bool) :
    a * (middle v)⁻¹ * a⁻¹ ∈ nonnegative := by
  induction v with
  | nil => simp
  | cons c v ih =>
    have hh : a * (middleLetter c)⁻¹ * a⁻¹ ∈ nonnegative := by
      cases c
      · change a * b⁻¹ * a⁻¹ ∈ nonnegative
        rw [gamma_a_mul_inverse]
        convert nonnegative.mul_mem b_nonnegative a_nonnegative using 1
        group
      · change a * (a * b)⁻¹ * a⁻¹ ∈ nonnegative
        have he : a * (a * b)⁻¹ * a⁻¹ = b := by
          calc
            _ = (a * b⁻¹) * a⁻¹ * a⁻¹ := by group
            _ = b := by rw [gamma_a_mul_inverse]; group
        rw [he]
        exact b_nonnegative
    have he : a * (middle (c :: v))⁻¹ * a⁻¹ =
        (a * (middle v)⁻¹ * a⁻¹) * (a * (middleLetter c)⁻¹ * a⁻¹) := by
      change a * (middleLetter c * middle v)⁻¹ * a⁻¹ = _
      group
    rw [he]
    exact nonnegative.mul_mem ih hh

 theorem mixed_complement_formula (i j : ℤ) (v : Gamma2) :
    z * (a ^ i * b * v * a ^ j)⁻¹ =
      a ^ (2 - j) * (a * v⁻¹ * a⁻¹) * b * a ^ (2 - i) := by
  have hh : a⁻¹ * b * a ^ 2 = b⁻¹ := by
    rw [mul_assoc, ← gamma_a_mul_inverse]
    group
  calc
    _ = a ^ (3 - j) * v⁻¹ * b⁻¹ * a ^ (-i) := by group
    _ = _ := by rw [← hh]; group

/-- Every reduced positive word lies below one central positive step. -/
 theorem reduced_complement_nonnegative {u : Gamma2} (hu : Reduced u) :
    z * u⁻¹ ∈ nonnegative := by
  cases hu with
  | pure i =>
    fin_cases i
    · simpa using z_nonnegative
    · convert nonnegative.pow_mem a_nonnegative 2 using 1
      group
    · convert a_nonnegative using 1
      group
  | mixed i j v =>
    have hi : ((2 - (i : ℕ) : ℕ) : ℤ) = 2 - (i : ℤ) := by
      rw [Int.natCast_sub (by omega)]; norm_num
    have hj : ((2 - (j : ℕ) : ℕ) : ℤ) = 2 - (j : ℤ) := by
      rw [Int.natCast_sub (by omega)]; norm_num
    have he := mixed_complement_formula (i : ℤ) (j : ℤ) (middle v)
    rw [← hi, ← hj] at he
    simp only [zpow_natCast] at he
    rw [he]
    exact nonnegative.mul_mem
      (nonnegative.mul_mem
        (nonnegative.mul_mem (nonnegative.pow_mem a_nonnegative (2 - j))
          (inverse_middle_conjugate v)) b_nonnegative)
      (nonnegative.pow_mem a_nonnegative (2 - i))

 theorem total (g : Gamma2) : g = 1 ∨ g ∈ basePositiveClosure ∨ g⁻¹ ∈ basePositiveClosure := by
  obtain ⟨u, k, hu, rfl⟩ := reduced_fraction g
  cases k with
  | ofNat k =>
    have h : u * z ^ k ∈ nonnegative :=
      nonnegative.mul_mem (reduced_nonnegative hu) (nonnegative.pow_mem z_nonnegative k)
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  | negSucc k =>
    have he : (u * z ^ (Int.negSucc k))⁻¹ = z ^ k * (z * u⁻¹) := by
      rw [Int.negSucc_eq]
      group
    have h : (u * z ^ (Int.negSucc k))⁻¹ ∈ nonnegative := by
      rw [he]
      exact nonnegative.mul_mem (nonnegative.pow_mem z_nonnegative k)
        (reduced_complement_nonnegative hu)
    rcases h with h | h
    · exact Or.inl (inv_eq_one.mp h)
    · exact Or.inr (Or.inr h)

end BaseConeNormalForm

/-- E01: totality for the exact semigroup generated by the marked a and b. -/
theorem baseTotal : BaseTotalGoal := BaseConeNormalForm.total

theorem base_total : BaseTotalGoal := baseTotal

/-- E02: the Dubrovina–Dubrovin/Navas positive cone in the supplied presentation. -/
theorem baseCone : BaseConeGoal := ⟨baseOneNotMem, baseTotal⟩

theorem base_positive_cone : BaseConeGoal := baseCone

end FnZPositiveCones
