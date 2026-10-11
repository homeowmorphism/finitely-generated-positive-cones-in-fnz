module

public import FnZPositiveCones.Cone.Basic

@[expose] public section

/-! Central extensions by normalized integer cocycles, with their strict cones.
This supplies algebra for the circular-order lifting problem, not its topological solution. -/
namespace FnZPositiveCones

universe u

/-- A normalized integer two-cocycle with trivial coefficient action. -/
structure NormalizedIntCocycle (G : Type u) [Group G] where
  value : G → G → ℤ
  one_left : ∀ g, value 1 g = 0
  one_right : ∀ g, value g 1 = 0
  cocycle : ∀ g h k, value g h + value (g * h) k = value h k + value g (h * k)

namespace NormalizedIntCocycle
variable {G : Type u} [Group G] (c : NormalizedIntCocycle G)

theorem inverse_symmetry (g : G) : c.value g g⁻¹ = c.value g⁻¹ g := by
  simpa only [mul_inv_cancel, inv_mul_cancel, c.one_left, c.one_right, add_zero,
    zero_add] using c.cocycle g g⁻¹ g

/-- The carrier of the central extension; multiplication includes the cocycle. -/
@[ext] structure Extension (c : NormalizedIntCocycle G) where
  base : G
  height : ℤ

instance : Group c.Extension where
  one := ⟨1, 0⟩
  mul x y := ⟨x.base * y.base, x.height + y.height + c.value x.base y.base⟩
  inv x := ⟨x.base⁻¹, -x.height - c.value x.base⁻¹ x.base⟩
  one_mul x := by
    apply Extension.ext
    · exact one_mul x.base
    · change 0 + x.height + c.value 1 x.base = x.height
      simp [c.one_left]
  mul_one x := by
    apply Extension.ext
    · exact mul_one x.base
    · change x.height + 0 + c.value x.base 1 = x.height
      simp [c.one_right]
  mul_assoc x y z := by
    apply Extension.ext
    · exact mul_assoc _ _ _
    · change x.height + y.height + c.value x.base y.base + z.height +
        c.value (x.base * y.base) z.base =
        x.height + (y.height + z.height + c.value y.base z.base) +
          c.value x.base (y.base * z.base)
      have := c.cocycle x.base y.base z.base
      omega
  inv_mul_cancel x := by
    apply Extension.ext
    · exact inv_mul_cancel x.base
    · change -x.height - c.value x.base⁻¹ x.base + x.height + c.value x.base⁻¹ x.base = 0
      omega

@[simp] theorem base_one : (1 : c.Extension).base = 1 := rfl
@[simp] theorem height_one : (1 : c.Extension).height = 0 := rfl
@[simp] theorem base_mul (x y : c.Extension) : (x * y).base = x.base * y.base := rfl
@[simp] theorem height_mul (x y : c.Extension) :
    (x * y).height = x.height + y.height + c.value x.base y.base := rfl
@[simp] theorem base_inv (x : c.Extension) : x⁻¹.base = x.base⁻¹ := rfl
@[simp] theorem height_inv (x : c.Extension) :
    x⁻¹.height = -x.height - c.value x.base⁻¹ x.base := rfl

def projection : c.Extension →* G where
  toFun := Extension.base
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The central copy of the integer group. -/
def central : Multiplicative ℤ →* c.Extension where
  toFun m := ⟨1, m.toAdd⟩
  map_one' := rfl
  map_mul' m n := by ext <;> simp [c.one_left]

theorem central_commute (m : Multiplicative ℤ) (x : c.Extension) :
    Commute (c.central m) x := by
  show c.central m * x = x * c.central m
  ext <;> simp [central, c.one_left, c.one_right, add_comm]

def IsCircular : Prop :=
  (∀ g h, 0 ≤ c.value g h ∧ c.value g h ≤ 1) ∧
    ∀ g, g ≠ 1 → c.value g g⁻¹ = 1

/-- The standard positive semigroup in a circular cocycle's extension. -/
def positive (hc : c.IsCircular) : Subsemigroup c.Extension where
  carrier := {x | 0 < x.height ∨ (x.height = 0 ∧ x.base ≠ 1)}
  mul_mem' := by
    intro x y hx hy
    change 0 < (x * y).height ∨ ((x * y).height = 0 ∧ (x * y).base ≠ 1)
    have hnonneg := (hc.1 x.base y.base).1
    rcases hx with hx | ⟨hx, hxb⟩ <;> rcases hy with hy | ⟨hy, hyb⟩
    · left; simp only [height_mul]; omega
    · left; simp only [height_mul]; omega
    · left; simp only [height_mul]; omega
    · by_cases hxy : x.base * y.base = 1
      · have he : y.base = x.base⁻¹ := eq_inv_of_mul_eq_one_right hxy
        have hval := hc.2 x.base hxb
        left
        simp only [height_mul, hx, hy, he, hval]
        omega
      · by_cases hzero : c.value x.base y.base = 0
        · right; exact ⟨by simp [hx, hy, hzero], hxy⟩
        · left; simp only [height_mul]; omega

theorem positive_isPositiveCone (hc : c.IsCircular) : IsPositiveCone (c.positive hc) := by
  constructor
  · change ¬(0 < (0 : ℤ) ∨ ((0 : ℤ) = 0 ∧ (1 : G) ≠ 1))
    simp
  · intro x
    change x = 1 ∨ (0 < x.height ∨ (x.height = 0 ∧ x.base ≠ 1)) ∨
      (0 < x⁻¹.height ∨ (x⁻¹.height = 0 ∧ x⁻¹.base ≠ 1))
    by_cases hpos : 0 < x.height
    · exact Or.inr (Or.inl (Or.inl hpos))
    by_cases hzero : x.height = 0
    · by_cases hb : x.base = 1
      · left; ext <;> assumption
      · exact Or.inr (Or.inl (Or.inr ⟨hzero, hb⟩))
    · right; right
      have hrange := hc.1 x.base⁻¹ x.base
      by_cases hb : x.base = 1
      · left; simp only [height_inv, hb, inv_one, c.one_left]; omega
      · by_cases hneg : 0 < -x.height - c.value x.base⁻¹ x.base
        · exact Or.inl hneg
        · right
          exact ⟨by simp only [height_inv]; omega, by simpa only [base_inv, inv_ne_one]⟩

section FreeGroup
variable {ι : Type u} (c : NormalizedIntCocycle (FreeGroup ι))

/-- Freeness selects a homomorphic section with any prescribed integer generator heights. -/
def freeSection (t : ι → ℤ) : FreeGroup ι →* c.Extension :=
  FreeGroup.lift (fun i => ⟨FreeGroup.of i, t i⟩)

theorem projection_comp_freeSection (t : ι → ℤ) :
    c.projection.comp (c.freeSection t) = MonoidHom.id (FreeGroup ι) := by
  apply FreeGroup.ext_hom
  intro i
  simp [freeSection, projection]

@[simp] theorem freeSection_base (t : ι → ℤ) (g : FreeGroup ι) :
    (c.freeSection t g).base = g :=
  DFunLike.congr_fun (c.projection_comp_freeSection t) g

/-- Splitting the cocycle extension over a free group. -/
def freeProductHom (t : ι → ℤ) : FreeGroup ι × Multiplicative ℤ →* c.Extension :=
  (c.freeSection t).noncommCoprod c.central (fun _ m => (c.central_commute m _).symm)

@[simp] theorem freeProductHom_base (t : ι → ℤ) (x : FreeGroup ι × Multiplicative ℤ) :
    (c.freeProductHom t x).base = x.1 := by
  change ((c.freeSection t x.1) * (c.central x.2)).base = x.1
  simp [central]

@[simp] theorem freeProductHom_height (t : ι → ℤ) (x : FreeGroup ι × Multiplicative ℤ) :
    (c.freeProductHom t x).height = (c.freeSection t x.1).height + x.2.toAdd := by
  change ((c.freeSection t x.1) * (c.central x.2)).height = _
  simp [central, c.one_right]

/-- Explicit inverse: subtract the height of the chosen free section. -/
def freeProductInverse (t : ι → ℤ) (x : c.Extension) : FreeGroup ι × Multiplicative ℤ :=
  (x.base, Multiplicative.ofAdd (x.height - (c.freeSection t x.base).height))

theorem freeProductInverse_left (t : ι → ℤ) (x : FreeGroup ι × Multiplicative ℤ) :
    c.freeProductInverse t (c.freeProductHom t x) = x := by
  apply Prod.ext
  · exact c.freeProductHom_base t x
  · change (c.freeProductHom t x).height - (c.freeSection t (c.freeProductHom t x).base).height = x.2.toAdd
    simp

theorem freeProductInverse_right (t : ι → ℤ) (x : c.Extension) :
    c.freeProductHom t (c.freeProductInverse t x) = x := by
  apply Extension.ext
  · simp [freeProductInverse]
  · simp [freeProductInverse]

/-- A marked product equivalence, constructed together with its inverse. -/
def freeProductEquiv (t : ι → ℤ) : FreeGroup ι × Multiplicative ℤ ≃* c.Extension where
  toFun := c.freeProductHom t
  invFun := c.freeProductInverse t
  left_inv := c.freeProductInverse_left t
  right_inv := c.freeProductInverse_right t
  map_mul' := (c.freeProductHom t).map_mul

/-- Pulling the exact extension cone back along the checked free splitting. -/
def freeProductPositive (t : ι → ℤ) (hc : c.IsCircular) :
    Subsemigroup (FreeGroup ι × Multiplicative ℤ) :=
  Subsemigroup.comap (c.freeProductHom t).toMulHom (c.positive hc)

theorem freeProductPositive_isPositiveCone (t : ι → ℤ) (hc : c.IsCircular) :
    IsPositiveCone (c.freeProductPositive t hc) := by
  refine ⟨?_, ?_⟩
  · change c.freeProductHom t 1 ∉ c.positive hc
    simpa using (c.positive_isPositiveCone hc).1
  · intro x
    obtain h | h | h := (c.positive_isPositiveCone hc).2 (c.freeProductHom t x)
    · left
      have hh : c.freeProductHom t x = c.freeProductHom t 1 := h.trans (map_one _).symm
      exact Function.LeftInverse.injective (c.freeProductInverse_left t) hh
    · exact Or.inr (Or.inl h)
    · right; right
      change c.freeProductHom t x⁻¹ ∈ c.positive hc
      simpa using h

end FreeGroup
end NormalizedIntCocycle
end FnZPositiveCones
