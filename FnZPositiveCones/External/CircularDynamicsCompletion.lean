module

public import FnZPositiveCones.External.CircularDynamics
public import FnZPositiveCones.External.CofinalCocycle

@[expose] public section

/-! Order completion of circular actions using the actual orbit carry cocycle. -/
namespace FnZPositiveCones
namespace CircularDynamics
attribute [local instance] Classical.propDecidable
universe u v
variable {G : Type u} [Group G] {X : Type v} [CircularOrder X]

/-- Circular permutations preserve the integer carry, including degenerate triples. -/
theorem carry_perm (e : Equiv.Perm X) (he : PreservesCircular e) (a b c : X) :
    CircularCarry.value (e a) (e b) (e c) = CircularCarry.value a b c := by
  classical
  have hs : sbtw (e a) (e b) (e c) ↔ sbtw a b c := by
    rw [sbtw_iff_btw_not_btw, sbtw_iff_btw_not_btw, he, he]
  simp only [CircularCarry.value, e.injective.eq_iff, hs]

variable (ρ : G →* Equiv.Perm X) (hρ : ∀ g, PreservesCircular (ρ g)) (x : X)

/-- The orbit carry remains a normalized cocycle even when the base orbit is not free. -/
noncomputable def orbitCocycle : NormalizedIntCocycle G where
  value g h := CircularCarry.value x (ρ g x) (ρ (g * h) x)
  one_left g := by simp
  one_right g := by simp
  cocycle g h k := by
    have ht := CircularCarry.fourpoint x (ρ g x) (ρ (g * h) x) (ρ (g * h * k) x)
    have he : CircularCarry.value (ρ g x) (ρ (g * h) x) (ρ (g * h * k) x) =
        CircularCarry.value x (ρ h x) (ρ (h * k) x) := by
      simpa only [map_mul, mul_assoc, Equiv.Perm.mul_apply] using
        carry_perm (ρ g) (hρ g) x (ρ h x) (ρ (h * k) x)
    rw [he, mul_assoc] at ht
    simpa only [mul_assoc] using ht

theorem orbitCocycle_range (g h : G) :
    0 ≤ (orbitCocycle ρ hρ x).value g h ∧ (orbitCocycle ρ hρ x).value g h ≤ 1 :=
  CircularCarry.value_nonneg_le_one _ _ _

theorem orbitCocycle_inverse (g : G) :
    (orbitCocycle ρ hρ x).value g g⁻¹ = if ρ g x = x then 0 else 1 := by
  classical
  change CircularCarry.value x (ρ g x) (ρ (g * g⁻¹) x) = _
  simp only [mul_inv_cancel, map_one, Equiv.Perm.one_apply]
  by_cases hg : ρ g x = x
  · simp [hg]
  · exact (CircularCarry.value_return (Ne.symm hg)).trans (ite_eq_right hg).symm

theorem orbitCocycle_inverse_rev (g : G) :
    (orbitCocycle ρ hρ x).value g⁻¹ g = if ρ g x = x then 0 else 1 := by
  rw [← NormalizedIntCocycle.inverse_symmetry, orbitCocycle_inverse]

/-- A zero carry returning to the basepoint forces both steps to stabilize it. -/
theorem orbitCocycle_zero_return (g h : G)
    (hzero : (orbitCocycle ρ hρ x).value g h = 0) (hret : ρ (g * h) x = x) :
    ρ g x = x ∧ ρ h x = x := by
  have hg : ρ g x = x := by
    by_contra hg
    have he : (orbitCocycle ρ hρ x).value g h = 1 := by
      change CircularCarry.value x (ρ g x) (ρ (g * h) x) = 1
      rw [hret]
      exact CircularCarry.value_return (Ne.symm hg)
    omega
  refine ⟨hg, (ρ g).injective ?_⟩
  simpa only [map_mul, Equiv.Perm.mul_apply, hg] using hret

variable (L : LeftGroupOrder G)

/-- Resolve the stabilizer fiber by a genuine left order. -/
def completedOrbitPositive : Subsemigroup (orbitCocycle ρ hρ x).Extension where
  carrier := {p | 0 < p.height ∨ (p.height = 0 ∧ (ρ p.base x ≠ x ∨ L.order.lt 1 p.base))}
  mul_mem' := by
    intro p q hp hq
    change 0 < (p * q).height ∨ ((p * q).height = 0 ∧
      (ρ (p * q).base x ≠ x ∨ L.order.lt 1 (p * q).base))
    have hrange := orbitCocycle_range ρ hρ x p.base q.base
    have hp0 : 0 ≤ p.height := by rcases hp with hp | ⟨hp, _⟩ <;> omega
    have hq0 : 0 ≤ q.height := by rcases hq with hq | ⟨hq, _⟩ <;> omega
    by_cases ht : 0 < (p * q).height
    · exact Or.inl ht
    have hpz : p.height = 0 := by simp only [NormalizedIntCocycle.height_mul] at ht; omega
    have hqz : q.height = 0 := by simp only [NormalizedIntCocycle.height_mul] at ht; omega
    have hcz : (orbitCocycle ρ hρ x).value p.base q.base = 0 := by
      simp only [NormalizedIntCocycle.height_mul] at ht; omega
    refine Or.inr ⟨by simp [hpz, hqz, hcz], ?_⟩
    by_cases hf : ρ (p.base * q.base) x = x
    · have hh := orbitCocycle_zero_return ρ hρ x p.base q.base hcz hf
      have hpl : L.order.lt 1 p.base := by rcases hp with hp | ⟨_, hp | hp⟩; omega; exact (hp hh.1).elim; exact hp
      have hql : L.order.lt 1 q.base := by rcases hq with hq | ⟨_, hq | hq⟩; omega; exact (hq hh.2).elim; exact hq
      right
      let := L.order
      change L.order.lt 1 (p.base * q.base)
      exact hpl.trans (by simpa only [mul_one] using L.mul_lt_mul_left p.base hql)
    · exact Or.inl hf

/-- Order completion gives an exact strict cone even when the action has stabilizers. -/
theorem completedOrbitPositive_isPositiveCone : IsPositiveCone (completedOrbitPositive ρ hρ x L) := by
  let := L.order
  constructor
  · change ¬(0 < (0 : ℤ) ∨ ((0 : ℤ) = 0 ∧ (ρ (1 : G) x ≠ x ∨ (1 : G) < 1)))
    simp
  · intro p
    change p = 1 ∨ (0 < p.height ∨ (p.height = 0 ∧ (ρ p.base x ≠ x ∨ 1 < p.base))) ∨
      (0 < p⁻¹.height ∨ (p⁻¹.height = 0 ∧ (ρ p⁻¹.base x ≠ x ∨ 1 < p⁻¹.base)))
    by_cases hp : 0 < p.height
    · exact Or.inr (Or.inl (Or.inl hp))
    by_cases hz : p.height = 0
    · by_cases hf : ρ p.base x = x
      · rcases lt_trichotomy 1 p.base with hlt | he | hgt
        · exact Or.inr (Or.inl (Or.inr ⟨hz, Or.inr hlt⟩))
        · left; ext <;> simp [he, hz]
        · right; right; right
          refine ⟨by simp [hz, orbitCocycle_inverse_rev, hf], Or.inr ?_⟩
          change L.order.lt 1 p.base⁻¹
          simpa only [inv_mul_cancel, mul_one] using L.mul_lt_mul_left p.base⁻¹ hgt
      · exact Or.inr (Or.inl (Or.inr ⟨hz, Or.inl hf⟩))
    · right; right
      have hcr := orbitCocycle_range ρ hρ x p.base⁻¹ p.base
      by_cases hf : ρ p.base x = x
      · left
        simp only [NormalizedIntCocycle.height_inv, orbitCocycle_inverse_rev, ite_eq_left hf]
        omega
      · have hfi : ρ p.base⁻¹ x ≠ x := by
          intro he
          have := congrArg (ρ p.base) he
          apply hf
          simpa using this.symm
        by_cases hneg : 0 < p⁻¹.height
        · exact Or.inl hneg
        · right
          refine ⟨?_, Or.inl hfi⟩
          simp only [NormalizedIntCocycle.height_inv] at *
          omega

section FreeGroup
variable {ι : Type u}
variable (ρ : FreeGroup ι →* Equiv.Perm X) (hρ : ∀ g, PreservesCircular (ρ g))
variable (x : X) (L : LeftGroupOrder (FreeGroup ι))

noncomputable def completionLift :
    FreeGroup ι × Multiplicative ℤ ≃* (orbitCocycle ρ hρ x).Extension :=
  (orbitCocycle ρ hρ x).freeProductEquiv (fun _ => 0)

noncomputable def completionProductPositive : Subsemigroup (FreeGroup ι × Multiplicative ℤ) :=
  Subsemigroup.comap (completionLift ρ hρ x).toMulHom (completedOrbitPositive ρ hρ x L)

theorem completionProductPositive_isPositiveCone :
    IsPositiveCone (completionProductPositive ρ hρ x L) := by
  refine ⟨?_, ?_⟩
  · change completionLift ρ hρ x 1 ∉ completedOrbitPositive ρ hρ x L
    simpa using (completedOrbitPositive_isPositiveCone ρ hρ x L).1
  · intro p
    obtain h | h | h := (completedOrbitPositive_isPositiveCone ρ hρ x L).2 (completionLift ρ hρ x p)
    · left
      exact (completionLift ρ hρ x).injective (by simpa using h)
    · exact Or.inr (Or.inl h)
    · right; right
      change completionLift ρ hρ x p⁻¹ ∈ completedOrbitPositive ρ hρ x L
      simpa only [map_inv] using h

/-- The actual left order completing all stabilizer fibers. -/
noncomputable def completionOrder : LeftGroupOrder (FreeGroup ι × Multiplicative ℤ) :=
  coneLeftOrder ⟨completionProductPositive ρ hρ x L, completionProductPositive_isPositiveCone ρ hρ x L⟩

theorem completionOrder_lt_iff (p q : FreeGroup ι × Multiplicative ℤ) :
    (completionOrder ρ hρ x L).order.lt p q ↔
      (completionLift ρ hρ x p)⁻¹ * completionLift ρ hρ x q ∈ completedOrbitPositive ρ hρ x L := by
  change completionLift ρ hρ x (p⁻¹ * q) ∈ completedOrbitPositive ρ hρ x L ↔ _
  rw [map_mul, map_inv]

@[simp] theorem completionLift_base (p : FreeGroup ι × Multiplicative ℤ) :
    (completionLift ρ hρ x p).base = p.1 :=
  NormalizedIntCocycle.freeProductHom_base _ _ _

@[simp] theorem completionLift_zpow (m : ℤ) :
    completionLift ρ hρ x (cofinalProductZ (FreeGroup ι) ^ m) =
      (orbitCocycle ρ hρ x).central (Multiplicative.ofAdd m) := by
  apply NormalizedIntCocycle.Extension.ext
  · simp [NormalizedIntCocycle.central, cofinalProductZ]
  · change ((orbitCocycle ρ hρ x).freeProductHom (fun _ => 0)
      (cofinalProductZ (FreeGroup ι) ^ m)).height = m
    simp [NormalizedIntCocycle.freeProductHom_height, cofinalProductZ]

/-- The central unit is strictly positive in the completed left order. -/
theorem completionOrder_center_positive :
    (completionOrder ρ hρ x L).order.lt 1 (cofinalProductZ (FreeGroup ι)) := by
  rw [completionOrder_lt_iff]
  have he := completionLift_zpow ρ hρ x 1
  simp only [zpow_one] at he
  rw [map_one, inv_one, one_mul, he]
  left
  exact zero_lt_one

/-- The central unit is cofinal, with explicit bounds read off from extension height. -/
theorem completionOrder_center_cofinal :
    (completionOrder ρ hρ x L).IsCofinal (cofinalProductZ (FreeGroup ι)) := by
  let := (completionOrder ρ hρ x L).order
  intro p
  let k := (completionLift ρ hρ x p).height
  refine ⟨k - 1, k + 2, ?_, ?_⟩
  · apply le_of_lt
    rw [completionOrder_lt_iff, completionLift_zpow]
    left
    change 0 < -(k - 1) - (orbitCocycle ρ hρ x).value (1 : FreeGroup ι)⁻¹ 1 +
      (completionLift ρ hρ x p).height +
      (orbitCocycle ρ hρ x).value (1 : FreeGroup ι)⁻¹ (completionLift ρ hρ x p).base
    simp only [inv_one, NormalizedIntCocycle.one_left]
    dsimp [k]
    omega
  · apply le_of_lt
    rw [completionOrder_lt_iff, completionLift_zpow]
    left
    change 0 < -(completionLift ρ hρ x p).height -
      (orbitCocycle ρ hρ x).value (completionLift ρ hρ x p).base⁻¹ (completionLift ρ hρ x p).base +
      (k + 2) + (orbitCocycle ρ hρ x).value (completionLift ρ hρ x p).base⁻¹ 1
    rw [NormalizedIntCocycle.one_right]
    have hr := orbitCocycle_range ρ hρ x (completionLift ρ hρ x p).base⁻¹ (completionLift ρ hρ x p).base
    dsimp [k]
    omega

/-- The circular order completing the possibly nonfree orbit. -/
noncomputable def completedCircularOrbitOrder : CircularGroupOrder (FreeGroup ι) :=
  cofinalProductCircularGroupOrder (completionOrder ρ hρ x L)
    (completionOrder_center_positive ρ hρ x L) (completionOrder_center_cofinal ρ hρ x L)

/-- Fundamental representatives in the completed product order. -/
noncomputable def completionRepresentative (g : FreeGroup ι) : FreeGroup ι × Multiplicative ℤ :=
  cofinalProductRepresentative (completionOrder ρ hρ x L)
    (completionOrder_center_positive ρ hρ x L) (completionOrder_center_cofinal ρ hρ x L) g

@[simp] theorem completionRepresentative_fst (g : FreeGroup ι) :
    (completionRepresentative ρ hρ x L g).1 = g :=
  cofinalProductRepresentative_fst _ _ _ g

/-- Nonstabilizing elements have precisely the zero-height fundamental representative. -/
theorem completionRepresentative_lift (g : FreeGroup ι) (hg : ρ g x ≠ x) :
    completionLift ρ hρ x (completionRepresentative ρ hρ x L g) = ⟨g, 0⟩ := by
  let := (completionOrder ρ hρ x L).order
  let r := completionRepresentative ρ hρ x L g
  have hrbase : (completionLift ρ hρ x r).base = g := by simp [r]
  have hrne : r ≠ 1 := by
    intro he
    apply hg
    have hfst := congrArg Prod.fst he
    simp only [r, completionRepresentative_fst, Prod.fst_one] at hfst
    simp [hfst]
  have hm := (completionOrder ρ hρ x L).fundamentalRepresentative_mem
    (completionOrder_center_positive ρ hρ x L) (completionOrder_center_cofinal ρ hρ x L) (g, 1)
  change 1 ≤ r ∧ r < cofinalProductZ (FreeGroup ι) at hm
  have hrpos : 1 < r := lt_of_le_of_ne hm.1 (Ne.symm hrne)
  have hp := (completionOrder_lt_iff ρ hρ x L 1 r).mp hrpos
  simp only [map_one, inv_one, one_mul] at hp
  have hp0 : 0 ≤ (completionLift ρ hρ x r).height := by
    rcases hp with hp | ⟨hp, _⟩ <;> omega
  have ht := (completionOrder_lt_iff ρ hρ x L r (cofinalProductZ (FreeGroup ι))).mp hm.2
  have he := completionLift_zpow ρ hρ x 1
  simp only [zpow_one] at he
  rw [he] at ht
  have hz : ((completionLift ρ hρ x r)⁻¹ *
      (orbitCocycle ρ hρ x).central (Multiplicative.ofAdd 1)).height =
      -(completionLift ρ hρ x r).height := by
    simp [NormalizedIntCocycle.central, hrbase, orbitCocycle_inverse_rev, hg, NormalizedIntCocycle.one_right]
  have hp1 : (completionLift ρ hρ x r).height ≤ 0 := by
    rcases ht with ht | ⟨ht, _⟩ <;> rw [hz] at ht <;> omega
  apply NormalizedIntCocycle.Extension.ext
  · exact hrbase
  · change (completionLift ρ hρ x r).height = 0
    omega

/-- Comparing two nonstabilizing representatives reads precisely the original
circular orientation, provided their orbit points are distinct. -/
theorem completionRepresentative_lt_iff (g h : FreeGroup ι)
    (hg : ρ g x ≠ x) (hh : ρ h x ≠ x) (hgh : ρ g x ≠ ρ h x) :
    (completionOrder ρ hρ x L).order.lt
      (completionRepresentative ρ hρ x L g) (completionRepresentative ρ hρ x L h) ↔
      sbtw x (ρ g x) (ρ h x) := by
  rw [completionOrder_lt_iff, completionRepresentative_lift ρ hρ x L g hg,
    completionRepresentative_lift ρ hρ x L h hh]
  have hfix : ρ (g⁻¹ * h) x ≠ x := by
    intro he
    apply hgh
    have he' := congrArg (ρ g) he
    simpa using he'.symm
  have hc : (orbitCocycle ρ hρ x).value g⁻¹ h =
      CircularCarry.value (ρ g x) x (ρ h x) := by
    change CircularCarry.value x (ρ g⁻¹ x) (ρ (g⁻¹ * h) x) = _
    have he := carry_perm (ρ g) (hρ g) x (ρ g⁻¹ x) (ρ (g⁻¹ * h) x)
    simpa using he.symm
  change (0 < -0 - (orbitCocycle ρ hρ x).value g⁻¹ g + 0 +
      (orbitCocycle ρ hρ x).value g⁻¹ h ∨
    (-0 - (orbitCocycle ρ hρ x).value g⁻¹ g + 0 +
      (orbitCocycle ρ hρ x).value g⁻¹ h = 0 ∧
      (ρ (g⁻¹ * h) x ≠ x ∨ L.order.lt 1 (g⁻¹ * h)))) ↔ _
  rw [orbitCocycle_inverse_rev, ite_eq_right hg, hc]
  have hs : sbtw (ρ g x) x (ρ h x) ↔ ¬sbtw x (ρ g x) (ρ h x) := by
    have ht := CircularCarry.strict_or_reverse (Ne.symm hg) hgh hh
    constructor
    · intro hs hn
      exact hs.not_sbtw hn.cyclic_right
    · intro hn
      exact (ht.resolve_left hn).cyclic_left
  simp only [map_mul, map_inv, Equiv.Perm.mul_apply] at hfix
  by_cases he : sbtw x (ρ g x) (ρ h x)
  · simp [CircularCarry.value, hg, hgh, Ne.symm hh, hs, he]
    exact Or.inl hfix
  · simp [CircularCarry.value, hg, hgh, Ne.symm hh, hs, he]

/-- Order completion preserves every strict comparison based at the original
basepoint whose three images are distinct. -/
theorem completedCircularOrbitOrder_sbtw_one (g h : FreeGroup ι)
    (hg : ρ g x ≠ x) (hh : ρ h x ≠ x) (hgh : ρ g x ≠ ρ h x) :
    (completedCircularOrbitOrder ρ hρ x L).order.sbtw 1 g h ↔
      sbtw x (ρ g x) (ρ h x) := by
  change (cofinalProductCircularGroupOrder (completionOrder ρ hρ x L)
    (completionOrder_center_positive ρ hρ x L)
    (completionOrder_center_cofinal ρ hρ x L)).order.sbtw 1 g h ↔ _
  rw [cofinalProductCircularGroupOrder_sbtw_one]
  change ((completionOrder ρ hρ x L).order.lt 1 (completionRepresentative ρ hρ x L g) ∧
    (completionOrder ρ hρ x L).order.lt
      (completionRepresentative ρ hρ x L g) (completionRepresentative ρ hρ x L h)) ↔ _
  have hp : (completionOrder ρ hρ x L).order.lt 1 (completionRepresentative ρ hρ x L g) := by
    rw [completionOrder_lt_iff, map_one, inv_one, one_mul, completionRepresentative_lift ρ hρ x L g hg]
    exact Or.inr ⟨rfl, Or.inl hg⟩
  rw [and_iff_right hp, completionRepresentative_lt_iff ρ hρ x L g h hg hh hgh]

/-- The completed circular order agrees with the original action on every triple
whose orbit images are distinct, irrespective of stabilizers elsewhere. -/
theorem completedCircularOrbitOrder_sbtw (a b c : FreeGroup ι)
    (hab : ρ a x ≠ ρ b x) (hbc : ρ b x ≠ ρ c x) (hca : ρ c x ≠ ρ a x) :
    (completedCircularOrbitOrder ρ hρ x L).order.sbtw a b c ↔
      sbtw (ρ a x) (ρ b x) (ρ c x) := by
  have htrans := (completedCircularOrbitOrder ρ hρ x L).mul_sbtw_mul_left a⁻¹ a b c
  simp only [inv_mul_cancel] at htrans
  rw [← htrans]
  have hb : ρ (a⁻¹ * b) x ≠ x := by
    intro he
    apply hab
    have he' := congrArg (ρ a) he
    simpa using he'.symm
  have hc : ρ (a⁻¹ * c) x ≠ x := by
    intro he
    apply hca
    have he' := congrArg (ρ a) he
    simpa using he'
  have hbc' : ρ (a⁻¹ * b) x ≠ ρ (a⁻¹ * c) x := by
    intro he
    apply hbc
    have he' := congrArg (ρ a) he
    simpa using he'
  rw [completedCircularOrbitOrder_sbtw_one ρ hρ x L _ _ hb hc hbc']
  have he : sbtw (ρ a x) (ρ a (ρ (a⁻¹ * b) x)) (ρ a (ρ (a⁻¹ * c) x)) ↔
      sbtw x (ρ (a⁻¹ * b) x) (ρ (a⁻¹ * c) x) := by
    rw [sbtw_iff_btw_not_btw, sbtw_iff_btw_not_btw, hρ, hρ]
  simpa using he.symm

/-- A free-group circular order supplies a genuine left order via its checked lift;
this provides the stabilizer ordering needed for completion. -/
noncomputable def freeGroupLeftOrderOfCircular (O : CircularGroupOrder (FreeGroup ι)) :
    LeftGroupOrder (FreeGroup ι) := by
  let P := circularFreeProductCone (fun _ : ι => 0) O
  let Q := Subsemigroup.comap (MonoidHom.inl (FreeGroup ι) (Multiplicative ℤ)).toMulHom P.val
  have hQ : IsPositiveCone Q := by
    constructor
    · change (1, 1) ∉ P.val
      exact P.property.1
    · intro g
      obtain h | h | h := P.property.2 (g, 1)
      · exact Or.inl (congrArg Prod.fst h)
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
  exact coneLeftOrder ⟨Q, hQ⟩

/-- If an orbit is already free, completing it does not change its circular order. -/
theorem completedCircularOrbitOrder_eq_of_injective
    (hx : Function.Injective (fun g => ρ g x)) :
    completedCircularOrbitOrder ρ hρ x L = circularOrbitOrder ρ hρ x hx := by
  apply CircularGroupOrder.ext
  intro a b c
  by_cases hab : a = b
  · subst b
    exact iff_of_false (@sbtw_irrefl_left _ (completedCircularOrbitOrder ρ hρ x L).order.toCircularPreorder a c)
      (@sbtw_irrefl_left _ (circularOrbitOrder ρ hρ x hx).order.toCircularPreorder a c)
  by_cases hbc : b = c
  · subst c
    exact iff_of_false (@sbtw_irrefl_right _ (completedCircularOrbitOrder ρ hρ x L).order.toCircularPreorder a b)
      (@sbtw_irrefl_right _ (circularOrbitOrder ρ hρ x hx).order.toCircularPreorder a b)
  by_cases hca : c = a
  · subst c
    exact iff_of_false (@sbtw_irrefl_left_right _ (completedCircularOrbitOrder ρ hρ x L).order.toCircularPreorder a b)
      (@sbtw_irrefl_left_right _ (circularOrbitOrder ρ hρ x hx).order.toCircularPreorder a b)
  exact completedCircularOrbitOrder_sbtw ρ hρ x L a b c
    (fun h => hab (hx h)) (fun h => hbc (hx h)) (fun h => hca (hx h))

/-- Completed signs agree with the original order whenever the finite orbit points
are distinct and have the specified original cyclic ordering. -/
theorem completedCircularOrbitOrder_sign_of_orbit_sign
    (O : CircularGroupOrder (FreeGroup ι)) (a b c : FreeGroup ι)
    (hab : a ≠ b → ρ a x ≠ ρ b x) (hbc : b ≠ c → ρ b x ≠ ρ c x)
    (hca : c ≠ a → ρ c x ≠ ρ a x)
    (hs : sbtw (ρ a x) (ρ b x) (ρ c x) ↔ O.order.sbtw a b c) :
    (completedCircularOrbitOrder ρ hρ x L).order.sbtw a b c ↔ O.order.sbtw a b c := by
  by_cases hab' : a = b
  · subst b
    exact iff_of_false (@sbtw_irrefl_left _ (completedCircularOrbitOrder ρ hρ x L).order.toCircularPreorder a c)
      (@sbtw_irrefl_left _ O.order.toCircularPreorder a c)
  by_cases hbc' : b = c
  · subst c
    exact iff_of_false (@sbtw_irrefl_right _ (completedCircularOrbitOrder ρ hρ x L).order.toCircularPreorder a b)
      (@sbtw_irrefl_right _ O.order.toCircularPreorder a b)
  by_cases hca' : c = a
  · subst c
    exact iff_of_false (@sbtw_irrefl_left_right _ (completedCircularOrbitOrder ρ hρ x L).order.toCircularPreorder a b)
      (@sbtw_irrefl_left_right _ O.order.toCircularPreorder a b)
  exact (completedCircularOrbitOrder_sbtw ρ hρ x L a b c (hab hab') (hbc hbc') (hca hca')).trans hs

/-- A distinct nondegenerate orbit sign yields a genuinely different completed order. -/
theorem completedCircularOrbitOrder_ne_of_changed_sign
    (O : CircularGroupOrder (FreeGroup ι)) (a b c : FreeGroup ι)
    (hab : ρ a x ≠ ρ b x) (hbc : ρ b x ≠ ρ c x) (hca : ρ c x ≠ ρ a x)
    (hs : ¬(sbtw (ρ a x) (ρ b x) (ρ c x) ↔ O.order.sbtw a b c)) :
    completedCircularOrbitOrder ρ hρ x L ≠ O := by
  intro he
  apply hs
  rw [← he]
  exact (completedCircularOrbitOrder_sbtw ρ hρ x L a b c hab hbc hca).symm

end FreeGroup

/-- The approximation step in the source's order-completion argument. Approximate
a finite orbit configuration and change one nondegenerate circular sign; no free
orbit is required for any of the approximating actions. -/
theorem circularOrder_not_isolated_of_action_approximations {ι : Type u}
    (O : CircularGroupOrder (FreeGroup ι))
    (happrox : ∀ S : Finset (FreeGroup ι),
      ∃ (ρ : FreeGroup ι →* Equiv.Perm X) (_hρ : ∀ g, PreservesCircular (ρ g)) (x : X),
        (∀ a ∈ S, ∀ b ∈ S, a ≠ b → ρ a x ≠ ρ b x) ∧
        (∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, sbtw (ρ a x) (ρ b x) (ρ c x) ↔ O.order.sbtw a b c) ∧
        ∃ a b c, ρ a x ≠ ρ b x ∧ ρ b x ≠ ρ c x ∧ ρ c x ≠ ρ a x ∧
          ¬(sbtw (ρ a x) (ρ b x) (ρ c x) ↔ O.order.sbtw a b c)) :
    ¬ IsOpen ({O} : Set (CircularGroupOrder (FreeGroup ι))) := by
  classical
  apply circularOrder_not_isolated_of_finite_signs
  intro F
  let S : Finset (FreeGroup ι) := F.image Prod.fst ∪ F.image (fun p => p.2.1) ∪ F.image (fun p => p.2.2)
  obtain ⟨ρ, hρ, x, hinj, hsign, a, b, c, hab, hbc, hca, hchange⟩ := happrox S
  let L := freeGroupLeftOrderOfCircular O
  refine ⟨completedCircularOrbitOrder ρ hρ x L,
    completedCircularOrbitOrder_ne_of_changed_sign ρ hρ x L O a b c hab hbc hca hchange, ?_⟩
  intro p hp
  have h1 : p.1 ∈ S := Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨p, hp, rfl⟩))
  have h2 : p.2.1 ∈ S := Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨p, hp, rfl⟩))
  have h3 : p.2.2 ∈ S := Finset.mem_union_right _ (Finset.mem_image.mpr ⟨p, hp, rfl⟩)
  have he := completedCircularOrbitOrder_sign_of_orbit_sign ρ hρ x L O p.1 p.2.1 p.2.2
    (hinj _ h1 _ h2) (hinj _ h2 _ h3) (hinj _ h3 _ h1) (hsign _ h1 _ h2 _ h3)
  simpa only [circularOrderSign, decide_eq_decide] using he

end CircularDynamics
end FnZPositiveCones
