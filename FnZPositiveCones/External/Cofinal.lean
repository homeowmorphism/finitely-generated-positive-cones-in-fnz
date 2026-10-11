module

public import FnZPositiveCones.Cone.Topology

@[expose] public section

/-!
# Checked starting lemmas for the cofinal-center branch

These lemmas construct the integer normalization of a cofinal positive element
in a left-ordered group. They do not assert the still-missing circular-order
quotient, local lifting section, or dynamical non-isolation theorem.
-/

namespace FnZPositiveCones

universe u v
variable {G : Type u} [Group G]

/-- Cofinality is stated using integer powers and the chosen left-invariant order. -/
def LeftGroupOrder.IsCofinal (O : LeftGroupOrder G) (z : G) : Prop :=
  ∀ g : G, ∃ m n : ℤ, O.order.le (z ^ m) g ∧ O.order.le g (z ^ n)

/-- Positive powers are strictly increasing with their integer exponent using left invariance only. -/
theorem LeftGroupOrder.zpow_strictMono (O : LeftGroupOrder G) {z : G}
    (hz : O.order.lt 1 z) :
    (letI : LinearOrder G := O.order; StrictMono (fun k : ℤ => z ^ k)) := by
  let := O.order
  apply strictMono_int_of_lt_succ
  intro k
  simpa only [mul_one, zpow_add, zpow_one] using O.mul_lt_mul_left (z ^ k) hz

/-- Each element lies between a unique pair of consecutive powers of a positive cofinal element. -/
theorem LeftGroupOrder.exists_unique_power_floor (O : LeftGroupOrder G) {z : G}
    (hz : O.order.lt 1 z) (hc : O.IsCofinal z) (g : G) :
    ∃! k : ℤ, O.order.le (z ^ k) g ∧ O.order.lt g (z ^ (k + 1)) := by
  let := O.order
  have hmono := O.zpow_strictMono hz
  obtain ⟨m, n, hm, hn⟩ := hc g
  obtain ⟨k, hk, hmax⟩ := Int.exists_greatest_of_bdd
    (P := fun k => z ^ k ≤ g)
    ⟨n, fun k hkg => hmono.le_iff_le.mp (hkg.trans hn)⟩ ⟨m, hm⟩
  have hupper : g < z ^ (k + 1) := by
    apply lt_of_not_ge
    intro h
    have h' := hmax (k + 1) h
    omega
  refine ⟨k, ⟨hk, hupper⟩, ?_⟩
  intro l hl
  have hlk : l < k + 1 := hmono.lt_iff_lt.mp (hl.1.trans_lt hupper)
  have hkl : k < l + 1 := hmono.lt_iff_lt.mp (hk.trans_lt hl.2)
  omega

/-- The selected integer floor, justified by its existence and uniqueness theorem. -/
noncomputable def LeftGroupOrder.powerFloor (O : LeftGroupOrder G) {z : G}
    (hz : O.order.lt 1 z) (hc : O.IsCofinal z) (g : G) : ℤ :=
  (O.exists_unique_power_floor hz hc g).choose

theorem LeftGroupOrder.powerFloor_spec (O : LeftGroupOrder G) {z : G}
    (hz : O.order.lt 1 z) (hc : O.IsCofinal z) (g : G) :
    O.order.le (z ^ O.powerFloor hz hc g) g ∧
      O.order.lt g (z ^ (O.powerFloor hz hc g + 1)) :=
  (O.exists_unique_power_floor hz hc g).choose_spec.1

/-- The representative obtained by multiplying by the inverse floor power. -/
noncomputable def LeftGroupOrder.fundamentalRepresentative (O : LeftGroupOrder G) {z : G}
    (hz : O.order.lt 1 z) (hc : O.IsCofinal z) (g : G) : G :=
  z ^ (-O.powerFloor hz hc g) * g

/-- The normalized representative really lies in the half-open fundamental interval. -/
theorem LeftGroupOrder.fundamentalRepresentative_mem (O : LeftGroupOrder G) {z : G}
    (hz : O.order.lt 1 z) (hc : O.IsCofinal z) (g : G) :
    O.order.le 1 (O.fundamentalRepresentative hz hc g) ∧
      O.order.lt (O.fundamentalRepresentative hz hc g) z := by
  let := O.order
  obtain ⟨hl, hu⟩ := O.powerFloor_spec hz hc g
  constructor
  · have h := O.mul_le_mul_left _ _ (z ^ (-O.powerFloor hz hc g)) hl
    simpa only [fundamentalRepresentative, ← zpow_add, neg_add_cancel, zpow_zero] using h
  · have h := O.mul_lt_mul_left (z ^ (-O.powerFloor hz hc g)) hu
    simpa only [fundamentalRepresentative, ← zpow_add, neg_add_cancel_left, zpow_one] using h

/-- A power translate belongs to the fundamental interval only at the selected exponent. -/
theorem LeftGroupOrder.fundamentalRepresentative_unique_exponent (O : LeftGroupOrder G) {z : G}
    (hz : O.order.lt 1 z) (hc : O.IsCofinal z) (g : G) (k : ℤ)
    (hk : O.order.le 1 (z ^ (-k) * g) ∧ O.order.lt (z ^ (-k) * g) z) :
    k = O.powerFloor hz hc g := by
  let := O.order
  have hl := O.mul_le_mul_left _ _ (z ^ k) hk.1
  have hu := O.mul_lt_mul_left (z ^ k) hk.2
  have hb : z ^ k ≤ g ∧ g < z ^ (k + 1) := by
    constructor
    · simpa only [mul_one, ← mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, one_mul] using hl
    · simp only [← mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, one_mul] at hu
      simpa only [zpow_add, zpow_one] using hu
  exact (O.exists_unique_power_floor hz hc g).choose_spec.2 k hb

/-- Normalization is constant on left translates by powers of the cofinal element. -/
theorem LeftGroupOrder.fundamentalRepresentative_zpow_mul (O : LeftGroupOrder G) {z : G}
    (hz : O.order.lt 1 z) (hc : O.IsCofinal z) (g : G) (m : ℤ) :
    O.fundamentalRepresentative hz hc (z ^ m * g) = O.fundamentalRepresentative hz hc g := by
  have hshift : O.powerFloor hz hc (z ^ m * g) = m + O.powerFloor hz hc g := by
    apply Eq.symm
    apply O.fundamentalRepresentative_unique_exponent hz hc
    convert O.fundamentalRepresentative_mem hz hc g using 1 <;>
      simp only [fundamentalRepresentative] <;> group
  simp only [fundamentalRepresentative, hshift]
  group

/-- For a central cofinal element normalization is also constant on right power translates. -/
theorem LeftGroupOrder.fundamentalRepresentative_mul_zpow (O : LeftGroupOrder G) {z : G}
    (hz : O.order.lt 1 z) (hc : O.IsCofinal z)
    (hcentral : ∀ g : G, Commute z g) (g : G) (m : ℤ) :
    O.fundamentalRepresentative hz hc (g * z ^ m) = O.fundamentalRepresentative hz hc g := by
  rw [← ((hcentral g).zpow_left m).eq]
  exact O.fundamentalRepresentative_zpow_mul hz hc g m

/-- A continuous local section through an isolated point makes its image isolated.
This is the extra topological input required in the cofinal circular-order adapter. -/
theorem isOpen_singleton_of_continuous_local_section
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (x : X) (U : Set Y) (hU : IsOpen U) (hxU : f x ∈ U)
    (s : U → X) (hs : Continuous s) (hsection : ∀ y : U, f (s y) = y.val)
    (hx : s ⟨f x, hxU⟩ = x) (hiso : IsOpen ({x} : Set X)) :
    IsOpen ({f x} : Set Y) := by
  have he : s ⁻¹' ({x} : Set X) = {⟨f x, hxU⟩} := by
    ext y
    constructor
    · intro hy
      apply Set.mem_singleton_iff.mpr
      apply Subtype.ext
      exact (hsection y).symm.trans (congrArg f hy)
    · rintro rfl
      exact hx
  have hi : IsOpen ({⟨f x, hxU⟩} : Set U) := he ▸ hiso.preimage hs
  simpa only [Set.image_singleton] using hU.isOpenMap_subtype_val _ hi

end FnZPositiveCones
