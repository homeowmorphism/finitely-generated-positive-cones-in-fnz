module

public import FnZPositiveCones.External.CocycleExtension
public import FnZPositiveCones.Cone.Topology

@[expose] public section

/-! Continuity of the explicit free-group lift from normalized integer cocycles.
The topology records all cocycle coordinates. This does not construct cocycles
from circular orders or prove a local-section identity for the circular quotient. -/

namespace FnZPositiveCones
namespace NormalizedIntCocycle

universe u
variable {G : Type u} [Group G]

/-- Pointwise convergence in the discrete integer cocycle coordinates. -/
instance : TopologicalSpace (NormalizedIntCocycle G) :=
  TopologicalSpace.induced NormalizedIntCocycle.value inferInstance

theorem continuous_value : Continuous (NormalizedIntCocycle.value (G := G)) :=
  continuous_induced_dom

theorem continuous_value_apply (g h : G) :
    Continuous (fun c : NormalizedIntCocycle G => c.value g h) :=
  (continuous_apply h).comp ((continuous_apply g).comp continuous_value)

variable {ι : Type u}

/-- The height of a fixed free word depends continuously on the cocycle. -/
theorem continuous_freeSection_height (t : ι → ℤ) (g : FreeGroup ι) :
    Continuous (fun c : NormalizedIntCocycle (FreeGroup ι) => (c.freeSection t g).height) := by
  induction g using FreeGroup.induction_on with
  | one => simpa using (continuous_const (y := (0 : ℤ)))
  | of i =>
    simpa only [freeSection, FreeGroup.lift_apply_of] using
      (continuous_const (y := t i) :
        Continuous (fun _ : NormalizedIntCocycle (FreeGroup ι) => t i))
  | inv_of i ih =>
    have hh : Continuous (fun c : NormalizedIntCocycle (FreeGroup ι) =>
        -(c.freeSection t (FreeGroup.of i)).height - c.value (FreeGroup.of i)⁻¹ (FreeGroup.of i)) :=
      ih.neg.sub (continuous_value_apply (FreeGroup.of i)⁻¹ (FreeGroup.of i))
    simpa only [map_inv, height_inv, freeSection_base] using hh
  | mul x y ihx ihy =>
    have hh : Continuous (fun c : NormalizedIntCocycle (FreeGroup ι) =>
        (c.freeSection t x).height + (c.freeSection t y).height + c.value x y) :=
      (ihx.add ihy).add (continuous_value_apply x y)
    simpa only [map_mul, height_mul, freeSection_base] using hh

/-- The exact sign formula in the chosen splitting, retaining the zero-height case. -/
theorem mem_freeProductPositive_iff (c : NormalizedIntCocycle (FreeGroup ι))
    (t : ι → ℤ) (hc : c.IsCircular) (x : FreeGroup ι × Multiplicative ℤ) :
    x ∈ c.freeProductPositive t hc ↔
      0 < (c.freeSection t x.1).height + x.2.toAdd ∨
        ((c.freeSection t x.1).height + x.2.toAdd = 0 ∧ x.1 ≠ 1) := by
  change (0 < (c.freeProductHom t x).height ∨
    ((c.freeProductHom t x).height = 0 ∧ (c.freeProductHom t x).base ≠ 1)) ↔ _
  rw [freeProductHom_height, freeProductHom_base]

/-- The actual strict cone obtained by the explicit checked free splitting. -/
def freeProductCone (t : ι → ℤ)
    (c : {c : NormalizedIntCocycle (FreeGroup ι) // c.IsCircular}) :
    PositiveCone (FreeGroup ι × Multiplicative ℤ) :=
  ⟨c.1.freeProductPositive t c.2, c.1.freeProductPositive_isPositiveCone t c.2⟩

open scoped Classical in
/-- Every sign coordinate of the lifted cone is a discrete function of one height. -/
theorem coneSign_freeProductCone (t : ι → ℤ)
    (c : {c : NormalizedIntCocycle (FreeGroup ι) // c.IsCircular})
    (x : FreeGroup ι × Multiplicative ℤ) :
    coneSign (freeProductCone t c) x =
      decide (0 < (c.1.freeSection t x.1).height + x.2.toAdd ∨
        ((c.1.freeSection t x.1).height + x.2.toAdd = 0 ∧ x.1 ≠ 1)) := by
  classical
  simp only [coneSign, freeProductCone, mem_freeProductPositive_iff]

/-- Fixed generator heights give a continuous lift into the product sign topology. -/
theorem continuous_freeProductCone (t : ι → ℤ) :
    Continuous (freeProductCone t) := by
  classical
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro x
  change Continuous (fun c => coneSign (freeProductCone t c) x)
  simp only [coneSign_freeProductCone]
  have hs : Continuous (fun h : ℤ => decide (0 < h ∨ (h = 0 ∧ x.1 ≠ 1))) :=
    continuous_of_discreteTopology
  exact hs.comp (((continuous_freeSection_height t x.1).comp continuous_subtype_val).add
    continuous_const)

/-- A normalized cocycle is determined by its integer values. -/
theorem value_injective : Function.Injective (NormalizedIntCocycle.value (G := G)) := by
  rintro ⟨c, hc₁, hc₂, hc₃⟩ ⟨d, hd₁, hd₂, hd₃⟩ h
  cases h
  rfl

/-- Cone inclusion bounds the height of every element in the selected section. -/
theorem freeSection_height_le_of_cone_le (t : ι → ℤ)
    {c d : {c : NormalizedIntCocycle (FreeGroup ι) // c.IsCircular}}
    (hcone : (freeProductCone t c).1 ≤ (freeProductCone t d).1) (g : FreeGroup ι) :
    (c.1.freeSection t g).height ≤ (d.1.freeSection t g).height := by
  by_cases hg : g = 1
  · subst g
    simp
  · have hp : (g, Multiplicative.ofAdd (-(c.1.freeSection t g).height)) ∈
        (freeProductCone t c).1 := by
      apply (mem_freeProductPositive_iff c.1 t c.2 _).mpr
      exact Or.inr ⟨by simp, hg⟩
    have hd := (mem_freeProductPositive_iff d.1 t d.2 _).mp (hcone hp)
    change (0 < (d.1.freeSection t g).height + -(c.1.freeSection t g).height ∨
      ((d.1.freeSection t g).height + -(c.1.freeSection t g).height = 0 ∧ g ≠ 1)) at hd
    omega

/-- Fixed generator heights make the lifted strict cone determine its cocycle. -/
theorem freeProductCone_injective (t : ι → ℤ) : Function.Injective (freeProductCone t) := by
  intro c d hcone
  have hval : (freeProductCone t c).1 = (freeProductCone t d).1 :=
    congrArg Subtype.val hcone
  have hh (g : FreeGroup ι) : (c.1.freeSection t g).height = (d.1.freeSection t g).height :=
    le_antisymm (freeSection_height_le_of_cone_le t hval.le g)
      (freeSection_height_le_of_cone_le t hval.ge g)
  apply Subtype.ext
  apply value_injective
  funext g h
  have hc := congrArg Extension.height ((c.1.freeSection t).map_mul g h)
  have hd := congrArg Extension.height ((d.1.freeSection t).map_mul g h)
  simp only [height_mul, freeSection_base] at hc hd
  rw [hh (g * h), hh g, hh h] at hc
  omega

/-- Isolation of a lifted cone forces isolation of its normalized circular cocycle. -/
theorem isOpen_singleton_of_freeProductCone (t : ι → ℤ)
    (c : {c : NormalizedIntCocycle (FreeGroup ι) // c.IsCircular})
    (hc : IsOpen ({freeProductCone t c} :
      Set (PositiveCone (FreeGroup ι × Multiplicative ℤ)))) :
    IsOpen ({c} : Set {c : NormalizedIntCocycle (FreeGroup ι) // c.IsCircular}) := by
  have hpre : freeProductCone t ⁻¹' {freeProductCone t c} = {c} := by
    ext d
    exact (freeProductCone_injective t).eq_iff
  rw [← hpre]
  exact hc.preimage (continuous_freeProductCone t)

end NormalizedIntCocycle
end FnZPositiveCones
