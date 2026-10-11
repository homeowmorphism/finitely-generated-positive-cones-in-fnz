module

public import FnZPositiveCones.External.CircularCocycle
public import FnZPositiveCones.External.CircularInjectivity
public import FnZPositiveCones.External.CocycleTopology

@[expose] public section

/-! The actual circular-order sign topology and the continuous lift over a free group. -/
namespace FnZPositiveCones
universe u
variable {G : Type u} [Group G]

/-- Strict circular signs use the discrete topology on Bool. -/
noncomputable def circularOrderSign (O : CircularGroupOrder G) (p : G × G × G) : Bool := by
  classical
  exact decide (O.order.sbtw p.1 p.2.1 p.2.2)

/-- Pointwise convergence of the strict circular relation. -/
noncomputable instance : TopologicalSpace (CircularGroupOrder G) :=
  TopologicalSpace.induced circularOrderSign inferInstance

theorem continuous_circularOrderSign_apply (a b c : G) :
    Continuous (fun O : CircularGroupOrder G => circularOrderSign O (a, b, c)) :=
  (continuous_apply (a, b, c)).comp
    (show Continuous (circularOrderSign (G := G)) from continuous_induced_dom)

/-- Each fixed carry is a discrete function of one circular sign. -/
theorem continuous_circularCarry (a b c : G) :
    Continuous (fun O : CircularGroupOrder G => @CircularCarry.value G O.order a b c) := by
  classical
  by_cases hab : a = b
  · simp [CircularCarry.value, hab, continuous_const]
  by_cases hbc : b = c
  · simp [CircularCarry.value, hbc, continuous_const]
  by_cases hac : a = c
  · simp [CircularCarry.value, hbc, hac, continuous_const]
  have hdisc : Continuous (fun s : Bool => if s = true then (0 : ℤ) else 1) :=
    continuous_of_discreteTopology
  simpa [Function.comp_def, CircularCarry.value, hab, hbc, hac, circularOrderSign] using
    hdisc.comp (continuous_circularOrderSign_apply a b c)

/-- The actual normalized cocycle depends continuously on the circular order. -/
theorem continuous_circularCocycle :
    Continuous (CircularGroupOrder.toNormalizedIntCocycle (G := G)) := by
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro g
  apply continuous_pi
  intro h
  exact continuous_circularCarry 1 g (g * h)

/-- The proved range property bundles circular-order cocycles for the lifting map. -/
noncomputable def CircularGroupOrder.circularCocycle (O : CircularGroupOrder G) :
    {c : NormalizedIntCocycle G // c.IsCircular} :=
  ⟨O.toNormalizedIntCocycle, O.toNormalizedIntCocycle_isCircular⟩

theorem continuous_circularCocycle_subtype :
    Continuous (CircularGroupOrder.circularCocycle (G := G)) :=
  continuous_circularCocycle.subtype_mk _

/-- The explicit lift with fixed generator heights, on the actual circular-order space. -/
noncomputable def circularFreeProductCone {ι : Type u} (t : ι → ℤ)
    (O : CircularGroupOrder (FreeGroup ι)) : PositiveCone (FreeGroup ι × Multiplicative ℤ) :=
  NormalizedIntCocycle.freeProductCone t O.circularCocycle

theorem continuous_circularFreeProductCone {ι : Type u} (t : ι → ℤ) :
    Continuous (circularFreeProductCone t) :=
  (NormalizedIntCocycle.continuous_freeProductCone t).comp continuous_circularCocycle_subtype

/-- Fixed generator heights make the lifted cone determine the original circular order. -/
theorem circularFreeProductCone_injective {ι : Type u} (t : ι → ℤ) :
    Function.Injective (circularFreeProductCone t) := by
  intro O P h
  have hc := NormalizedIntCocycle.freeProductCone_injective t h
  exact CircularGroupOrder.toNormalizedIntCocycle_injective (congrArg Subtype.val hc)

/-- Isolation transfers from the lifted cone to its circular order by a continuous
injective preimage. This is the direction required in the odd-rank reduction. -/
theorem isOpen_singleton_of_circularFreeProductCone {ι : Type u} (t : ι → ℤ)
    (O : CircularGroupOrder (FreeGroup ι))
    (h : IsOpen ({circularFreeProductCone t O} :
      Set (PositiveCone (FreeGroup ι × Multiplicative ℤ)))) :
    IsOpen ({O} : Set (CircularGroupOrder (FreeGroup ι))) := by
  have he : circularFreeProductCone t ⁻¹' {circularFreeProductCone t O} = {O} := by
    ext P
    exact (circularFreeProductCone_injective t).eq_iff
  rw [← he]
  exact h.preimage (continuous_circularFreeProductCone t)

end FnZPositiveCones
