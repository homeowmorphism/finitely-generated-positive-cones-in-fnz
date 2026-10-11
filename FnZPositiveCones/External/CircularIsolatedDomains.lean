module

public import FnZPositiveCones.External.CircularDynamicsCoincidence
public import FnZPositiveCones.External.CircularDynamicsCircleDomains
public import FnZPositiveCones.External.OrderedActionsCircleRealization

@[expose] public section

/-! Local consequences of isolation for an actual circular realization. -/
namespace FnZPositiveCones
namespace CircularDynamics
open Filter
open scoped Topology

/-- Translation preserves the concrete circular order used on the standard circle. -/
theorem standardCircle_sbtw_add_right (a b c d : StandardCircle) :
    sbtw (a + d) (b + d) (c + d) ↔ sbtw a b c := by
  have ht (a b c : StandardCircle) : btw (a + d) (b + d) (c + d) ↔ btw a b c := by
    change ((_ : ℝ) ≤ _) ↔ ((_ : ℝ) ≤ _)
    simp only [add_sub_add_right_eq_sub]
  simp only [sbtw_iff_btw_not_btw, ht]

theorem standardCircle_sbtw_coordinate (a b c : StandardCircle) :
    sbtw a b c ↔ 0 < circleCoordinate (b - a) ∧
      circleCoordinate (b - a) < circleCoordinate (c - a) := by
  have he := standardCircle_sbtw_add_right a b c (-a)
  simp only [add_neg_cancel, ← sub_eq_add_neg] at he
  rw [← he]
  have hh := OrderedActions.circle_sbtw_zero_iff (circleCoordinate_mem (b - a))
    (circleCoordinate_mem (c - a))
  simpa only [coe_circleCoordinate] using hh

/-- A strict circular comparison persists under three continuous point motions.
The proof uses the actual cut coordinates away from the two diagonals. -/
theorem eventually_sbtw_of_continuousAt {Y : Type*} [TopologicalSpace Y]
    {f g h : Y → StandardCircle} {x : Y}
    (hf : ContinuousAt f x) (hg : ContinuousAt g x) (hh : ContinuousAt h x)
    (hs : sbtw (f x) (g x) (h x)) :
    ∀ᶠ y in 𝓝 x, sbtw (f y) (g y) (h y) := by
  have hgf : g x - f x ≠ 0 := by
    intro he
    have he' := sub_eq_zero.mp he
    rw [he'] at hs
    exact sbtw_irrefl_left hs
  have hhf : h x - f x ≠ 0 := by
    intro he
    have he' := sub_eq_zero.mp he
    rw [he'] at hs
    exact sbtw_irrefl_left_right hs
  have hgc : ContinuousAt (fun y => circleCoordinate (g y - f y)) x :=
    (continuousAt_circleCoordinate hgf).comp (f := fun y : Y => g y - f y) (x := x) (hg.sub hf)
  have hhc : ContinuousAt (fun y => circleCoordinate (h y - f y)) x :=
    (continuousAt_circleCoordinate hhf).comp (f := fun y : Y => h y - f y) (x := x) (hh.sub hf)
  have hc := (standardCircle_sbtw_coordinate _ _ _).mp hs
  have hpos : ∀ᶠ y in 𝓝 x, 0 < circleCoordinate (g y - f y) :=
    (tendsto_order.mp hgc).1 0 hc.1
  have hlt : ∀ᶠ y in 𝓝 x, circleCoordinate (g y - f y) < circleCoordinate (h y - f y) :=
    (hgc.prodMk hhc).eventually (isOpen_lt continuous_fst continuous_snd |>.mem_nhds hc.2)
  filter_upwards [hpos, hlt] with y hy hy'
  exact (standardCircle_sbtw_coordinate _ _ _).mpr ⟨hy, hy'⟩

/-- For pairwise distinct labels, the entire circular sign is locally constant
as the basepoint moves continuously. -/
theorem eventually_sbtw_iff_of_continuousAt {Y : Type*} [TopologicalSpace Y]
    {f g h : Y → StandardCircle} {x : Y}
    (hf : ContinuousAt f x) (hg : ContinuousAt g x) (hh : ContinuousAt h x)
    (hfg : f x ≠ g x) (hgh : g x ≠ h x) (hhf : h x ≠ f x) :
    ∀ᶠ y in 𝓝 x, sbtw (f y) (g y) (h y) ↔ sbtw (f x) (g x) (h x) := by
  rcases CircularCarry.strict_or_reverse hfg hgh hhf with hs | hs
  · filter_upwards [eventually_sbtw_of_continuousAt hf hg hh hs] with y hy
    exact iff_of_true hy hs
  · have hs' := hs.not_sbtw
    filter_upwards [eventually_sbtw_of_continuousAt hh hg hf hs] with y hy
    exact iff_of_false hy.not_sbtw hs'

universe u
variable {ι : Type u}

/-- A finite set of pairwise distinct orbit points stays distinct when the
basepoint moves slightly. No freeness of the nearby full orbit is assumed. -/
theorem eventually_finite_orbit_injective
    (ρ : FreeGroup ι →* Equiv.Perm StandardCircle) (hc : ∀ g, Continuous (ρ g))
    (base : StandardCircle) (hx : Function.Injective (fun g => ρ g base))
    (S : Finset (FreeGroup ι)) :
    ∀ᶠ y in 𝓝 base, ∀ a ∈ S, ∀ b ∈ S, a ≠ b → ρ a y ≠ ρ b y := by
  apply (Filter.eventually_all_finset S).mpr
  intro a ha
  apply (Filter.eventually_all_finset S).mpr
  intro b hb
  by_cases hab : a = b
  · exact Filter.Eventually.of_forall (fun _ h => False.elim (h hab))
  · have hh := ((hc a).continuousAt.sub (hc b).continuousAt).eventually_ne
      (sub_ne_zero.mpr (hx.ne hab))
    filter_upwards [hh] with y hy _ hye
    exact hy (sub_eq_zero.mpr hye)

/-- All comparisons on a finite orbit set persist near a free basepoint. -/
theorem eventually_finite_orbit_signs
    (ρ : FreeGroup ι →* Equiv.Perm StandardCircle) (hc : ∀ g, Continuous (ρ g))
    (base : StandardCircle) (hx : Function.Injective (fun g => ρ g base))
    (S : Finset (FreeGroup ι)) :
    ∀ᶠ y in 𝓝 base, ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S,
      sbtw (ρ a y) (ρ b y) (ρ c y) ↔ sbtw (ρ a base) (ρ b base) (ρ c base) := by
  apply (Filter.eventually_all_finset S).mpr
  intro a ha
  apply (Filter.eventually_all_finset S).mpr
  intro b hb
  apply (Filter.eventually_all_finset S).mpr
  intro c hcS
  by_cases hab : a = b
  · subst b
    exact Filter.Eventually.of_forall (fun _ => iff_of_false sbtw_irrefl_left sbtw_irrefl_left)
  by_cases hbc : b = c
  · subst c
    exact Filter.Eventually.of_forall (fun _ => iff_of_false sbtw_irrefl_right sbtw_irrefl_right)
  by_cases hca : c = a
  · subst c
    exact Filter.Eventually.of_forall (fun _ => iff_of_false sbtw_irrefl_left_right sbtw_irrefl_left_right)
  exact eventually_sbtw_iff_of_continuousAt (hc a).continuousAt (hc b).continuousAt
    (hc c).continuousAt (hx.ne hab) (hx.ne hbc) (hx.ne hca)

/-- Isolation forces genuine local freeness of the given circle action. Every
basepoint in one open neighborhood has trivial stabilizer and induces the
original order; the proof resolves a hypothetical stabilizer in opposite ways. -/
theorem isolated_orbit_has_free_neighborhood
    (ρ : FreeGroup ι →* Equiv.Perm StandardCircle)
    (hρ : ∀ g, PreservesCircular (ρ g)) (hc : ∀ g, Continuous (ρ g))
    (base : StandardCircle) (hx : Function.Injective (fun g => ρ g base))
    (g₀ : FreeGroup ι) (hg₀ : ρ g₀ base ≠ base)
    (hi : IsOpen ({circularOrbitOrder ρ hρ base hx} : Set (CircularGroupOrder (FreeGroup ι)))) :
    ∃ U : Set StandardCircle, IsOpen U ∧ base ∈ U ∧
      ∀ y ∈ U, Function.Injective (fun g => ρ g y) ∧
        ∀ L : LeftGroupOrder (FreeGroup ι),
          completedCircularOrbitOrder ρ hρ y L = circularOrbitOrder ρ hρ base hx := by
  classical
  let O := circularOrbitOrder ρ hρ base hx
  obtain ⟨F, hF⟩ := (circularOrder_isolated_iff_finite_signs O).mp hi
  let S : Finset (FreeGroup ι) :=
    F.image Prod.fst ∪ F.image (fun p => p.2.1) ∪ F.image (fun p => p.2.2)
  have hmove : ∀ᶠ y in 𝓝 base, ρ g₀ y ≠ y := by
    have hm := ((hc g₀).continuousAt.sub continuousAt_id).eventually_ne (sub_ne_zero.mpr hg₀)
    filter_upwards [hm] with y hy he
    exact hy (sub_eq_zero.mpr he)
  have hnear := (eventually_finite_orbit_injective ρ hc base hx S).and
    ((eventually_finite_orbit_signs ρ hc base hx S).and hmove)
  obtain ⟨U, hUsub, hUopen, hbaseU⟩ := mem_nhds_iff.mp hnear
  refine ⟨U, hUopen, hbaseU, ?_⟩
  intro y hy
  obtain ⟨hinj, hsign, hm⟩ := hUsub hy
  have heq (L : LeftGroupOrder (FreeGroup ι)) : completedCircularOrbitOrder ρ hρ y L = O := by
    apply hF
    intro p hp
    have h1 : p.1 ∈ S :=
      Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨p, hp, rfl⟩))
    have h2 : p.2.1 ∈ S :=
      Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨p, hp, rfl⟩))
    have h3 : p.2.2 ∈ S := Finset.mem_union_right _ (Finset.mem_image.mpr ⟨p, hp, rfl⟩)
    have hs := completedCircularOrbitOrder_sign_of_orbit_sign ρ hρ y L O p.1 p.2.1 p.2.2
      (hinj _ h1 _ h2) (hinj _ h2 _ h3) (hinj _ h3 _ h1)
      (hsign _ h1 _ h2 _ h3)
    simpa only [circularOrderSign, decide_eq_decide] using hs
  have hfix : ∀ k, ρ k y = y → k = 1 := by
    intro k hk
    by_contra hne
    let L := freeGroupLeftOrderOfCircular O
    exact completedCircularOrbitOrder_ne_reverse ρ hρ y L k g₀ hne hk hm
      ((heq L).trans (heq L.reverse).symm)
  refine ⟨?_, heq⟩
  intro a b hab
  change ρ a y = ρ b y at hab
  have hh : ρ (a⁻¹ * b) y = y := by
    rw [map_mul, map_inv]
    change (ρ a).symm (ρ b y) = y
    rw [← hab, Equiv.symm_apply_apply]
  exact inv_mul_eq_one.mp (hfix _ hh)

/-- The points where the entire group orbit is free. -/
def freeOrbitPoints {G : Type*} [Group G] {X : Type*}
    (ρ : G →* Equiv.Perm X) : Set X := {x | Function.Injective (fun g => ρ g x)}

theorem mem_freeOrbitPoints_action_iff {G : Type*} [Group G] {X : Type*}
    (ρ : G →* Equiv.Perm X) (g : G) (x : X) :
    ρ g x ∈ freeOrbitPoints ρ ↔ x ∈ freeOrbitPoints ρ := by
  constructor
  · intro hx a b hab
    apply mul_right_cancel (b := g⁻¹)
    apply hx
    simp only [map_mul, map_inv, Equiv.Perm.mul_apply]
    change ρ a ((ρ g).symm (ρ g x)) = ρ b ((ρ g).symm (ρ g x))
    simpa only [Equiv.symm_apply_apply] using hab
  · intro hx a b hab
    apply mul_right_cancel (b := g)
    apply hx
    simpa only [map_mul, Equiv.Perm.mul_apply] using hab

/-- The free-orbit set is genuinely invariant under the original action. -/
theorem image_freeOrbitPoints {G : Type*} [Group G] {X : Type*}
    (ρ : G →* Equiv.Perm X) (g : G) : ρ g '' freeOrbitPoints ρ = freeOrbitPoints ρ := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (mem_freeOrbitPoints_action_iff ρ g y).mpr hy
  · intro hx
    refine ⟨(ρ g).symm x, ?_, (ρ g).apply_symm_apply x⟩
    apply (mem_freeOrbitPoints_action_iff ρ g ((ρ g).symm x)).mp
    simpa only [Equiv.apply_symm_apply] using hx

/-- Its open interior is also invariant; this is the interval source for the
linear-part argument, without an assumed minimal-set classification. -/
theorem image_interior_freeOrbitPoints {G : Type*} [Group G]
    (ρ : G →* Equiv.Perm StandardCircle) (hc : ∀ g, Continuous (ρ g)) (g : G) :
    ρ g '' interior (freeOrbitPoints ρ) = interior (freeOrbitPoints ρ) := by
  let e : StandardCircle ≃ₜ StandardCircle :=
    { toEquiv := ρ g
      continuous_toFun := hc g
      continuous_invFun := by
        have hh := hc g⁻¹
        rw [map_inv] at hh
        exact hh }
  change e '' interior (freeOrbitPoints ρ) = interior (freeOrbitPoints ρ)
  rw [e.image_interior]
  exact congrArg interior (image_freeOrbitPoints ρ g)

end CircularDynamics

namespace CircularRealization
open CircularDynamics
universe u
variable {ι : Type u} [Nonempty ι] {C : CircularGroupOrder (FreeGroup ι)}

/-- An isolated circular order has an actual neighborhood of the realization
basepoint on which all orbits are free and have the identical order. -/
theorem isolated_has_free_neighborhood (R : CircularRealization C)
    (hi : IsOpen ({C} : Set (CircularGroupOrder (FreeGroup ι)))) :
    ∃ U : Set StandardCircle, IsOpen U ∧ (0 : StandardCircle) ∈ U ∧
      ∀ y ∈ U, Function.Injective (fun g => R.action g y) ∧
        ∀ a b c, sbtw (R.action a y) (R.action b y) (R.action c y) ↔ C.order.sbtw a b c := by
  classical
  have heq : circularOrbitOrder R.action R.action_preserves 0 R.orbit_injective = C := by
    apply CircularGroupOrder.ext
    intro a b c
    exact (R.orbit_sbtw a b c).symm
  let g := FreeGroup.of (Classical.arbitrary ι)
  have hg : R.action g 0 ≠ 0 := by
    intro he
    have he' : R.action g 0 = R.action 1 0 := by simpa only [map_one, Equiv.Perm.one_apply] using he
    exact FreeGroup.of_ne_one _ (R.orbit_injective he')
  obtain ⟨U, hU, hzero, hfree⟩ := isolated_orbit_has_free_neighborhood R.action R.action_preserves
    R.action_continuous 0 R.orbit_injective g hg (heq.symm ▸ hi)
  refine ⟨U, hU, hzero, ?_⟩
  intro y hy
  obtain ⟨hinj, hsign⟩ := hfree y hy
  refine ⟨hinj, ?_⟩
  let L := freeGroupLeftOrderOfCircular C
  have horder : circularOrbitOrder R.action R.action_preserves y hinj = C :=
    (completedCircularOrbitOrder_eq_of_injective R.action R.action_preserves y L hinj).symm.trans
      ((hsign L).trans heq)
  intro a b c
  exact iff_of_eq (congrArg (fun O : CircularGroupOrder (FreeGroup ι) => O.order.sbtw a b c) horder)

/-- The invariant open free-orbit locus contains the marked basepoint. -/
theorem base_mem_interior_freeOrbitPoints (R : CircularRealization C)
    (hi : IsOpen ({C} : Set (CircularGroupOrder (FreeGroup ι)))) :
    (0 : StandardCircle) ∈ interior (freeOrbitPoints R.action) := by
  obtain ⟨U, hU, hzero, hfree⟩ := R.isolated_has_free_neighborhood hi
  exact interior_maximal (fun y hy => (hfree y hy).1) hU hzero

end CircularRealization
end FnZPositiveCones
