module

public import FnZPositiveCones.External.CircularIsolatedDomains
public import FnZPositiveCones.External.OrderedActionsHolder
public import FnZPositiveCones.External.OrderedActionsCircleGaps
public import FnZPositiveCones.External.CircularComponentEndpoints
public import FnZPositiveCones.External.CircularDynamicsLocal

@[expose] public section

/-! The real free locus and its actual component stabilizer action. -/
namespace FnZPositiveCones
namespace CircularDynamics
universe u
variable {G : Type u} [Group G]

/-- The actual setwise stabilizer under an ordered real action. -/
def realSetStabilizer (ρ : G →* (ℝ ≃o ℝ)) (S : Set ℝ) : Subgroup G where
  carrier := {g | ρ g '' S = S}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    change ρ (a * b) '' S = S
    rw [map_mul]
    change (fun x => ρ a (ρ b x)) '' S = S
    rw [← Set.image_image, hb, ha]
  inv_mem' := by
    intro g hg
    change ρ g⁻¹ '' S = S
    have hh := congrArg (fun T => ρ g⁻¹ '' T) hg
    rw [Set.image_image] at hh
    have he : (fun x => ρ g⁻¹ (ρ g x)) = id := by
      funext x
      rw [map_inv]
      exact (ρ g).symm_apply_apply x
    rw [he, Set.image_id] at hh
    exact hh.symm

theorem realSetStabilizer_mapsTo (ρ : G →* (ℝ ≃o ℝ)) (S : Set ℝ)
    (g : realSetStabilizer ρ S) : Set.MapsTo (ρ g.val) S S := by
  intro x hx
  have hg : ρ g.val '' S = S := g.property
  exact Eq.mp (congrArg (fun T : Set ℝ => ρ g.val x ∈ T) hg)
    (Set.mem_image_of_mem (ρ g.val) hx)

/-- Restriction is a genuine homomorphism to interval order automorphisms. -/
def realSetStabilizerAction (ρ : G →* (ℝ ≃o ℝ)) (S : Set ℝ) :
    realSetStabilizer ρ S →* (S ≃o S) where
  toFun g :=
    { toFun x := ⟨ρ g.val x, realSetStabilizer_mapsTo ρ S g x.property⟩
      invFun x := ⟨ρ g.val⁻¹ x, realSetStabilizer_mapsTo ρ S g⁻¹ x.property⟩
      left_inv x := by
        apply Subtype.ext
        change ρ g.val⁻¹ (ρ g.val x.val) = x.val
        rw [map_inv]
        exact (ρ g.val).symm_apply_apply x.val
      right_inv x := by
        apply Subtype.ext
        change ρ g.val (ρ g.val⁻¹ x.val) = x.val
        rw [map_inv]
        exact (ρ g.val).apply_symm_apply x.val
      map_rel_iff' := by intro x y; exact (ρ g.val).map_rel_iff }
  map_one' := by
    ext x
    change ρ 1 x.val = x.val
    rw [map_one]
    rfl
  map_mul' g h := by ext x; exact congrArg (fun e : ℝ ≃o ℝ => e x.val) (ρ.map_mul g.val h.val)

/-- Any interval chart transports this actual restricted action to the line. -/
noncomputable def realSetStabilizerLineAction (ρ : G →* (ℝ ≃o ℝ)) (S : Set ℝ) (e : S ≃o ℝ) :
    realSetStabilizer ρ S →* (ℝ ≃o ℝ) :=
  (OrderedActions.conjugateOrderIso e).comp (realSetStabilizerAction ρ S)

@[simp] theorem realSetStabilizerLineAction_apply
    (ρ : G →* (ℝ ≃o ℝ)) (S : Set ℝ) (e : S ≃o ℝ)
    (g : realSetStabilizer ρ S) (x : ℝ) :
    realSetStabilizerLineAction ρ S e g x =
      e (realSetStabilizerAction ρ S g (e.symm x)) := rfl

/-- The transported action is free whenever the original action is free on the
actual set. This is the precise input to the ordered-action Hölder theorem. -/
theorem realSetStabilizerLineAction_free
    (ρ : G →* (ℝ ≃o ℝ)) (S : Set ℝ) (e : S ≃o ℝ)
    (hfree : ∀ g, ∀ x ∈ S, ρ g x = x → g = 1)
    (g : realSetStabilizer ρ S) (hg : g ≠ 1) (x : ℝ) :
    realSetStabilizerLineAction ρ S e g x ≠ x := by
  intro he
  rw [realSetStabilizerLineAction_apply] at he
  have hh := e.injective (he.trans (e.apply_symm_apply x).symm)
  have hv := congrArg Subtype.val hh
  have hgval : g.val = 1 := hfree g.val (e.symm x).val (e.symm x).property hv
  exact hg (Subtype.ext hgval)

end CircularDynamics

namespace CircularRealization
open CircularDynamics
universe u
variable {ι : Type u} {C : CircularGroupOrder (FreeGroup ι)} (R : CircularRealization C)

/-- Pull back the invariant open free-orbit locus through the actual covering map. -/
def liftedFreeLocus : Set ℝ :=
  ((↑) : ℝ → StandardCircle) ⁻¹' interior (freeOrbitPoints R.action)

theorem isOpen_liftedFreeLocus : IsOpen R.liftedFreeLocus :=
  isOpen_interior.preimage (AddCircle.continuous_mk' (1 : ℝ))

theorem zero_mem_liftedFreeLocus [Nonempty ι]
    (hi : IsOpen ({C} : Set (CircularGroupOrder (FreeGroup ι)))) : 0 ∈ R.liftedFreeLocus :=
  R.base_mem_interior_freeOrbitPoints hi

theorem mem_liftedFreeLocus_action_iff (g : FreeGroup ι × Multiplicative ℤ) (x : ℝ) :
    R.realLift.action g x ∈ R.liftedFreeLocus ↔ x ∈ R.liftedFreeLocus := by
  change ((R.realLift.action g x : ℝ) : StandardCircle) ∈ interior (freeOrbitPoints R.action) ↔ _
  rw [R.coe_real_action]
  have he := image_interior_freeOrbitPoints R.action R.action_continuous g.1
  rw [← he]
  change R.action g.1 (x : StandardCircle) ∈ R.action g.1 '' interior (freeOrbitPoints R.action) ↔ _
  constructor
  · rintro ⟨z, hz, hz'⟩
    have hz'' := (R.action g.1).injective hz'
    change (x : StandardCircle) ∈ interior (freeOrbitPoints R.action)
    exact hz'' ▸ hz
  · intro hx
    exact ⟨(x : StandardCircle), hx, rfl⟩

theorem image_liftedFreeLocus (g : FreeGroup ι × Multiplicative ℤ) :
    R.realLift.action g '' R.liftedFreeLocus = R.liftedFreeLocus := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (R.mem_liftedFreeLocus_action_iff g y).mpr hy
  · intro hx
    refine ⟨(R.realLift.action g).symm x, ?_, (R.realLift.action g).apply_symm_apply x⟩
    apply (R.mem_liftedFreeLocus_action_iff g _).mp
    simpa only [(R.realLift.action g).apply_symm_apply] using hx

/-- The real action is free on this locus, including the central coordinate.
Fixed-point-freeness of the projected circle action alone is not assumed. -/
theorem realLift_free_on_liftedFreeLocus (g : FreeGroup ι × Multiplicative ℤ)
    {x : ℝ} (hx : x ∈ R.liftedFreeLocus) (hfix : R.realLift.action g x = x) : g = 1 := by
  have hf : Function.Injective (fun a => R.action a (x : StandardCircle)) := interior_subset hx
  have hg : g.1 = 1 := by
    apply hf
    have he := congrArg (fun t : ℝ => (t : StandardCircle)) hfix
    rw [R.coe_real_action] at he
    simpa only [map_one, Equiv.Perm.one_apply] using he
  have hcentral : g = cofinalProductZ (FreeGroup ι) ^ g.2.toAdd := by
    apply Prod.ext
    · simpa [cofinalProductZ] using hg
    · apply Multiplicative.toAdd.injective
      simp [cofinalProductZ]
  rw [hcentral, R.central_zpow_apply] at hfix
  have hn : g.2.toAdd = 0 := by exact_mod_cast (show (g.2.toAdd : ℝ) = 0 by linarith)
  rw [hcentral, hn, zpow_zero]

/-- The actual real component containing the marked basepoint. -/
def baseFreeComponent : Set ℝ := connectedComponentIn R.liftedFreeLocus 0

theorem baseFreeComponent_subset : R.baseFreeComponent ⊆ R.liftedFreeLocus :=
  connectedComponentIn_subset _ _

theorem isOpen_baseFreeComponent : IsOpen R.baseFreeComponent :=
  R.isOpen_liftedFreeLocus.connectedComponentIn

theorem isConnected_baseFreeComponent [Nonempty ι]
    (hi : IsOpen ({C} : Set (CircularGroupOrder (FreeGroup ι)))) :
    IsConnected R.baseFreeComponent :=
  isConnected_connectedComponentIn_iff.mpr (R.zero_mem_liftedFreeLocus hi)

/-- Membership of the moved basepoint exactly detects preservation of its
connected component, so the subgroup is derived from the original action. -/
theorem image_baseFreeComponent_eq_iff [Nonempty ι]
    (hi : IsOpen ({C} : Set (CircularGroupOrder (FreeGroup ι))))
    (g : FreeGroup ι × Multiplicative ℤ) :
    R.realLift.action g '' R.baseFreeComponent = R.baseFreeComponent ↔
      R.realLift.action g 0 ∈ R.baseFreeComponent := by
  have he := (R.realLift.action g).toHomeomorph.image_connectedComponentIn
    (R.zero_mem_liftedFreeLocus hi)
  change R.realLift.action g '' R.baseFreeComponent =
    connectedComponentIn (R.realLift.action g '' R.liftedFreeLocus) (R.realLift.action g 0) at he
  rw [R.image_liftedFreeLocus] at he
  constructor
  · intro h
    rw [← h]
    exact ⟨0, mem_connectedComponentIn (R.zero_mem_liftedFreeLocus hi), rfl⟩
  · intro hg
    exact he.trans (connectedComponentIn_eq hg).symm

/-- A proper lifted free locus has an actual missing point in one period. -/
theorem exists_period_cut_of_liftedFreeLocus_ne_univ [Nonempty ι]
    (hi : IsOpen ({C} : Set (CircularGroupOrder (FreeGroup ι))))
    (hproper : R.liftedFreeLocus ≠ Set.univ) :
    ∃ q : ℝ, 0 < q ∧ q < 1 ∧ q ∉ R.liftedFreeLocus ∧ q - 1 ∉ R.liftedFreeLocus := by
  have hex : ∃ x, x ∉ R.liftedFreeLocus := by
    by_contra h
    push Not at h
    exact hproper (Set.eq_univ_of_forall h)
  obtain ⟨x, hx⟩ := hex
  let q := circleCoordinate (x : StandardCircle)
  have hq : q ∉ R.liftedFreeLocus := by
    intro h
    apply hx
    change (x : StandardCircle) ∈ interior (freeOrbitPoints R.action)
    change (q : StandardCircle) ∈ interior (freeOrbitPoints R.action) at h
    simpa only [q, coe_circleCoordinate] using h
  have hqmem := circleCoordinate_mem (x : StandardCircle)
  have hqpos : 0 < q := lt_of_le_of_ne hqmem.1 (by
    intro he
    exact hq (he ▸ R.zero_mem_liftedFreeLocus hi))
  refine ⟨q, hqpos, hqmem.2, hq, ?_⟩
  intro h
  apply hq
  change ((q - 1 : ℝ) : StandardCircle) ∈ interior (freeOrbitPoints R.action) at h
  change (q : StandardCircle) ∈ interior (freeOrbitPoints R.action)
  simpa only [AddCircle.coe_sub, AddCircle.coe_period, sub_zero] using h

/-- Periodic missing points bound the actual connected component. The bounds
are deduced from connectedness, not supplied as an interval hypothesis. -/
theorem baseFreeComponent_subset_period [Nonempty ι]
    (hi : IsOpen ({C} : Set (CircularGroupOrder (FreeGroup ι))))
    {q : ℝ} (hq : 0 < q) (hq1 : q < 1)
    (hcut : q ∉ R.liftedFreeLocus) (hcut' : q - 1 ∉ R.liftedFreeLocus) :
    R.baseFreeComponent ⊆ Set.Ioo (q - 1) q := by
  have hzero : 0 ∈ R.baseFreeComponent := mem_connectedComponentIn (R.zero_mem_liftedFreeLocus hi)
  have hc := (R.isConnected_baseFreeComponent hi).isPreconnected.ordConnected
  intro x hx
  constructor
  · by_contra h
    apply hcut'
    exact R.baseFreeComponent_subset (hc.out hx hzero ⟨le_of_not_gt h, by linarith⟩)
  · by_contra h
    apply hcut
    exact R.baseFreeComponent_subset (hc.out hzero hx ⟨hq.le, le_of_not_gt h⟩)

/-- Every isolated realization's base component has an actual order chart onto
the line, whether its lifted free locus is the whole line or a proper set. -/
theorem baseFreeComponent_nonempty_orderIso_real [Nonempty ι]
    (hi : IsOpen ({C} : Set (CircularGroupOrder (FreeGroup ι)))) :
    Nonempty (R.baseFreeComponent ≃o ℝ) := by
  by_cases hfull : R.liftedFreeLocus = Set.univ
  · have he : R.baseFreeComponent = Set.univ := by
      change connectedComponentIn R.liftedFreeLocus 0 = Set.univ
      rw [hfull, connectedComponentIn_univ]
      exact PreconnectedSpace.connectedComponent_eq_univ (0 : ℝ)
    exact ⟨(Set.orderIsoOfEq _ _ he).trans OrderIso.Set.univ⟩
  · obtain ⟨q, hq, hq1, hcut, hcut'⟩ := R.exists_period_cut_of_liftedFreeLocus_ne_univ hi hfull
    have hJ := R.baseFreeComponent_subset_period hi hq hq1 hcut hcut'
    have hcomp : IsCompact (closure R.baseFreeComponent) :=
      isCompact_Icc.of_isClosed_subset isClosed_closure
        (closure_minimal (hJ.trans Set.Ioo_subset_Icc_self) isClosed_Icc)
    obtain ⟨a, b, hab, hI, _⟩ := open_connected_real_eq_Ioo R.isOpen_baseFreeComponent
      (R.isConnected_baseFreeComponent hi) hcomp
    exact ⟨(Set.orderIsoOfEq _ _ hI).trans (realIooOrderIso a b hab)⟩

/-- A checked free real action of the actual base-component stabilizer. -/
theorem exists_free_baseComponent_real_action [Nonempty ι]
    (hi : IsOpen ({C} : Set (CircularGroupOrder (FreeGroup ι)))) :
    ∃ ρ : realSetStabilizer R.realLift.action R.baseFreeComponent →* (ℝ ≃o ℝ),
      ∀ g, g ≠ 1 → ∀ x, ρ g x ≠ x := by
  obtain ⟨e⟩ := R.baseFreeComponent_nonempty_orderIso_real hi
  refine ⟨realSetStabilizerLineAction R.realLift.action R.baseFreeComponent e, ?_⟩
  exact realSetStabilizerLineAction_free _ _ _ (fun g x hx hfix =>
    R.realLift_free_on_liftedFreeLocus g (R.baseFreeComponent_subset hx) hfix)

/-- Hölder applies to the constructed component action, so the actual
stabilizer is abelian without any assumed commutativity. -/
theorem baseComponentStabilizer_commute [Nonempty ι]
    (hi : IsOpen ({C} : Set (CircularGroupOrder (FreeGroup ι))))
    (g h : realSetStabilizer R.realLift.action R.baseFreeComponent) : Commute g h := by
  obtain ⟨ρ, hf⟩ := R.exists_free_baseComponent_real_action hi
  exact OrderedActions.commute_of_free_real_action ρ hf g h

/-- Distinct free generators do not commute, checked using the two reduced words. -/
theorem distinct_free_generators_not_commute {i j : ι} (hij : i ≠ j) :
    ¬ Commute (FreeGroup.of i) (FreeGroup.of j) := by
  classical
  intro hc
  have hr (a b : ι) : FreeGroup.IsReduced [(a, true), (b, true)] :=
    FreeGroup.isReduced_cons_cons.mpr ⟨fun _ => rfl, FreeGroup.IsReduced.singleton⟩
  have he := congrArg FreeGroup.toWord hc.eq
  simp only [FreeGroup.of, FreeGroup.mul_mk, List.singleton_append,
    FreeGroup.toWord_mk, (hr i j).reduce_eq, (hr j i).reduce_eq] at he
  exact hij (Prod.mk.inj (List.cons.inj he).1).1

/-- For a nonabelian free group the invariant lifted free locus is proper.
Otherwise the whole product group would act freely on the line, contradicting
its explicit noncommuting generators. -/
theorem liftedFreeLocus_ne_univ [Nontrivial ι] :
    R.liftedFreeLocus ≠ Set.univ := by
  intro he
  have hf : ∀ g : FreeGroup ι × Multiplicative ℤ, g ≠ 1 →
      ∀ x, R.realLift.action g x ≠ x := by
    intro g hg x hx
    exact hg (R.realLift_free_on_liftedFreeLocus g (he.symm ▸ Set.mem_univ x) hx)
  obtain ⟨i, j, hij⟩ := exists_pair_ne ι
  have hh := OrderedActions.commute_of_free_real_action R.realLift.action hf
    (FreeGroup.of i, 1) (FreeGroup.of j, 1)
  exact distinct_free_generators_not_commute hij
    (congrArg Prod.fst hh.eq)

end CircularRealization
end FnZPositiveCones
