module

public import FnZPositiveCones.External.NoncofinalConvexJumpAdapter
public import FnZPositiveCones.External.NoncofinalFreeTower
public import FnZPositiveCones.External.NoncofinalRayPerturbation
public import FnZPositiveCones.External.OrderedActionsRealization

@[expose] public section

/-!
# Actual crossings from finite positive generation and noncofinality

The convex chain, relative free-subgroup obstruction, ordered coset action,
and real realization are assembled here. No nonnormality, crossing, or
minimality hypothesis remains in the assembled endpoints. The resulting real
components may be rays; central invariance of a chosen component is a separate
geometric obligation and is not asserted by these theorems.
-/

namespace FnZPositiveCones.NoncofinalCrossingExistence

open NoncofinalConvexJump NoncofinalConvexJumpAdapter NoncofinalCrossings

universe u
variable {G : Type u} [Group G]

/-- A strict inequality of convex left cosets forces the same inequality of
any representatives in the original order. -/
theorem order_lt_of_coset_lt (O : LeftGroupOrder G) (C : Subgroup G)
    (hC : letI := O.order; Set.OrdConnected (C : Set G)) {a b : G}
    (hab : letI := cosetLinearOrder O C hC
      (QuotientGroup.mk a : G ⧸ C) < QuotientGroup.mk b) : O.order.lt a b := by
  let := O.order
  let := cosetLinearOrder O C hC
  apply lt_of_not_ge
  intro hba
  exact hab.not_ge ((coset_mk_le_mk O C hC b a).mpr (Or.inl hba))

/-- The orbit of a tight realization preserves strict inequalities. -/
theorem realization_lt_iff (O : LeftGroupOrder G) (R : TightRealization O) (a b : G) :
    O.order.lt a b ↔ R.action a R.base < R.action b R.base := by
  let := O.order
  simp only [lt_iff_le_not_ge, ← R.order_iff]

/-- An actual crossing of the ordered coset action lifts to a crossing of the
original real action by choosing representatives. Powers keep their order
because strict coset comparisons hold for every representative. -/
theorem crossing_in_realization (O : LeftGroupOrder G) (C : Subgroup G)
    (hC : letI := O.order; Set.OrdConnected (C : Set G)) (R : TightRealization O)
    {f g : G} {u v w : G ⧸ C}
    (hc : letI := cosetLinearOrder O C hC
      Crossing (cosetAction O C hC f) (cosetAction O C hC g) u v w) :
    ∃ u' v' w' : ℝ, Crossing (R.action f) (R.action g) u' v' w' := by
  let := cosetLinearOrder O C hC
  have hlift {a b : G} (hab : (QuotientGroup.mk a : G ⧸ C) < QuotientGroup.mk b) :
      R.action a R.base < R.action b R.base :=
    (realization_lt_iff O R a b).mp (order_lt_of_coset_lt O C hC hab)
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective u
  obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective v
  obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective w
  refine ⟨R.action u R.base, R.action v R.base, R.action w R.base,
    hlift hc.left_lt_middle, hlift hc.middle_lt_right, ?_, ?_, ?_⟩
  · intro n
    have hn : (QuotientGroup.mk (g ^ n * u) : G ⧸ C) < QuotientGroup.mk v := by
      simpa only [← map_pow, cosetAction_mk] using hc.left_bounded n
    simpa only [map_mul, map_pow, RelIso.mul_apply] using hlift hn
  · intro n
    have hn : (QuotientGroup.mk u : G ⧸ C) < QuotientGroup.mk (f ^ n * v) := by
      simpa only [← map_pow, cosetAction_mk] using hc.right_bounded n
    simpa only [map_mul, map_pow, RelIso.mul_apply] using hlift hn
  · obtain ⟨N, M, hN, hM⟩ := hc.crosses
    have hN' : (QuotientGroup.mk (f ^ N * v) : G ⧸ C) < QuotientGroup.mk w := by
      simpa only [← map_pow, cosetAction_mk] using hN
    have hM' : (QuotientGroup.mk w : G ⧸ C) < QuotientGroup.mk (g ^ M * u) := by
      simpa only [← map_pow, cosetAction_mk] using hM
    exact ⟨N, M, by simpa only [map_mul, map_pow, RelIso.mul_apply] using hlift hN',
      by simpa only [map_mul, map_pow, RelIso.mul_apply] using hlift hM'⟩

section Product
variable {ι : Type u}

noncomputable abbrev boundedSubgroup (P : PositiveCone (FreeGroup ι × Multiplicative ℤ)) :
    Subgroup (FreeGroup ι × Multiplicative ℤ) :=
  (coneLeftOrder P).centralBoundedSubgroup (cofinalProductZ (FreeGroup ι)) cofinalProductZ_central

/-- Convexity proof for the actual bounded subgroup in a restricted overgroup. -/
theorem restrictedBoundedConvex (P : PositiveCone (FreeGroup ι × Multiplicative ℤ))
    (H : Subgroup (FreeGroup ι × Multiplicative ℤ)) :
    letI := ((coneLeftOrder P).restrictSubgroup H).order
    Set.OrdConnected ((boundedSubgroup P).subgroupOf H : Set H) :=
  convex_subgroupOf (coneLeftOrder P) (boundedSubgroup P) H
    ((coneLeftOrder P).centralBoundedSubgroup_ordConnected _ cofinalProductZ_central)

variable [Nontrivial ι]

/-- Actual finite positive generation and noncofinality produce a maximal
convex jump with a crossing. All algebraic and convexity inputs are discharged. -/
theorem exists_convex_jump_crossing (P : PositiveCone (FreeGroup ι × Multiplicative ℤ))
    (hfg : SemigroupFG P.1)
    (hnon : ¬ (coneLeftOrder P).IsCofinal (cofinalProductZ (FreeGroup ι))) :
    ∃ H : Subgroup (FreeGroup ι × Multiplicative ℤ), ConeConvex P H ∧ boundedSubgroup P < H ∧
      ((boundedSubgroup P).subgroupOf H ≠ ⊤ ∧
        ∀ S : Subgroup H,
          (letI := ((coneLeftOrder P).restrictSubgroup H).order; Set.OrdConnected (S : Set H)) →
          (boundedSubgroup P).subgroupOf H < S → S = ⊤) ∧
      (let O := (coneLeftOrder P).restrictSubgroup H
       let C := (boundedSubgroup P).subgroupOf H
       letI := cosetLinearOrder O C (restrictedBoundedConvex P H)
       ∃ f g : H, ∃ u v w : H ⧸ C,
         Crossing (cosetAction O C (restrictedBoundedConvex P H) f)
           (cosetAction O C (restrictedBoundedConvex P H) g) u v w) := by
  let O := coneLeftOrder P
  let C := boundedSubgroup P
  have hC : ConeConvex P C := O.centralBoundedSubgroup_ordConnected _ cofinalProductZ_central
  have hne : C ≠ ⊤ := fun h => hnon
    ((O.isCofinal_iff_centralBoundedSubgroup_eq_top _ cofinalProductZ_central).mpr h)
  obtain ⟨H, hH, hCH, hmin⟩ := NoncofinalConvex.exists_minimal_convex_overgroup
    P (semigroupFG_finitelyDetermined P.2 hfg) C hne
  have hmax := maximal_subgroupOf_of_minimal_overgroup O C H hH hCH hmin
  refine ⟨H, hH, hCH, hmax, ?_⟩
  exact crossing_in_minimal_overgroup O C H hC hH hCH hmin
    (NoncofinalFreeTower.centralBounded_subgroupOf_not_normal P hfg H hCH)

/-- In every tight realization of the resulting restricted order, a nonfixed
component can be found beyond any prescribed bound. No collapse assumption or
minimality hypothesis is needed for this conclusion. -/
theorem exists_restricted_real_components (P : PositiveCone (FreeGroup ι × Multiplicative ℤ))
    (hfg : SemigroupFG P.1)
    (hnon : ¬ (coneLeftOrder P).IsCofinal (cofinalProductZ (FreeGroup ι))) :
    ∃ H : Subgroup (FreeGroup ι × Multiplicative ℤ), ConeConvex P H ∧ boundedSubgroup P < H ∧
      ∀ R : TightRealization ((coneLeftOrder P).restrictSubgroup H), ∀ p : ℝ,
        ∃ a : H, ∃ l t : ℝ, p < l ∧ l < t ∧ R.action a l = l ∧ R.action a t < t ∧
          Set.Ioc l t ⊆ connectedComponentIn {x : ℝ | R.action a x ≠ x} t ∧
          connectedComponentIn {x : ℝ | R.action a x ≠ x} t ⊆ Set.Ioi l := by
  obtain ⟨H, hH, hCH, hmax, f, g, u, v, w, hc⟩ := exists_convex_jump_crossing P hfg hnon
  refine ⟨H, hH, hCH, ?_⟩
  intro R p
  obtain ⟨u', v', w', hc'⟩ := crossing_in_realization ((coneLeftOrder P).restrictSubgroup H)
    ((boundedSubgroup P).subgroupOf H) (restrictedBoundedConvex P H) R hc
  exact NoncofinalRayPerturbation.crossing_component_above R.action R.no_global_fixed hc' p

/-- The realization can itself be chosen for a countable free group, making
the geometric conclusion an existence theorem rather than a vacuous statement
about realizations supplied from elsewhere. -/
theorem exists_realization_with_components [Countable ι]
    (P : PositiveCone (FreeGroup ι × Multiplicative ℤ)) (hfg : SemigroupFG P.1)
    (hnon : ¬ (coneLeftOrder P).IsCofinal (cofinalProductZ (FreeGroup ι))) :
    ∃ H : Subgroup (FreeGroup ι × Multiplicative ℤ), ConeConvex P H ∧ boundedSubgroup P < H ∧
      ∃ R : TightRealization ((coneLeftOrder P).restrictSubgroup H),
        ∀ p : ℝ, ∃ a : H, ∃ l t : ℝ, p < l ∧ l < t ∧ R.action a l = l ∧ R.action a t < t ∧
          Set.Ioc l t ⊆ connectedComponentIn {x : ℝ | R.action a x ≠ x} t ∧
          connectedComponentIn {x : ℝ | R.action a x ≠ x} t ⊆ Set.Ioi l := by
  obtain ⟨H, hH, hCH, hreal⟩ := exists_restricted_real_components P hfg hnon
  obtain ⟨g, hgH, hgC⟩ := IsConcreteLE.exists_of_lt hCH
  have hg1 : (⟨g, hgH⟩ : H) ≠ 1 := by
    intro h
    have he : g = 1 := congrArg Subtype.val h
    exact hgC (he.symm ▸ (boundedSubgroup P).one_mem)
  let : Nontrivial H := ⟨⟨⟨g, hgH⟩, 1, hg1⟩⟩
  obtain ⟨R⟩ := ((coneLeftOrder P).restrictSubgroup H).exists_tightRealization
  exact ⟨H, hH, hCH, R, hreal R⟩

end Product
end FnZPositiveCones.NoncofinalCrossingExistence
