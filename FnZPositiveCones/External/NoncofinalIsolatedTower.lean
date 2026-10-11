module

public import FnZPositiveCones.External.NoncofinalFreeTowerModel
public import FnZPositiveCones.External.InfiniteRank
public import FnZPositiveCones.External.OrderedActionsCollapse
public import FnZPositiveCones.External.NoncofinalIsolationAdapter

@[expose] public section

/-!
# The convex free-group tower under finite determination

Finite determination, rather than positive semigroup generation, passes to
the convex subgroup and the marked Nielsen–Schreier model. Infinite-rank
nonisolation then proves finite generation of these subgroups as groups.
The nontriviality of the bounded subgroup's free projection is retained as
a separate hypothesis exactly where the free normal-subgroup theorem needs
it; the trivial-projection case is not silently discharged by a stronger
finite-positive-generation result.
-/

namespace FnZPositiveCones.NoncofinalIsolatedTower

open NoncofinalConvex NoncofinalSubgroupProduct NoncofinalFreeTowerModel

universe u v
variable {G : Type u} {J : Type v} [Group G] [Group J]

/-- A finite determining set transports through the actual group isomorphism. -/
theorem transport_finitelyDetermined (P : PositiveCone G) (e : G ≃* J)
    (hfd : FinitelyDetermined P.1) : FinitelyDetermined (transportCone P e).1 := by
  classical
  obtain ⟨S, hSP, hdet⟩ := hfd
  refine ⟨S.image e, ?_, ?_⟩
  · rintro y hy
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hy
    exact (transportCone_mem P e g).mpr (hSP hg)
  · intro Q hQ hSQ
    let Q' : PositiveCone J := ⟨Q, hQ⟩
    have hback : (transportCone Q' e.symm).1 = P.1 := hdet _
      (transportCone Q' e.symm).2 (by
        intro g hg
        change e g ∈ Q
        exact hSQ (Finset.mem_image.mpr ⟨g, hg, rfl⟩))
    ext y
    change y ∈ Q ↔ e.symm y ∈ P.1
    rw [← hback]
    change y ∈ Q ↔ e (e.symm y) ∈ Q
    rw [e.apply_symm_apply]

/-- An isolated order on a free-group product forces a finite actual basis. -/
theorem finite_basis_of_finitelyDetermined {ι : Type u} {A : Type v} [Group A]
    (P : PositiveCone (FreeGroup ι × A)) (hfd : FinitelyDetermined P.1) : Finite ι := by
  rcases finite_or_infinite ι with hf | hi
  · exact hf
  · let := hi
    exact False.elim (InfiniteFreeRank.not_finitelyDetermined P.1 P.2 hfd)

/-- The marked model of every convex subgroup containing the center retains
finite determination without assuming any positive generating set. -/
theorem model_finitelyDetermined [IsFreeGroup G]
    (P : PositiveCone (G × Multiplicative ℤ)) (hfd : FinitelyDetermined P.1)
    (H : Subgroup (G × Multiplicative ℤ)) (hH : ConeConvex P H)
    (hzH : cofinalProductZ G ∈ H) : FinitelyDetermined (modelCone P H hzH).1 :=
  transport_finitelyDetermined (restrictedCone P H) (markedEquiv H hzH)
    (hH.finitelyDetermined_restrict hfd)

/-- Finite determination on a convex free-group product implies ordinary
group finite generation of that subgroup, via its checked finite free basis. -/
theorem convex_subgroup_fg [IsFreeGroup G]
    (P : PositiveCone (G × Multiplicative ℤ)) (hfd : FinitelyDetermined P.1)
    (H : Subgroup (G × Multiplicative ℤ)) (hH : ConeConvex P H)
    (hzH : cofinalProductZ G ∈ H) : H.FG := by
  let : Finite (Basis H) := finite_basis_of_finitelyDetermined (modelCone P H hzH)
    (model_finitelyDetermined P hfd H hH hzH)
  exact IsMulFG.of_surjective (markedEquiv H hzH).symm (markedEquiv H hzH).symm.surjective

/-- In particular the subgroup bounded by central powers is finitely
generated as a group. This does not assert its positive cone is generated. -/
theorem bounded_subgroup_fg [IsFreeGroup G]
    (P : PositiveCone (G × Multiplicative ℤ)) (hfd : FinitelyDetermined P.1) :
    ((coneLeftOrder P).centralBoundedSubgroup (cofinalProductZ G) cofinalProductZ_central).FG :=
  convex_subgroup_fg P hfd _
    ((coneLeftOrder P).centralBoundedSubgroup_ordConnected _ cofinalProductZ_central)
    (central_mem_bounded (coneLeftOrder P))

/-- Actual nonnormality inside the overgroup follows from finite
determination and a nontrivial lower free projection. -/
theorem bounded_subgroupOf_not_normal [IsFreeGroup G]
    (P : PositiveCone (G × Multiplicative ℤ)) (hfd : FinitelyDetermined P.1)
    (H : Subgroup (G × Multiplicative ℤ))
    (hCH : (coneLeftOrder P).centralBoundedSubgroup
      (cofinalProductZ G) cofinalProductZ_central < H)
    (hne : projection ((coneLeftOrder P).centralBoundedSubgroup
      (cofinalProductZ G) cofinalProductZ_central) ≠ ⊥) :
    ¬ (((coneLeftOrder P).centralBoundedSubgroup
      (cofinalProductZ G) cofinalProductZ_central).subgroupOf H).Normal := by
  have hz := central_mem_bounded (coneLeftOrder P)
  exact NoncofinalFreeTower.subgroupOf_not_normal _ H hz hCH.le
    (bounded_subgroup_fg P hfd) hne
    (NoncofinalFreeTower.relative_bounded_index_zero (coneLeftOrder P) H (hCH.le hz) hCH)

/-- The minimal-overgroup model carries isolation itself and a finite actual
free basis. No field asserts finite generation of the positive semigroup. -/
structure Model {ι : Type u} (P : PositiveCone (FreeGroup ι × Multiplicative ℤ)) where
  H : Subgroup (FreeGroup ι × Multiplicative ℤ)
  center_mem : cofinalProductZ (FreeGroup ι) ∈ H
  convex : ConeConvex P H
  strict_overgroup : (coneLeftOrder P).centralBoundedSubgroup
    (cofinalProductZ (FreeGroup ι)) cofinalProductZ_central < H
  cone_fd : FinitelyDetermined (modelCone P H center_mem).1
  finite_basis : Finite (Basis H)
  center_not_cofinal : ¬ (coneLeftOrder (modelCone P H center_mem)).IsCofinal
    (cofinalProductZ (FreeGroup (Basis H)))
  bounded_maximal : ∀ L : Subgroup (FreeGroup (Basis H) × Multiplicative ℤ),
    ConeConvex (modelCone P H center_mem) L →
    (coneLeftOrder (modelCone P H center_mem)).centralBoundedSubgroup
      (cofinalProductZ (FreeGroup (Basis H))) cofinalProductZ_central < L → L = ⊤

/-- Finite determination supplies the actual convex jump, restricted cone,
marked product equivalence and finite basis before any nonnormality input. -/
theorem exists_model {ι : Type u}
    (P : PositiveCone (FreeGroup ι × Multiplicative ℤ)) (hfd : FinitelyDetermined P.1)
    (hnon : ¬ (coneLeftOrder P).IsCofinal (cofinalProductZ (FreeGroup ι))) :
    Nonempty (Model P) := by
  let O := coneLeftOrder P
  let C := O.centralBoundedSubgroup (cofinalProductZ (FreeGroup ι)) cofinalProductZ_central
  have hC : ConeConvex P C := O.centralBoundedSubgroup_ordConnected _ cofinalProductZ_central
  have hne : C ≠ ⊤ := by
    intro he
    exact hnon ((O.isCofinal_iff_centralBoundedSubgroup_eq_top _ cofinalProductZ_central).mpr he)
  obtain ⟨H, hH, hCH, _, _, hmax⟩ :=
    NoncofinalConvexJumpAdapter.exists_maximal_convex_restriction P hfd C hC hne
  have hzH := hCH.le (central_mem_bounded O)
  have hfdH := model_finitelyDetermined P hfd H hH hzH
  exact ⟨{
    H := H
    center_mem := hzH
    convex := hH
    strict_overgroup := hCH
    cone_fd := hfdH
    finite_basis := finite_basis_of_finitelyDetermined _ hfdH
    center_not_cofinal := model_not_cofinal P H hzH hCH
    bounded_maximal := model_maximal P H hzH hmax }⟩

/-- The model has an isolated cone in the actual sign topology. -/
theorem Model.isolated {ι : Type u} {P : PositiveCone (FreeGroup ι × Multiplicative ℤ)}
    (M : Model P) : IsOpen ({modelCone P M.H M.center_mem} :
      Set (PositiveCone (FreeGroup (Basis M.H) × Multiplicative ℤ))) :=
  (finiteDetermination_iff_isolated _).mp M.cone_fd

/-- The bounded subgroup of the model remains proper. -/
theorem Model.bounded_ne_top {ι : Type u} {P : PositiveCone (FreeGroup ι × Multiplicative ℤ)}
    (M : Model P) :
    (coneLeftOrder (modelCone P M.H M.center_mem)).centralBoundedSubgroup
      (cofinalProductZ (FreeGroup (Basis M.H))) cofinalProductZ_central ≠ ⊤ := by
  intro he
  exact M.center_not_cofinal ((LeftGroupOrder.isCofinal_iff_centralBoundedSubgroup_eq_top
    (coneLeftOrder (modelCone P M.H M.center_mem)) _ cofinalProductZ_central).mpr he)

/-- Nonnormality transports from the actual restricted subgroup tower, not
from a claim about normality in the original ambient group. -/
theorem Model.bounded_not_normal {ι : Type u} {P : PositiveCone (FreeGroup ι × Multiplicative ℤ)}
    (M : Model P) (hfd : FinitelyDetermined P.1)
    (hne : projection ((coneLeftOrder P).centralBoundedSubgroup
      (cofinalProductZ (FreeGroup ι)) cofinalProductZ_central) ≠ ⊥) :
    ¬ ((coneLeftOrder (modelCone P M.H M.center_mem)).centralBoundedSubgroup
      (cofinalProductZ (FreeGroup (Basis M.H))) cofinalProductZ_central).Normal := by
  rw [model_bounded]
  intro hn
  apply bounded_subgroupOf_not_normal P hfd M.H M.strict_overgroup hne
  exact Subgroup.Normal.of_map_injective (markedEquiv M.H M.center_mem).injective hn

/-- A finite actual free basis together with nonnormality rules out rank
zero or one without assuming a rank formula for a chosen free instance. -/
theorem Model.basis_nontrivial {ι : Type u} {P : PositiveCone (FreeGroup ι × Multiplicative ℤ)}
    (M : Model P) (hfd : FinitelyDetermined P.1)
    (hne : projection ((coneLeftOrder P).centralBoundedSubgroup
      (cofinalProductZ (FreeGroup ι)) cofinalProductZ_central) ≠ ⊥) : Nontrivial (Basis M.H) := by
  classical
  by_contra hn
  have : Subsingleton (Basis M.H) := not_nontrivial_iff_subsingleton.mp hn
  have hcyclic : IsCyclic (FreeGroup (Basis M.H)) := by
    cases isEmpty_or_nonempty (Basis M.H) with
    | inl he => have : IsEmpty (Basis M.H) := he; infer_instance
    | inr hn =>
      let : Unique (Basis M.H) := ⟨⟨Classical.choice hn⟩, fun _ => Subsingleton.elim _ _⟩
      infer_instance
  let := hcyclic
  have hcomm : IsMulCommutative (FreeGroup (Basis M.H) × Multiplicative ℤ) := inferInstance
  let := hcomm
  exact M.bounded_not_normal hfd hne inferInstance

/-- With the remaining nontrivial-projection input explicit, the isolated
convex-jump model has the full minimal factor used in the perturbation proof.
The central action in this factor is proved to be the identity. -/
theorem Model.exists_minimal_factor {ι : Type u}
    {P : PositiveCone (FreeGroup ι × Multiplicative ℤ)}
    (M : Model P) (hfd : FinitelyDetermined P.1)
    (hne : projection ((coneLeftOrder P).centralBoundedSubgroup
      (cofinalProductZ (FreeGroup ι)) cofinalProductZ_central) ≠ ⊥)
    (R : TightRealization (coneLeftOrder (modelCone P M.H M.center_mem))) :
    ∃ σ : (FreeGroup (Basis M.H) × Multiplicative ℤ) →* (ℝ ≃o ℝ), ∃ p : ℝ → ℝ,
      Monotone p ∧ Continuous p ∧ Function.Surjective p ∧
      (∀ g t, p (R.action g t) = σ g (p t)) ∧
      σ (cofinalProductZ (FreeGroup (Basis M.H))) = 1 ∧
      (∀ t, DenseRange (fun g => σ g t)) ∧
      ∃ f g u v w, NoncofinalCrossings.Crossing (σ f) (σ g) u v w := by
  let := M.finite_basis
  let O := coneLeftOrder (modelCone P M.H M.center_mem)
  let C := O.centralBoundedSubgroup (cofinalProductZ (FreeGroup (Basis M.H)))
    cofinalProductZ_central
  obtain ⟨σ, y, p, hm, hc, hs, he, _, hstab, hmin, hcross⟩ :=
    NoncofinalMinimalAction.exists_minimal_factor O R C
      (O.centralBoundedSubgroup_ordConnected _ cofinalProductZ_central)
      M.bounded_ne_top M.bounded_maximal (M.bounded_not_normal hfd hne)
  refine ⟨σ, p, hm, hc, hs, he, ?_, hmin, hcross⟩
  exact NoncofinalMinimalAction.central_eq_one_of_fixed_dense σ _
    (fun g => (cofinalProductZ_central g).eq) y
    ((hstab _).mp (central_mem_bounded O)) (hmin y)

/-- The finite-basis model admits the checked tight realization without a
countability assumption on the original ambient free basis. -/
theorem Model.exists_tightRealization {ι : Type u}
    {P : PositiveCone (FreeGroup ι × Multiplicative ℤ)} (M : Model P) :
    Nonempty (TightRealization (coneLeftOrder (modelCone P M.H M.center_mem))) := by
  let := M.finite_basis
  exact LeftGroupOrder.exists_tightRealization _

/-- The tower and minimal-factor constructions now discharge every input to
the second-alternative adapter. What remains is precisely a primitive
depending on the bound, not an unbounded fixed set for one chosen generator. -/
theorem Model.primitive_fixed_above {ι : Type u}
    {P : PositiveCone (FreeGroup ι × Multiplicative ℤ)}
    (M : Model P) (hfd : FinitelyDetermined P.1)
    (hne : projection ((coneLeftOrder P).centralBoundedSubgroup
      (cofinalProductZ (FreeGroup ι)) cofinalProductZ_central) ≠ ⊥)
    (R : TightRealization (coneLeftOrder (modelCone P M.H M.center_mem))) (b : ℝ) :
    ∃ a : FreeGroup (Basis M.H), NoncofinalPrimitiveEntry.IsPrimitive a ∧
      ∃ y : ℝ, b < y ∧ R.action (a, 1) y = y := by
  let := M.basis_nontrivial hfd hne
  obtain ⟨σ, p, hm, hc, hs, he, hz, hmin, f, g, u, v, w, hcross⟩ :=
    M.exists_minimal_factor hfd hne R
  have hx : R.action (cofinalProductZ (FreeGroup (Basis M.H))) R.base ≠ R.base := by
    intro h
    have heq : cofinalProductZ (FreeGroup (Basis M.H)) = 1 := R.orbit_injective
      (by simpa only [map_one, RelIso.one_apply] using h)
    have hh := congrArg (fun g : FreeGroup (Basis M.H) × Multiplicative ℤ => g.2.toAdd) heq
    norm_num [cofinalProductZ] at hh
  exact NoncofinalIsolationAdapter.isolated_factor_crossing_primitive_fixed_above
    _ R.action σ R.base R.order_iff R.no_global_fixed hx p hm hc hs he hz hmin hcross
    ((finiteDetermination_iff_leftOrder_isolated _).mp M.cone_fd) b

end FnZPositiveCones.NoncofinalIsolatedTower
