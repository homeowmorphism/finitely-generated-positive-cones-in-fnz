module

public import FnZPositiveCones.External.NoncofinalConvexJumpAdapter
public import FnZPositiveCones.External.NoncofinalQuotientCone
public import FnZPositiveCones.External.NoncofinalFreeTower

@[expose] public section

/-! Marked free-product models for the minimal noncofinal convex overgroup. -/

namespace FnZPositiveCones
namespace NoncofinalFreeTowerModel

open NoncofinalSubgroupProduct NoncofinalConvex
universe u v
variable {G : Type u} {J : Type v} [Group G] [Group J]

/-- Transport by an isomorphism, expressed as pullback along the explicit
inverse so that every transported sign has a direct membership test. -/
def transportCone (P : PositiveCone G) (e : G ≃* J) : PositiveCone J :=
  ⟨Subsemigroup.comap e.symm.toMonoidHom.toMulHom P.1, by
    have h := positiveCone_transport e P.2
    change IsPositiveCone (Subsemigroup.map (e : G →ₙ* J) P.1) at h
    rwa [Subsemigroup.map_equiv_eq_comap_symm] at h⟩

@[simp] theorem transportCone_mem (P : PositiveCone G) (e : G ≃* J) (g : G) :
    e g ∈ (transportCone P e).1 ↔ g ∈ P.1 := by
  change e.symm (e g) ∈ P.1 ↔ g ∈ P.1
  rw [e.symm_apply_apply]

theorem transportCone_semigroupFG (P : PositiveCone G) (e : G ≃* J)
    (hfg : SemigroupFG P.1) : SemigroupFG (transportCone P e).1 := by
  have h := semigroupFG_transport e hfg
  change SemigroupFG (Subsemigroup.map (e : G →ₙ* J) P.1) at h
  rwa [Subsemigroup.map_equiv_eq_comap_symm] at h

/-- All weak comparisons are transported by the same isomorphism. -/
theorem transportCone_le (P : PositiveCone G) (e : G ≃* J) (x y : J) :
    (coneLeftOrder (transportCone P e)).order.le x y ↔
      (coneLeftOrder P).order.le (e.symm x) (e.symm y) := by
  change (x = y ∨ e.symm (x⁻¹ * y) ∈ P.1) ↔
    (e.symm x = e.symm y ∨ (e.symm x)⁻¹ * e.symm y ∈ P.1)
  rw [e.symm.injective.eq_iff, e.symm.map_mul, e.symm.map_inv]

/-- The group equivalence is simultaneously an order equivalence. -/
noncomputable def coneOrderIso (P : PositiveCone G) (e : G ≃* J) :
    let := coneLinearOrder P
    let := coneLinearOrder (transportCone P e)
    G ≃o J := by
  let := coneLinearOrder P
  let := coneLinearOrder (transportCone P e)
  exact { e.toEquiv with
    map_rel_iff' := by
      intro a b
      change (coneLeftOrder (transportCone P e)).order.le (e a) (e b) ↔
        (coneLeftOrder P).order.le a b
      simpa only [e.symm_apply_apply] using transportCone_le P e (e a) (e b) }

/-- Convexity passes to the exact image subgroup. -/
theorem convex_transport (P : PositiveCone G) (e : G ≃* J) (K : Subgroup G)
    (hK : ConeConvex P K) : ConeConvex (transportCone P e) (K.map e.toMonoidHom) := by
  let := coneLinearOrder P
  let := coneLinearOrder (transportCone P e)
  let : Set.OrdConnected (K : Set G) := hK
  exact Set.ordConnected_image (coneOrderIso P e)

/-- Convexity also pulls back to the source subgroup. -/
theorem convex_comap (P : PositiveCone G) (e : G ≃* J) (K : Subgroup J)
    (hK : ConeConvex (transportCone P e) K) : ConeConvex P (K.comap e.toMonoidHom) := by
  let := coneLinearOrder P
  let := coneLinearOrder (transportCone P e)
  let : Set.OrdConnected (K : Set J) := hK
  exact Set.ordConnected_preimage (coneOrderIso P e)

/-- Cofinality is preserved, with the marked element itself transported. -/
theorem cofinal_transport (P : PositiveCone G) (e : G ≃* J) (z : G) :
    (coneLeftOrder (transportCone P e)).IsCofinal (e z) ↔ (coneLeftOrder P).IsCofinal z := by
  constructor
  · intro h g
    obtain ⟨m, n, hm, hn⟩ := h (e g)
    refine ⟨m, n, ?_, ?_⟩
    · simpa only [transportCone_le, ← map_zpow, e.symm_apply_apply] using hm
    · simpa only [transportCone_le, ← map_zpow, e.symm_apply_apply] using hn
  · intro h g
    obtain ⟨m, n, hm, hn⟩ := h (e.symm g)
    refine ⟨m, n, ?_, ?_⟩
    · simpa only [transportCone_le, ← map_zpow, e.symm_apply_apply] using hm
    · simpa only [transportCone_le, ← map_zpow, e.symm_apply_apply] using hn

/-- Maximal proper convexity is preserved as a statement about exact subgroup images. -/
theorem maximal_transport (P : PositiveCone G) (e : G ≃* J) (K : Subgroup G)
    (hmax : ∀ L : Subgroup G, ConeConvex P L → K < L → L = ⊤) :
    ∀ L : Subgroup J, ConeConvex (transportCone P e) L → K.map e.toMonoidHom < L → L = ⊤ := by
  intro L hL hKL
  have hlt : K < L.comap e.toMonoidHom := by
    constructor
    · intro k hk
      exact hKL.le ⟨k, hk, rfl⟩
    · intro hback
      apply hKL.not_ge
      intro l hl
      exact ⟨e.symm l, hback (by simpa using hl), e.apply_symm_apply l⟩
  have he := hmax (L.comap e.toMonoidHom) (convex_comap P e L hL) hlt
  apply top_unique
  intro l _
  have hm : e.symm l ∈ L.comap e.toMonoidHom := by rw [he]; trivial
  simpa using hm

/-- The bounded subgroup is transported as the exact subgroup image. -/
theorem bounded_transport (P : PositiveCone G) (e : G ≃* J) (z : G) (w : J)
    (he : e z = w) (hz : ∀ g, Commute z g) (hw : ∀ j, Commute w j) :
    (coneLeftOrder (transportCone P e)).centralBoundedSubgroup w hw =
      ((coneLeftOrder P).centralBoundedSubgroup z hz).map e.toMonoidHom := by
  ext x
  rw [Subgroup.mem_map_equiv]
  simp only [LeftGroupOrder.mem_centralBoundedSubgroup, transportCone_le,
    ← he, ← map_zpow, e.symm_apply_apply]

/-- Cone restriction and order restriction give the same bundled left order. -/
theorem restrictedOrder_eq (P : PositiveCone G) (H : Subgroup G) :
    coneLeftOrder (restrictedCone P H) = (coneLeftOrder P).restrictSubgroup H := by
  have ho : (coneLeftOrder (restrictedCone P H)).order =
      ((coneLeftOrder P).restrictSubgroup H).order := by
    apply LinearOrder.ext_lt
    intro a b
    rfl
  have hext : ∀ (A B : LeftGroupOrder H), A.order = B.order → A = B := by
    rintro ⟨A, hA⟩ ⟨B, hB⟩ h
    cases h
    rfl
  exact hext _ _ ho

section FreeModel
variable [IsFreeGroup G]

/-- The actual Nielsen–Schreier basis chosen for the first projection. -/
abbrev Basis (H : Subgroup (G × Multiplicative ℤ)) := IsFreeGroup.Generators (projection H)

/-- Explicit marked product isomorphism: first split off the integer factor,
then apply the checked Nielsen–Schreier free-basis equivalence. -/
noncomputable def markedEquiv (H : Subgroup (G × Multiplicative ℤ))
    (hzH : cofinalProductZ G ∈ H) : H ≃* FreeGroup (Basis H) × Multiplicative ℤ :=
  (productEquiv H hzH).trans ((IsFreeGroup.toFreeGroup (projection H)).prodCongr
    (MulEquiv.refl (Multiplicative ℤ)))

@[simp] theorem markedEquiv_center (H : Subgroup (G × Multiplicative ℤ))
    (hzH : cofinalProductZ G ∈ H) :
    markedEquiv H hzH (NoncofinalFreeTower.centerIn H hzH) = cofinalProductZ (FreeGroup (Basis H)) := by
  change ((IsFreeGroup.toFreeGroup (projection H)).prodCongr
    (MulEquiv.refl (Multiplicative ℤ))) (productEquiv H hzH
      (NoncofinalFreeTower.centerIn H hzH)) = _
  rw [NoncofinalFreeTower.productEquiv_centerIn]
  apply Prod.ext
  · change (IsFreeGroup.toFreeGroup (projection H)) 1 = 1
    exact map_one _
  · rfl

/-- The actual cone on the marked free-product model. -/
noncomputable def modelCone (P : PositiveCone (G × Multiplicative ℤ))
    (H : Subgroup (G × Multiplicative ℤ)) (hzH : cofinalProductZ G ∈ H) :
    PositiveCone (FreeGroup (Basis H) × Multiplicative ℤ) :=
  transportCone (restrictedCone P H) (markedEquiv H hzH)

theorem modelCone_semigroupFG (P : PositiveCone (G × Multiplicative ℤ))
    (hfg : SemigroupFG P.1) (H : Subgroup (G × Multiplicative ℤ))
    (hzH : cofinalProductZ G ∈ H) (hH : ConeConvex P H) :
    SemigroupFG (modelCone P H hzH).1 :=
  transportCone_semigroupFG _ _ (hH.semigroupFG_restrict hfg)

/-- Countability is inherited from the original group, not postulated for the
chosen Nielsen–Schreier basis. -/
theorem basis_countable [Countable G] (H : Subgroup (G × Multiplicative ℤ)) :
    Countable (Basis H) := by
  let e := IsFreeGroup.toFreeGroup (projection H)
  exact Function.Injective.countable (e.symm.injective.comp FreeGroup.of_injective)

/-- The subgroup bounded by central powers on the model is exactly the image
of the original subgroup-of tower. -/
theorem model_bounded (P : PositiveCone (G × Multiplicative ℤ))
    (H : Subgroup (G × Multiplicative ℤ)) (hzH : cofinalProductZ G ∈ H) :
    (coneLeftOrder (modelCone P H hzH)).centralBoundedSubgroup
        (cofinalProductZ (FreeGroup (Basis H))) cofinalProductZ_central =
      (((coneLeftOrder P).centralBoundedSubgroup (cofinalProductZ G)
        cofinalProductZ_central).subgroupOf H).map (markedEquiv H hzH).toMonoidHom := by
  rw [modelCone, bounded_transport _ _ (NoncofinalFreeTower.centerIn H hzH) _
    (markedEquiv_center H hzH) (NoncofinalFreeTower.centerIn_central H hzH)
    cofinalProductZ_central, restrictedOrder_eq, NoncofinalFreeTower.centralBounded_restrict]

/-- Noncofinality persists after restriction and the marked product equivalence. -/
theorem model_not_cofinal (P : PositiveCone (G × Multiplicative ℤ))
    (H : Subgroup (G × Multiplicative ℤ)) (hzH : cofinalProductZ G ∈ H)
    (hCH : (coneLeftOrder P).centralBoundedSubgroup
      (cofinalProductZ G) cofinalProductZ_central < H) :
    ¬ (coneLeftOrder (modelCone P H hzH)).IsCofinal (cofinalProductZ (FreeGroup (Basis H))) := by
  rw [← markedEquiv_center H hzH, modelCone, cofinal_transport, restrictedOrder_eq]
  exact NoncofinalFreeTower.restricted_not_cofinal _ H hzH hCH

end FreeModel

/-- A basis with at most one generator makes its free group cyclic, including
the empty-basis case. -/
private theorem free_isCyclic_of_subsingleton {α : Type u} [Subsingleton α] :
    IsCyclic (FreeGroup α) := by
  classical
  cases isEmpty_or_nonempty α with
  | inl he => have : IsEmpty α := he; infer_instance
  | inr hn =>
    let : Unique α := ⟨⟨Classical.choice hn⟩, fun _ => Subsingleton.elim _ _⟩
    infer_instance

/-- The marked model has at least two free generators. If its basis had size
at most one, the nontrivial lower projection would have finite index in a
cyclic group, contradicting its checked relative index zero. -/
theorem basis_nontrivial {ι : Type u} [Nontrivial ι]
    (P : PositiveCone (FreeGroup ι × Multiplicative ℤ)) (hfg : SemigroupFG P.1)
    (H : Subgroup (FreeGroup ι × Multiplicative ℤ))
    (hCH : (coneLeftOrder P).centralBoundedSubgroup
      (cofinalProductZ (FreeGroup ι)) cofinalProductZ_central < H) : Nontrivial (Basis H) := by
  classical
  by_contra hn
  have : Subsingleton (Basis H) := not_nontrivial_iff_subsingleton.mp hn
  have : IsCyclic (FreeGroup (Basis H)) := free_isCyclic_of_subsingleton
  have : IsCyclic (projection H) := (IsFreeGroup.toFreeGroup (projection H)).isCyclic.mpr this
  let O := coneLeftOrder P
  let C := O.centralBoundedSubgroup (cofinalProductZ (FreeGroup ι)) cofinalProductZ_central
  have hz : cofinalProductZ (FreeGroup ι) ∈ C := central_mem_bounded O
  have hne := NoncofinalFreeTower.relative_projection_ne_bot C H hCH.le
    (NoncofinalQuotientCone.bounded_projection_ne_bot P hfg)
  have hi := NoncofinalFreeTower.relative_bounded_index_zero O H (hCH.le hz) hCH
  exact NoncofinalFreeTower.cyclic_index_ne_zero _ hne
    ((NoncofinalFreeTower.relative_projection_index C H hz hCH.le).trans hi)

/-- Maximal convexity of the original subgroup tower survives the marked model. -/
theorem model_maximal {ι : Type u}
    (P : PositiveCone (FreeGroup ι × Multiplicative ℤ))
    (H : Subgroup (FreeGroup ι × Multiplicative ℤ)) (hzH : cofinalProductZ (FreeGroup ι) ∈ H)
    (hmax : ∀ K : Subgroup H,
      (letI := ((coneLeftOrder P).restrictSubgroup H).order; Set.OrdConnected (K : Set H)) →
      ((coneLeftOrder P).centralBoundedSubgroup
        (cofinalProductZ (FreeGroup ι)) cofinalProductZ_central).subgroupOf H < K → K = ⊤) :
    ∀ L : Subgroup (FreeGroup (Basis H) × Multiplicative ℤ), ConeConvex (modelCone P H hzH) L →
      (coneLeftOrder (modelCone P H hzH)).centralBoundedSubgroup
        (cofinalProductZ (FreeGroup (Basis H))) cofinalProductZ_central < L → L = ⊤ := by
  intro L hL hlt
  rw [model_bounded] at hlt
  apply maximal_transport (restrictedCone P H) (markedEquiv H hzH) _ _ L hL hlt
  intro K hK hCK
  apply hmax K _ hCK
  have hK' : (letI := (coneLeftOrder (restrictedCone P H)).order;
      Set.OrdConnected (K : Set H)) := hK
  rwa [restrictedOrder_eq] at hK'

/-- A complete marked model of the minimal convex overgroup. Every field is
proved from the original cone in `exists_model`; none is an external dynamical
assumption. The basis is the chosen Nielsen–Schreier basis of `projection H`. -/
structure Model {ι : Type u} (P : PositiveCone (FreeGroup ι × Multiplicative ℤ)) where
  H : Subgroup (FreeGroup ι × Multiplicative ℤ)
  center_mem : cofinalProductZ (FreeGroup ι) ∈ H
  convex : ConeConvex P H
  strict_overgroup : (coneLeftOrder P).centralBoundedSubgroup
    (cofinalProductZ (FreeGroup ι)) cofinalProductZ_central < H
  basis_nontrivial : Nontrivial (Basis H)
  cone_fg : SemigroupFG (modelCone P H center_mem).1
  center_not_cofinal : ¬ (coneLeftOrder (modelCone P H center_mem)).IsCofinal
    (cofinalProductZ (FreeGroup (Basis H)))
  bounded_maximal : ∀ L : Subgroup (FreeGroup (Basis H) × Multiplicative ℤ),
    ConeConvex (modelCone P H center_mem) L →
    (coneLeftOrder (modelCone P H center_mem)).centralBoundedSubgroup
      (cofinalProductZ (FreeGroup (Basis H))) cofinalProductZ_central < L → L = ⊤

/-- From a noncofinal finitely generated cone, obtain an actual marked free
product with a maximal proper convex bounded subgroup. -/
theorem exists_model {ι : Type u} [Nontrivial ι]
    (P : PositiveCone (FreeGroup ι × Multiplicative ℤ)) (hfg : SemigroupFG P.1)
    (hnon : ¬ (coneLeftOrder P).IsCofinal (cofinalProductZ (FreeGroup ι))) : Nonempty (Model P) := by
  let O := coneLeftOrder P
  let C := O.centralBoundedSubgroup (cofinalProductZ (FreeGroup ι)) cofinalProductZ_central
  have hC : ConeConvex P C := O.centralBoundedSubgroup_ordConnected _ cofinalProductZ_central
  have hne : C ≠ ⊤ := by
    intro he
    exact hnon ((O.isCofinal_iff_centralBoundedSubgroup_eq_top _ cofinalProductZ_central).mpr he)
  obtain ⟨H, hH, hCH, _, _, hmax⟩ :=
    NoncofinalConvexJumpAdapter.exists_maximal_convex_restriction P
      (semigroupFG_finitelyDetermined P.2 hfg) C hC hne
  have hzH := hCH.le (central_mem_bounded O)
  exact ⟨{
    H := H
    center_mem := hzH
    convex := hH
    strict_overgroup := hCH
    basis_nontrivial := basis_nontrivial P hfg H hCH
    cone_fg := modelCone_semigroupFG P hfg H hzH hH
    center_not_cofinal := model_not_cofinal P H hzH hCH
    bounded_maximal := model_maximal P H hzH hmax }⟩

/-- Countability of every constructed model follows from countability of the
original free basis; in particular it applies to each original `Fin n`. -/
theorem Model.countable_basis {ι : Type u} [Countable ι]
    {P : PositiveCone (FreeGroup ι × Multiplicative ℤ)} (M : Model P) : Countable (Basis M.H) :=
  basis_countable M.H

/-- The bounded subgroup in the model remains proper. -/
theorem Model.bounded_ne_top {ι : Type u}
    {P : PositiveCone (FreeGroup ι × Multiplicative ℤ)} (M : Model P) :
    (coneLeftOrder (modelCone P M.H M.center_mem)).centralBoundedSubgroup
      (cofinalProductZ (FreeGroup (Basis M.H))) cofinalProductZ_central ≠ ⊤ := by
  intro he
  exact M.center_not_cofinal ((LeftGroupOrder.isCofinal_iff_centralBoundedSubgroup_eq_top
    (coneLeftOrder (modelCone P M.H M.center_mem)) _ cofinalProductZ_central).mpr he)

/-- Positivity of the original marked center is unchanged in the model. -/
theorem Model.center_positive {ι : Type u}
    {P : PositiveCone (FreeGroup ι × Multiplicative ℤ)} (M : Model P)
    (hz : (coneLeftOrder P).order.lt 1 (cofinalProductZ (FreeGroup ι))) :
    (coneLeftOrder (modelCone P M.H M.center_mem)).order.lt 1
      (cofinalProductZ (FreeGroup (Basis M.H))) := by
  rw [coneLeftOrder_lt, inv_one, one_mul, ← markedEquiv_center M.H M.center_mem]
  apply (transportCone_mem (restrictedCone P M.H) (markedEquiv M.H M.center_mem) _).mpr
  change cofinalProductZ (FreeGroup ι) ∈ P.1
  simpa only [coneLeftOrder_lt, inv_one, one_mul] using hz

/-- The maximal proper bounded subgroup of the marked model is nonnormal. -/
theorem Model.bounded_not_normal {ι : Type u}
    {P : PositiveCone (FreeGroup ι × Multiplicative ℤ)} (M : Model P) :
    ¬ ((coneLeftOrder (modelCone P M.H M.center_mem)).centralBoundedSubgroup
      (cofinalProductZ (FreeGroup (Basis M.H))) cofinalProductZ_central).Normal := by
  have := M.basis_nontrivial
  exact NoncofinalQuotientCone.bounded_not_normal_of_semigroupFG _ M.cone_fg M.center_not_cofinal

end NoncofinalFreeTowerModel
end FnZPositiveCones
