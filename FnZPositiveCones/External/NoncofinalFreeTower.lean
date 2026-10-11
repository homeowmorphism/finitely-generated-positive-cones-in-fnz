module

public import FnZPositiveCones.External.NoncofinalSubgroupProduct
public import FnZPositiveCones.External.NoncofinalQuotientCone
public import Mathlib.GroupTheory.FreeGroup.NielsenSchreier

@[expose] public section

/-! Exact subgroup-tower algebra for the noncofinal convex jump. -/

namespace FnZPositiveCones
namespace NoncofinalFreeTower

open NoncofinalSubgroupProduct
universe u
variable {G : Type u} [Group G]

/-- A nontrivial subgroup of a cyclic group has finite index. -/
theorem cyclic_index_ne_zero [IsCyclic G] (K : Subgroup G) (hne : K ≠ ⊥) : K.index ≠ 0 := by
  intro hi
  apply hne
  apply bot_unique
  apply IsCyclic.subgroup_le_iff_index_dvd.mpr
  rw [hi]
  exact dvd_zero _

/-- Include rank zero and rank one explicitly in the free normal-subgroup theorem. -/
theorem free_index_ne_zero {ι : Type u} (K : Subgroup (FreeGroup ι)) [K.Normal]
    (hfg : K.FG) (hne : K ≠ ⊥) : K.index ≠ 0 := by
  classical
  by_cases h : Nontrivial ι
  · exact NoncofinalFreeSubgroup.index_ne_zero_of_fg_normal K hfg hne
  have : Subsingleton ι := not_nontrivial_iff_subsingleton.mp h
  cases isEmpty_or_nonempty ι with
  | inl he =>
    have : IsEmpty ι := he
    exact cyclic_index_ne_zero K hne
  | inr hn =>
    let : Unique ι := ⟨⟨Classical.choice hn⟩, fun _ => Subsingleton.elim _ _⟩
    exact cyclic_index_ne_zero K hne

/-- The checked normal-subgroup obstruction transports through an explicit
Nielsen–Schreier basis, without any rank assumption. -/
theorem isFree_index_ne_zero [IsFreeGroup G] (K : Subgroup G) [K.Normal]
    (hfg : K.FG) (hne : K ≠ ⊥) : K.index ≠ 0 := by
  let e := IsFreeGroup.toFreeGroup G
  have hmap : (K.map e.toMonoidHom).Normal :=
    (inferInstance : K.Normal).map e.toMonoidHom e.surjective
  have hmapfg : (K.map e.toMonoidHom).FG := by infer_instance
  have hmapne : K.map e.toMonoidHom ≠ ⊥ := by
    intro he
    apply hne
    apply (Subgroup.eq_bot_iff_forall _).mpr
    intro k hk
    have hmem : e k ∈ K.map e.toMonoidHom := ⟨k, hk, rfl⟩
    rw [he] at hmem
    exact e.injective (by simpa using hmem)
  have hn := free_index_ne_zero (K.map e.toMonoidHom) hmapfg hmapne
  have heq : (K.map e.toMonoidHom).index = K.index := K.index_map_equiv e
  exact fun hi => hn (heq.trans hi)

/-- First projection with its codomain restricted to the actual projected subgroup. -/
def projectionHom (H : Subgroup (G × Multiplicative ℤ)) : H →* projection H where
  toFun h := ⟨h.1.1, ⟨h.1, h.2, rfl⟩⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem projectionHom_surjective (H : Subgroup (G × Multiplicative ℤ)) :
    Function.Surjective (projectionHom H) := by
  rintro ⟨g, ⟨h, hh, he⟩⟩
  exact ⟨⟨h, hh⟩, Subtype.ext he⟩

/-- Image of the lower subgroup in the restricted projection is precisely the
subgroup-of construction on the two projected subgroups. -/
theorem projectionHom_map_subgroupOf (C H : Subgroup (G × Multiplicative ℤ))
    (hCH : C ≤ H) :
    (C.subgroupOf H).map (projectionHom H) = (projection C).subgroupOf (projection H) := by
  ext g
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact ⟨h.1, hh, rfl⟩
  · rintro ⟨c, hc, he⟩
    exact ⟨⟨c, hCH hc⟩, hc, Subtype.ext he⟩

/-- The lower subgroup in the actual tower decomposes into the corresponding
projected subgroup tower and the unchanged integer factor. -/
def relativeProductEquiv (C H : Subgroup (G × Multiplicative ℤ))
    (hz : cofinalProductZ G ∈ C) (hCH : C ≤ H) :
    C.subgroupOf H ≃* (projection C).subgroupOf (projection H) × Multiplicative ℤ :=
  (Subgroup.subgroupOfEquivOfLe hCH).trans ((productEquiv C hz).trans
    ((Subgroup.subgroupOfEquivOfLe (Subgroup.map_mono hCH)).symm.prodCongr
      (MulEquiv.refl (Multiplicative ℤ))))

/-- The ambient product equivalence identifies the lower subgroup as the exact
product subgroup, rather than just an abstract isomorphic group. -/
theorem productEquiv_map_subgroupOf (C H : Subgroup (G × Multiplicative ℤ))
    (hz : cofinalProductZ G ∈ C) (hCH : C ≤ H) :
    (C.subgroupOf H).map (productEquiv H (hCH hz)).toMonoidHom =
      ((projection C).subgroupOf (projection H)).prod ⊤ := by
  ext g
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact ⟨⟨h.1, hh, rfl⟩, trivial⟩
  · intro hg
    refine ⟨(productEquiv H (hCH hz)).symm g, ?_, by simp⟩
    change (g.1.1, g.2) ∈ C
    exact (mem_iff_projection C hz _ _).mpr hg.1

/-- The kernel of the restricted projection lies in the lower subgroup. -/
theorem projectionHom_ker_le (C H : Subgroup (G × Multiplicative ℤ))
    (hz : cofinalProductZ G ∈ C) : (projectionHom H).ker ≤ C.subgroupOf H := by
  intro h hh
  have he : h.1.1 = 1 := congrArg Subtype.val hh
  have hm := central_factor_mem C hz h.1.2
  change h.1 ∈ C
  simpa only [← he, Prod.mk.eta] using hm

/-- Exact relative-index equality; no ambient normality is involved. -/
theorem relative_projection_index (C H : Subgroup (G × Multiplicative ℤ))
    (hz : cofinalProductZ G ∈ C) (hCH : C ≤ H) :
    ((projection C).subgroupOf (projection H)).index = (C.subgroupOf H).index := by
  rw [← projectionHom_map_subgroupOf C H hCH]
  exact (C.subgroupOf H).index_map_eq (projectionHom_surjective H) (projectionHom_ker_le C H hz)

/-- Nontriviality is preserved in the projected subgroup tower. -/
theorem relative_projection_ne_bot (C H : Subgroup (G × Multiplicative ℤ))
    (hCH : C ≤ H) (hne : projection C ≠ ⊥) :
    (projection C).subgroupOf (projection H) ≠ ⊥ := by
  intro he
  apply hne
  apply (Subgroup.eq_bot_iff_forall _).mpr
  intro g hg
  have hgH : g ∈ projection H := (Subgroup.map_mono hCH) hg
  have hm : (⟨g, hgH⟩ : projection H) ∈ (projection C).subgroupOf (projection H) := hg
  rw [he] at hm
  exact congrArg Subtype.val hm

/-- Finite generation passes to a subgroup viewed inside an overgroup. -/
theorem subgroupOf_fg (C H : Subgroup G) (hCH : C ≤ H) (hfg : C.FG) :
    (C.subgroupOf H).FG := by
  let e := Subgroup.subgroupOfEquivOfLe hCH
  exact IsMulFG.of_surjective e.symm e.symm.surjective

/-- Nonnormality inside the actual overgroup follows from its free projection,
relative infinite index, and a nontrivial finitely generated lower projection. -/
theorem subgroupOf_not_normal [IsFreeGroup G]
    (C H : Subgroup (G × Multiplicative ℤ)) (hz : cofinalProductZ G ∈ C)
    (hCH : C ≤ H) (hfg : C.FG) (hne : projection C ≠ ⊥)
    (hi : (C.subgroupOf H).index = 0) : ¬ (C.subgroupOf H).Normal := by
  intro hn
  let D := (projection C).subgroupOf (projection H)
  have hDnormal : D.Normal := by
    change ((projection C).subgroupOf (projection H)).Normal
    rw [← projectionHom_map_subgroupOf C H hCH]
    exact hn.map (projectionHom H) (projectionHom_surjective H)
  have hDfg : D.FG := by
    have hC' : (C.subgroupOf H).FG := subgroupOf_fg C H hCH hfg
    change ((projection C).subgroupOf (projection H)).FG
    rw [← projectionHom_map_subgroupOf C H hCH]
    infer_instance
  exact isFree_index_ne_zero D hDfg (relative_projection_ne_bot C H hCH hne)
    ((relative_projection_index C H hz hCH).trans hi)

/-- The marked center inside an overgroup is the actual subtype of the original
central generator. -/
def centerIn (H : Subgroup (G × Multiplicative ℤ)) (hzH : cofinalProductZ G ∈ H) : H :=
  ⟨cofinalProductZ G, hzH⟩

theorem centerIn_central (H : Subgroup (G × Multiplicative ℤ))
    (hzH : cofinalProductZ G ∈ H) (h : H) : Commute (centerIn H hzH) h :=
  Subtype.ext (cofinalProductZ_central h.1).eq

/-- The explicit product equivalence preserves the actual subtype center. -/
@[simp] theorem productEquiv_centerIn (H : Subgroup (G × Multiplicative ℤ))
    (hzH : cofinalProductZ G ∈ H) :
    productEquiv H hzH (centerIn H hzH) = cofinalProductZ (projection H) := rfl

/-- Boundedness by integer central powers restricts exactly to the subgroup
 tower; the inequalities and all subtype coercions are unchanged. -/
theorem centralBounded_restrict (O : LeftGroupOrder (G × Multiplicative ℤ))
    (H : Subgroup (G × Multiplicative ℤ)) (hzH : cofinalProductZ G ∈ H) :
    (O.restrictSubgroup H).centralBoundedSubgroup (centerIn H hzH) (centerIn_central H hzH) =
      (O.centralBoundedSubgroup (cofinalProductZ G) cofinalProductZ_central).subgroupOf H := by
  ext h
  rfl

/-- A proper overgroup of the bounded subgroup still has noncofinal center. -/
theorem restricted_not_cofinal (O : LeftGroupOrder (G × Multiplicative ℤ))
    (H : Subgroup (G × Multiplicative ℤ)) (hzH : cofinalProductZ G ∈ H)
    (hCH : O.centralBoundedSubgroup (cofinalProductZ G) cofinalProductZ_central < H) :
    ¬ (O.restrictSubgroup H).IsCofinal (centerIn H hzH) := by
  intro hc
  have he := ((O.restrictSubgroup H).isCofinal_iff_centralBoundedSubgroup_eq_top
    (centerIn H hzH) (centerIn_central H hzH)).mp hc
  rw [centralBounded_restrict] at he
  exact hCH.not_ge (Subgroup.subgroupOf_eq_top.mp he)

/-- Thus the lower subgroup has infinite index inside the actual overgroup. -/
theorem relative_bounded_index_zero (O : LeftGroupOrder (G × Multiplicative ℤ))
    (H : Subgroup (G × Multiplicative ℤ)) (hzH : cofinalProductZ G ∈ H)
    (hCH : O.centralBoundedSubgroup (cofinalProductZ G) cofinalProductZ_central < H) :
    ((O.centralBoundedSubgroup (cofinalProductZ G) cofinalProductZ_central).subgroupOf H).index = 0 := by
  rw [← centralBounded_restrict O H hzH]
  exact (O.restrictSubgroup H).centralBoundedSubgroup_index_eq_zero _ _
    (restricted_not_cofinal O H hzH hCH)

/-- Convex restriction supplies the finite positive generating set in the
proper overgroup itself. -/
theorem restricted_semigroupFG (P : PositiveCone (G × Multiplicative ℤ))
    (hfg : SemigroupFG P.1) (H : Subgroup (G × Multiplicative ℤ)) (hH : ConeConvex P H) :
    SemigroupFG (Subsemigroup.comap H.subtype.toMulHom P.1) := hH.semigroupFG_restrict hfg

/-- The relative nonnormality needed for the convex jump, now with all algebraic
obligations discharged from the original finite positive generation. It holds
for every proper overgroup of the bounded subgroup, even before requiring
convexity or minimality of that overgroup. -/
theorem centralBounded_subgroupOf_not_normal {ι : Type u} [Nontrivial ι]
    (P : PositiveCone (FreeGroup ι × Multiplicative ℤ)) (hfg : SemigroupFG P.1)
    (H : Subgroup (FreeGroup ι × Multiplicative ℤ))
    (hCH : (coneLeftOrder P).centralBoundedSubgroup
      (cofinalProductZ (FreeGroup ι)) cofinalProductZ_central < H) :
    ¬ (((coneLeftOrder P).centralBoundedSubgroup
      (cofinalProductZ (FreeGroup ι)) cofinalProductZ_central).subgroupOf H).Normal := by
  let O := coneLeftOrder P
  let C := O.centralBoundedSubgroup (cofinalProductZ (FreeGroup ι)) cofinalProductZ_central
  have hz : cofinalProductZ (FreeGroup ι) ∈ C := central_mem_bounded O
  exact subgroupOf_not_normal C H hz hCH.le
    (centralBoundedSubgroup_groupFG P hfg _ cofinalProductZ_central)
    (NoncofinalQuotientCone.bounded_projection_ne_bot P hfg)
    (relative_bounded_index_zero O H (hCH.le hz) hCH)

end NoncofinalFreeTower
end FnZPositiveCones
