module

public import FnZPositiveCones.External.NoncofinalConvexJump
public import FnZPositiveCones.External.NoncofinalSubgroupProduct

@[expose] public section

/-!
# Convex-jump restriction and the product nonnormality adapter

A minimal convex overgroup gives a maximal proper convex subgroup after
restriction. All subgroup towers retain their subtype inclusions explicitly.
Nonnormality must hold inside that overgroup; ambient nonnormality alone is
not used to infer it.
-/

namespace FnZPositiveCones.NoncofinalConvexJumpAdapter

open NoncofinalConvexJump NoncofinalCrossings

universe u
variable {G : Type u} [Group G]

/-- Convexity restricts to the actual subgroup tower. -/
theorem convex_subgroupOf (O : LeftGroupOrder G) (C H : Subgroup G)
    (hC : letI := O.order; Set.OrdConnected (C : Set G)) :
    letI := (O.restrictSubgroup H).order
    Set.OrdConnected (C.subgroupOf H : Set H) := by
  let := O.order
  let := (O.restrictSubgroup H).order
  constructor
  intro a ha b hb y hy
  exact hC.out ha hb hy

/-- A convex subgroup of a convex subgroup remains convex in the ambient order. -/
theorem convex_map_subtype (O : LeftGroupOrder G) (H : Subgroup G)
    (hH : letI := O.order; Set.OrdConnected (H : Set G)) (S : Subgroup H)
    (hS : letI := (O.restrictSubgroup H).order; Set.OrdConnected (S : Set H)) :
    letI := O.order
    Set.OrdConnected (S.map H.subtype : Set G) := by
  let := O.order
  let := (O.restrictSubgroup H).order
  constructor
  rintro a ⟨a', ha', rfl⟩ b ⟨b', hb', rfl⟩ y hy
  have hyH : y ∈ H := hH.out a'.2 b'.2 hy
  refine ⟨⟨y, hyH⟩, ?_, rfl⟩
  exact hS.out ha' hb' hy

/-- Minimality upstairs gives the exact maximal-convex contract in the restricted order. -/
theorem maximal_subgroupOf_of_minimal_overgroup (O : LeftGroupOrder G) (C H : Subgroup G)
    (hH : letI := O.order; Set.OrdConnected (H : Set G)) (hCH : C < H)
    (hmin : ∀ M : Subgroup G, (letI := O.order; Set.OrdConnected (M : Set G)) →
      C < M → M ≤ H → H ≤ M) :
    C.subgroupOf H ≠ ⊤ ∧
    ∀ S : Subgroup H, (letI := (O.restrictSubgroup H).order; Set.OrdConnected (S : Set H)) →
      C.subgroupOf H < S → S = ⊤ := by
  constructor
  · exact fun h => hCH.not_ge (Subgroup.subgroupOf_eq_top.mp h)
  · intro S hS hCS
    have hCM : C ≤ S.map H.subtype := by
      intro c hc
      exact ⟨⟨c, hCH.le hc⟩, hCS.le hc, rfl⟩
    have hlt : C < S.map H.subtype := lt_of_le_of_ne hCM (by
      intro he
      apply hCS.not_ge
      intro s hs
      have hm : (s : G) ∈ S.map H.subtype := ⟨s, hs, rfl⟩
      exact he.symm ▸ hm)
    have hHM := hmin (S.map H.subtype) (convex_map_subtype O H hH S hS) hlt
      (Subgroup.map_subtype_le S)
    apply top_unique
    intro s _
    obtain ⟨t, ht, he⟩ := hHM s.2
    exact (Subtype.ext he : t = s) ▸ ht

/-- The complete finite-chain restriction adapter, including the proper maximal
subgroup in the restricted order, follows from finite determination. -/
theorem exists_maximal_convex_restriction (P : PositiveCone G)
    (hfd : FinitelyDetermined P.1) (C : Subgroup G) (hC : ConeConvex P C) (hne : C ≠ ⊤) :
    ∃ H : Subgroup G, ConeConvex P H ∧ C < H ∧
      (letI := ((coneLeftOrder P).restrictSubgroup H).order
       Set.OrdConnected (C.subgroupOf H : Set H)) ∧
      C.subgroupOf H ≠ ⊤ ∧
      ∀ S : Subgroup H,
        (letI := ((coneLeftOrder P).restrictSubgroup H).order; Set.OrdConnected (S : Set H)) →
        C.subgroupOf H < S → S = ⊤ := by
  obtain ⟨H, hH, hCH, hmin⟩ := NoncofinalConvex.exists_minimal_convex_overgroup P hfd C hne
  have hm := maximal_subgroupOf_of_minimal_overgroup (coneLeftOrder P) C H hH hCH hmin
  exact ⟨H, hH, hCH, convex_subgroupOf (coneLeftOrder P) C H hC, hm.1, hm.2⟩

/-- Nonnormality inside the minimal convex overgroup gives an actual crossing
for the restricted ordered left-coset action. -/
theorem crossing_in_minimal_overgroup (O : LeftGroupOrder G) (C H : Subgroup G)
    (hC : letI := O.order; Set.OrdConnected (C : Set G))
    (hH : letI := O.order; Set.OrdConnected (H : Set G)) (hCH : C < H)
    (hmin : ∀ M : Subgroup G, (letI := O.order; Set.OrdConnected (M : Set G)) →
      C < M → M ≤ H → H ≤ M)
    (hnormal : ¬ (C.subgroupOf H).Normal) :
    let O' := O.restrictSubgroup H
    let C' := C.subgroupOf H
    let hC' := convex_subgroupOf O C H hC
    letI := cosetLinearOrder O' C' hC'
    ∃ f g : H, ∃ u v w : H ⧸ C',
      Crossing (cosetAction O' C' hC' f) (cosetAction O' C' hC' g) u v w := by
  have hm := maximal_subgroupOf_of_minimal_overgroup O C H hH hCH hmin
  exact exists_crossing_of_maximal_convex_not_normal (O.restrictSubgroup H)
    (C.subgroupOf H) (convex_subgroupOf O C H hC) hm.1 hm.2 hnormal

/-- The checked free-projection obstruction supplies nonnormality, and therefore
crossings, when the ambient group of the convex jump is explicitly a product. -/
theorem crossing_of_product_projection {ι : Type u} [Nontrivial ι]
    (O : LeftGroupOrder (FreeGroup ι × Multiplicative ℤ))
    (C : Subgroup (FreeGroup ι × Multiplicative ℤ))
    (hC : letI := O.order; Set.OrdConnected (C : Set (FreeGroup ι × Multiplicative ℤ)))
    (hmax : ∀ S : Subgroup (FreeGroup ι × Multiplicative ℤ),
      (letI := O.order; Set.OrdConnected (S : Set (FreeGroup ι × Multiplicative ℤ))) →
      C < S → S = ⊤)
    (hz : cofinalProductZ (FreeGroup ι) ∈ C)
    (hfg : (NoncofinalSubgroupProduct.projection C).FG)
    (hne : NoncofinalSubgroupProduct.projection C ≠ ⊥) (hi : C.index = 0) :
    letI := cosetLinearOrder O C hC
    ∃ f g : FreeGroup ι × Multiplicative ℤ, ∃ u v w : (FreeGroup ι × Multiplicative ℤ) ⧸ C,
      Crossing (cosetAction O C hC f) (cosetAction O C hC g) u v w := by
  have hproper : C ≠ ⊤ := by
    intro h
    simp only [h, Subgroup.index_top, Nat.one_ne_zero] at hi
  exact exists_crossing_of_maximal_convex_not_normal O C hC hproper hmax
    (NoncofinalSubgroupProduct.not_normal_of_projection C hz hfg hne hi)

end FnZPositiveCones.NoncofinalConvexJumpAdapter
