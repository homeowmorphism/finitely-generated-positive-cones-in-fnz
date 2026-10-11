module

public import FnZPositiveCones.External.NoncofinalFreeSubgroup
public import FnZPositiveCones.External.Noncofinal
public import FnZPositiveCones.External.CircularQuotient

@[expose] public section

/-!
# Subgroups containing the distinguished central factor

A subgroup containing `z = (1, 1)` contains the entire integer factor and is
exactly the product of its first projection and that factor. The equivalence,
its inverse, index equality, and normality equivalence are checked explicitly.
-/

namespace FnZPositiveCones
namespace NoncofinalSubgroupProduct

universe u
variable {G : Type u} [Group G]

/-- The projection used throughout the noncofinal argument. -/
abbrev projection (C : Subgroup (G × Multiplicative ℤ)) : Subgroup G :=
  C.map (MonoidHom.fst G (Multiplicative ℤ))

variable (C : Subgroup (G × Multiplicative ℤ)) (hz : cofinalProductZ G ∈ C)

include hz in
/-- Containing the marked central generator means containing the whole factor. -/
theorem central_factor_mem (t : Multiplicative ℤ) : (1, t) ∈ C := by
  have h := C.zpow_mem hz t.toAdd
  simpa [cofinalProductZ, ← ofAdd_zsmul] using h

include hz in
/-- Membership depends only on the first coordinate. No normality is needed. -/
theorem mem_iff_projection (g : G) (t : Multiplicative ℤ) :
    (g, t) ∈ C ↔ g ∈ projection C := by
  constructor
  · intro h
    exact ⟨(g, t), h, rfl⟩
  · rintro ⟨⟨g', t'⟩, hp, he⟩
    change g' = g at he
    subst g'
    have h := C.mul_mem hp (central_factor_mem C hz (t'⁻¹ * t))
    simpa using h

include hz in
/-- Equality with the inverse image of the projection. -/
theorem eq_comap_projection : C = (projection C).comap (MonoidHom.fst G (Multiplicative ℤ)) := by
  ext ⟨g, t⟩
  exact mem_iff_projection C hz g t

include hz in
/-- Equality with the product as an ambient subgroup. -/
theorem eq_projection_prod : C = (projection C).prod ⊤ := by
  rw [Subgroup.prod_top]
  exact eq_comap_projection C hz

/-- Explicit product isomorphism, with inverse `(g,t) ↦ (g,t)` on the
underlying ambient pair and membership justified by the central factor. -/
def productEquiv : C ≃* projection C × Multiplicative ℤ where
  toFun c := (⟨c.1.1, ⟨c.1, c.2, rfl⟩⟩, c.1.2)
  invFun c := ⟨(c.1.1, c.2), (mem_iff_projection C hz _ _).mpr c.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

@[simp] theorem productEquiv_apply (c : C) :
    productEquiv C hz c = (⟨c.1.1, ⟨c.1, c.2, rfl⟩⟩, c.1.2) := rfl

@[simp] theorem productEquiv_symm_coe (c : projection C × Multiplicative ℤ) :
    ((productEquiv C hz).symm c : G × Multiplicative ℤ) = (c.1.1, c.2) := rfl

/-- The marked central element is unchanged by the product decomposition. -/
@[simp] theorem productEquiv_central :
    productEquiv C hz ⟨cofinalProductZ G, hz⟩ = cofinalProductZ (projection C) := rfl

include hz in
/-- Projection preserves the subgroup index because its kernel is contained in `C`. -/
theorem projection_index : (projection C).index = C.index := by
  apply C.index_map_eq (fun g => ⟨(g, 1), rfl⟩)
  intro ⟨g, t⟩ hg
  change g = 1 at hg
  subst g
  exact central_factor_mem C hz t

include hz in
/-- Normality of the projected subgroup is equivalent to normality upstairs. -/
theorem normal_iff_projection : C.Normal ↔ (projection C).Normal := by
  constructor
  · intro h
    exact h.map _ (fun g => ⟨(g, 1), rfl⟩)
  · intro h
    rw [eq_comap_projection C hz]
    exact h.comap _

/-- Projection of a finitely generated subgroup is finitely generated. -/
theorem projection_fg (hfg : C.FG) : (projection C).FG := by
  infer_instance

/-- Infinite index and a nontrivial finitely generated free projection force
nonnormality. This is the algebraic inference between MMRT Claims 3 and 4. -/
theorem not_normal_of_projection {ι : Type u} [Nontrivial ι]
    (C : Subgroup (FreeGroup ι × Multiplicative ℤ))
    (hz : cofinalProductZ (FreeGroup ι) ∈ C)
    (hfg : (projection C).FG) (hne : projection C ≠ ⊥) (hi : C.index = 0) :
    ¬ C.Normal := by
  intro hn
  have hp := (normal_iff_projection C hz).mp hn
  exact NoncofinalFreeSubgroup.not_normal_of_fg_nontrivial_index_zero
    (projection C) hfg hne ((projection_index C hz).trans hi) hp

/-- The bounded subgroup contains the marked central generator. -/
theorem central_mem_bounded (O : LeftGroupOrder (G × Multiplicative ℤ)) :
    cofinalProductZ G ∈ O.centralBoundedSubgroup (cofinalProductZ G) cofinalProductZ_central := by
  simpa using O.zpow_mem_centralBoundedSubgroup (cofinalProductZ G) cofinalProductZ_central 1

/-- Nonnormality of a noncofinal central-bounded subgroup, with finite generation
and nontriviality stated only for its free projection. -/
theorem bounded_not_normal {ι : Type u} [Nontrivial ι]
    (O : LeftGroupOrder (FreeGroup ι × Multiplicative ℤ))
    (hfg : (projection (O.centralBoundedSubgroup
      (cofinalProductZ (FreeGroup ι)) cofinalProductZ_central)).FG)
    (hne : projection (O.centralBoundedSubgroup
      (cofinalProductZ (FreeGroup ι)) cofinalProductZ_central) ≠ ⊥)
    (hnon : ¬ O.IsCofinal (cofinalProductZ (FreeGroup ι))) :
    ¬ (O.centralBoundedSubgroup (cofinalProductZ (FreeGroup ι)) cofinalProductZ_central).Normal :=
  not_normal_of_projection _ (central_mem_bounded O) hfg hne
    (O.centralBoundedSubgroup_index_eq_zero _ cofinalProductZ_central hnon)

/-- For a finitely generated strict cone, the required projected finite
generation is already checked by restriction to the convex bounded subgroup. -/
theorem bounded_not_normal_of_semigroupFG {ι : Type u} [Nontrivial ι]
    (P : PositiveCone (FreeGroup ι × Multiplicative ℤ)) (hfg : SemigroupFG P.1)
    (hne : projection ((coneLeftOrder P).centralBoundedSubgroup
      (cofinalProductZ (FreeGroup ι)) cofinalProductZ_central) ≠ ⊥)
    (hnon : ¬ (coneLeftOrder P).IsCofinal (cofinalProductZ (FreeGroup ι))) :
    ¬ ((coneLeftOrder P).centralBoundedSubgroup
      (cofinalProductZ (FreeGroup ι)) cofinalProductZ_central).Normal := by
  apply bounded_not_normal _ _ hne hnon
  exact projection_fg _ (centralBoundedSubgroup_groupFG P hfg _ cofinalProductZ_central)

end NoncofinalSubgroupProduct
end FnZPositiveCones
