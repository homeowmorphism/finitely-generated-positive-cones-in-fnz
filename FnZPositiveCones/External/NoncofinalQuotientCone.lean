module

public import FnZPositiveCones.External.ConvexExtension
public import FnZPositiveCones.External.NoncofinalSubgroupProduct
public import FnZPositiveCones.External.NoncofinalFreeCone

@[expose] public section

/-!
# Strict cones on quotients by convex kernels

Finite positive generation descends along a surjective homomorphism with a
convex kernel. Identity images are discarded. The proof tracks whether the
projected product is the identity or belongs to a nonempty semigroup closure;
it never replaces that closure by a monoid closure.
-/

namespace FnZPositiveCones
namespace NoncofinalQuotientCone

universe u v
variable {G : Type u} {H : Type v} [Group G] [Group H]
variable (P : PositiveCone G) (φ : G →* H) (hc : ConeConvex P φ.ker)

/-- Positive elements strictly outside the convex kernel remain closed under
multiplication. -/
def outside : Subsemigroup G where
  carrier := {g | g ∈ P.1 ∧ g ∉ φ.ker}
  mul_mem' := fun hx hy => hc.positive_outside_mul_positive hx.1 hx.2 hy.1

/-- The strict cone induced on the codomain. -/
def quotientCone : Subsemigroup H := Subsemigroup.map φ.toMulHom (outside P φ hc)

@[simp] theorem mem_quotientCone (h : H) :
    h ∈ quotientCone P φ hc ↔ h ≠ 1 ∧ ∃ g ∈ P.1, φ g = h := by
  constructor
  · rintro ⟨g, ⟨hg, hgk⟩, rfl⟩
    exact ⟨hgk, g, hg, rfl⟩
  · rintro ⟨hne, g, hg, rfl⟩
    exact ⟨g, ⟨hg, hne⟩, rfl⟩

/-- Surjectivity gives totality of the induced strict cone. -/
theorem quotientCone_positive (hsurj : Function.Surjective φ) :
    IsPositiveCone (quotientCone P φ hc) := by
  constructor
  · intro h
    exact ((mem_quotientCone P φ hc 1).mp h).1 rfl
  · intro h
    by_cases he : h = 1
    · exact Or.inl he
    obtain ⟨g, rfl⟩ := hsurj h
    rcases P.2.2 g with hg | hp | hn
    · exact (he (hg ▸ φ.map_one)).elim
    · exact Or.inr (Or.inl ((mem_quotientCone P φ hc _).mpr ⟨he, g, hp, rfl⟩))
    · exact Or.inr (Or.inr ((mem_quotientCone P φ hc _).mpr
        ⟨by simpa using he, g⁻¹, hn, φ.map_inv g⟩))

open scoped Classical in
/-- Nonidentity images of the original positive generators generate the strict
quotient cone by nonempty products. -/
theorem quotientCone_closure (S : Finset G) (hS : Subsemigroup.closure (S : Set G) = P.1) :
    Subsemigroup.closure
      (((S.filter (fun g => φ g ≠ 1)).image φ : Finset H) : Set H) = quotientCone P φ hc := by
  classical
  let T : Finset H := (S.filter (fun g => φ g ≠ 1)).image φ
  have hSP : (S : Set G) ⊆ (P.1 : Set G) := by
    rw [← hS]
    exact Subsemigroup.subset_closure
  apply le_antisymm
  · apply Subsemigroup.closure_le.mpr
    intro h hh
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hh
    obtain ⟨hgS, hgne⟩ := Finset.mem_filter.mp hg
    exact (mem_quotientCone P φ hc _).mpr ⟨hgne, g, hSP hgS, rfl⟩
  · have hproject : ∀ g ∈ P.1, φ g = 1 ∨ φ g ∈ Subsemigroup.closure (T : Set H) := by
      intro g hg
      rw [← hS] at hg
      induction hg using Subsemigroup.closure_induction with
      | mem g hg =>
        by_cases he : φ g = 1
        · exact Or.inl he
        · right
          apply Subsemigroup.subset_closure
          exact Finset.mem_image.mpr ⟨g, Finset.mem_filter.mpr ⟨hg, he⟩, rfl⟩
      | mul a b ha hb iha ihb =>
        rw [φ.map_mul]
        rcases iha with he | hp
        · simpa [he] using ihb
        · rcases ihb with he | hq
          · exact Or.inr (by simpa [he] using hp)
          · exact Or.inr (Subsemigroup.mul_mem _ hp hq)
    intro h hh
    obtain ⟨hne, g, hg, rfl⟩ := (mem_quotientCone P φ hc _).mp hh
    exact (hproject g hg).resolve_left hne

/-- Finite semigroup generation descends through every convex kernel. -/
theorem quotientCone_semigroupFG (hfg : SemigroupFG P.1) :
    SemigroupFG (quotientCone P φ hc) := by
  classical
  obtain ⟨S, hS⟩ := hfg
  exact ⟨(S.filter (fun g => φ g ≠ 1)).image φ, quotientCone_closure P φ hc S hS⟩

include hc in
/-- Existence form of the quotient construction. -/
theorem hasFGPositiveCone_of_convex_kernel (hsurj : Function.Surjective φ)
    (hfg : SemigroupFG P.1) : HasFGPositiveCone H := by
  obtain ⟨T, hT⟩ := quotientCone_semigroupFG P φ hc hfg
  exact ⟨T, by rw [hT]; exact quotientCone_positive P φ hc hsurj⟩

/-- In a finitely generated cone on a nonabelian free group product, the
central-bounded subgroup has a nontrivial free projection. This discharges the
trivial-projection branch using the actual finite-generation hypothesis. -/
theorem bounded_projection_ne_bot {ι : Type u} [Nontrivial ι]
    (P : PositiveCone (FreeGroup ι × Multiplicative ℤ)) (hfg : SemigroupFG P.1) :
    NoncofinalSubgroupProduct.projection ((coneLeftOrder P).centralBoundedSubgroup
      (cofinalProductZ (FreeGroup ι)) cofinalProductZ_central) ≠ ⊥ := by
  intro hbot
  let O := coneLeftOrder P
  let C := O.centralBoundedSubgroup (cofinalProductZ (FreeGroup ι)) cofinalProductZ_central
  let φ := MonoidHom.fst (FreeGroup ι) (Multiplicative ℤ)
  have he : C = φ.ker := by
    rw [NoncofinalSubgroupProduct.eq_comap_projection C
      (NoncofinalSubgroupProduct.central_mem_bounded O)]
    change (NoncofinalSubgroupProduct.projection C).comap φ = φ.ker
    rw [show NoncofinalSubgroupProduct.projection C = ⊥ from hbot]
    rfl
  have hc : ConeConvex P φ.ker := by
    rw [← he]
    exact O.centralBoundedSubgroup_ordConnected _ cofinalProductZ_central
  exact NoncofinalFreeCone.not_hasFGPositiveCone
    (hasFGPositiveCone_of_convex_kernel P φ hc (fun g => ⟨(g, 1), rfl⟩) hfg)

/-- The actual finite-generation hypothesis suffices for both algebraic inputs:
the central-bounded subgroup is finitely generated and its projection is
nontrivial, hence a noncofinal center forces that subgroup to be nonnormal. -/
theorem bounded_not_normal_of_semigroupFG {ι : Type u} [Nontrivial ι]
    (P : PositiveCone (FreeGroup ι × Multiplicative ℤ)) (hfg : SemigroupFG P.1)
    (hnon : ¬ (coneLeftOrder P).IsCofinal (cofinalProductZ (FreeGroup ι))) :
    ¬ ((coneLeftOrder P).centralBoundedSubgroup
      (cofinalProductZ (FreeGroup ι)) cofinalProductZ_central).Normal :=
  NoncofinalSubgroupProduct.bounded_not_normal_of_semigroupFG P hfg
    (bounded_projection_ne_bot P hfg) hnon

end NoncofinalQuotientCone
end FnZPositiveCones
