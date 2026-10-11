module

public import FnZPositiveCones.External.NoncofinalQuotientCone

@[expose] public section

/-!
# Finite determination descends through convex kernels

An alternative quotient cone is lifted lexicographically, retaining the
original signs in the kernel. Its nonidentity signs are tested by the
nonidentity images of an ambient finite determining set. This is an
isolation argument; finite semigroup generation is not assumed or inferred.
-/

namespace FnZPositiveCones.IsolatedQuotientCone

open NoncofinalQuotientCone

universe u v
variable {G : Type u} {H : Type v} [Group G] [Group H]

/-- Lift quotient signs and retain the original signs exactly in the kernel.
The multiplication proof retains the order of noncommuting factors. -/
def lexCone (P : PositiveCone G) (φ : G →* H) (Q : Subsemigroup H) : Subsemigroup G where
  carrier := {g | φ g ∈ Q ∨ (φ g = 1 ∧ g ∈ P.1)}
  mul_mem' := by
    intro a b ha hb
    rcases ha with ha | ⟨ha, hPa⟩
    · rcases hb with hb | ⟨hb, _⟩
      · exact Or.inl (by simpa only [φ.map_mul] using Q.mul_mem ha hb)
      · exact Or.inl (by simpa only [φ.map_mul, hb, mul_one] using ha)
    · rcases hb with hb | ⟨hb, hPb⟩
      · exact Or.inl (by simpa only [φ.map_mul, ha, one_mul] using hb)
      · exact Or.inr ⟨by simp only [φ.map_mul, ha, hb, mul_one], P.1.mul_mem hPa hPb⟩

@[simp] theorem mem_lexCone (P : PositiveCone G) (φ : G →* H) (Q : Subsemigroup H) (g : G) :
    g ∈ lexCone P φ Q ↔ φ g ∈ Q ∨ (φ g = 1 ∧ g ∈ P.1) := Iff.rfl

/-- Any strict quotient cone gives a strict lifted cone. No commutativity
or splitting of the quotient homomorphism is needed. -/
theorem lexCone_positive (P : PositiveCone G) (φ : G →* H) (Q : Subsemigroup H)
    (hQ : IsPositiveCone Q) : IsPositiveCone (lexCone P φ Q) := by
  constructor
  · intro h
    rcases h with h | ⟨_, h⟩
    · exact hQ.1 (by simpa only [φ.map_one] using h)
    · exact P.2.1 h
  · intro g
    rcases hQ.2 (φ g) with he | hp | hn
    · rcases P.2.2 g with hg | hp | hn
      · exact Or.inl hg
      · exact Or.inr (Or.inl (Or.inr ⟨he, hp⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨by simp only [φ.map_inv, he, inv_one], hn⟩))
    · exact Or.inr (Or.inl (Or.inl hp))
    · exact Or.inr (Or.inr (Or.inl (by simpa only [φ.map_inv] using hn)))

/-- The actual strict quotient cone inherits finite determination through
any surjective homomorphism with convex kernel. Identity images are omitted
from the finite sign tests. -/
theorem quotientCone_finitelyDetermined (P : PositiveCone G) (φ : G →* H)
    (hc : ConeConvex P φ.ker) (hsurj : Function.Surjective φ)
    (hfd : FinitelyDetermined P.1) : FinitelyDetermined (quotientCone P φ hc) := by
  classical
  obtain ⟨S, hSP, hdet⟩ := hfd
  let T := (S.filter (fun g => φ g ≠ 1)).image φ
  refine ⟨T, ?_, ?_⟩
  · intro y hy
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨hgS, hgφ⟩ := Finset.mem_filter.mp hg
    exact (mem_quotientCone P φ hc _).mpr ⟨hgφ, g, hSP hgS, rfl⟩
  · intro Q hQ hTQ
    have hlift : lexCone P φ Q = P.1 := hdet _ (lexCone_positive P φ Q hQ) (by
      intro g hg
      by_cases he : φ g = 1
      · exact Or.inr ⟨he, hSP hg⟩
      · exact Or.inl (hTQ (Finset.mem_image.mpr
          ⟨g, Finset.mem_filter.mpr ⟨hg, he⟩, rfl⟩)))
    ext y
    constructor
    · intro hy
      obtain ⟨g, rfl⟩ := hsurj y
      have hg : g ∈ P.1 := hlift ▸ (show g ∈ lexCone P φ Q from Or.inl hy)
      exact (mem_quotientCone P φ hc _).mpr
        ⟨fun he => hQ.1 (he ▸ hy), g, hg, rfl⟩
    · intro hy
      obtain ⟨hne, g, hg, rfl⟩ := (mem_quotientCone P φ hc y).mp hy
      have hmem : g ∈ lexCone P φ Q := hlift.symm ▸ hg
      rcases hmem with hmem | ⟨he, _⟩
      · exact hmem
      · exact (hne he).elim

/-- Bundled existence form, ready to apply an independently checked
nonisolation theorem for the quotient group. -/
theorem exists_finitelyDetermined_quotient (P : PositiveCone G) (φ : G →* H)
    (hc : ConeConvex P φ.ker) (hsurj : Function.Surjective φ)
    (hfd : FinitelyDetermined P.1) :
    ∃ Q : PositiveCone H, FinitelyDetermined Q.1 :=
  ⟨⟨quotientCone P φ hc, quotientCone_positive P φ hc hsurj⟩,
    quotientCone_finitelyDetermined P φ hc hsurj hfd⟩

/-- If the subgroup bounded by central powers has trivial free projection,
its kernel quotient is the original free group and inherits an actual
finitely determined strict cone. No free-group nonisolation result is used. -/
theorem exists_finitelyDetermined_free_cone_of_bounded_projection_eq_bot {ι : Type u}
    (P : PositiveCone (FreeGroup ι × Multiplicative ℤ)) (hfd : FinitelyDetermined P.1)
    (hbot : NoncofinalSubgroupProduct.projection ((coneLeftOrder P).centralBoundedSubgroup
      (cofinalProductZ (FreeGroup ι)) cofinalProductZ_central) = ⊥) :
    ∃ Q : PositiveCone (FreeGroup ι), FinitelyDetermined Q.1 := by
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
  exact exists_finitelyDetermined_quotient P φ hc (fun g => ⟨(g, 1), rfl⟩) hfd

end FnZPositiveCones.IsolatedQuotientCone
