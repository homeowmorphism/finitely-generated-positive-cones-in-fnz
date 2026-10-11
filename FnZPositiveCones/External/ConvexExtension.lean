module

public import FnZPositiveCones.Cone.Topology

@[expose] public section

/-! Perturbing the order inside a convex subgroup, without a normality assumption. -/
namespace FnZPositiveCones

universe u
variable {G : Type u} [Group G]

/-- Convexity in the actual left order induced by the strict cone. -/
def ConeConvex (P : PositiveCone G) (K : Subgroup G) : Prop :=
  letI := coneLinearOrder P
  Set.OrdConnected (K : Set G)

namespace ConeConvex
variable {P : PositiveCone G} {K : Subgroup G}

/-- A convenient strict-comparison form of order convexity. -/
theorem between (hK : ConeConvex P K) {x y z : G} (hx : x ∈ K) (hz : z ∈ K)
    (hxy : x⁻¹ * y ∈ P.1) (hyz : y⁻¹ * z ∈ P.1) : y ∈ K := by
  let := coneLinearOrder P
  exact hK.out hx hz ⟨Or.inr hxy, Or.inr hyz⟩

theorem positive_outside_mul_inside (hK : ConeConvex P K) {x y : G}
    (hx : x ∈ P.1) (hxK : x ∉ K) (hy : y ∈ K) : x * y ∈ P.1 ∧ x * y ∉ K := by
  have hxyK : x * y ∉ K := by
    intro h
    exact hxK (by simpa using K.mul_mem h (K.inv_mem hy))
  refine ⟨?_, hxyK⟩
  rcases P.2.2 (x * y) with he | hp | hn
  · exact (hxyK (he ▸ K.one_mem)).elim
  · exact hp
  · have hi : x⁻¹ ∈ K := hK.between hy K.one_mem
      (by simpa only [mul_inv_rev] using hn) (by simpa using hx)
    have hx' : x ∈ K := by simpa using K.inv_mem hi
    exact (hxK hx').elim

theorem inside_mul_positive_outside (hK : ConeConvex P K) {x y : G}
    (hx : x ∈ K) (hy : y ∈ P.1) (hyK : y ∉ K) : x * y ∈ P.1 ∧ x * y ∉ K := by
  have hxyK : x * y ∉ K := by
    intro h
    exact hyK (by simpa using K.mul_mem (K.inv_mem hx) h)
  refine ⟨?_, hxyK⟩
  rcases P.2.2 (x * y) with he | hp | hn
  · exact (hxyK (he ▸ K.one_mem)).elim
  · exact hp
  · have hi : y ∈ K := hK.between K.one_mem (K.inv_mem hx)
      (by simpa using hy) (by simpa only [mul_inv_rev] using hn)
    exact (hyK hi).elim

theorem positive_outside_mul_positive (hK : ConeConvex P K) {x y : G}
    (hx : x ∈ P.1) (hxK : x ∉ K) (hy : y ∈ P.1) : x * y ∈ P.1 ∧ x * y ∉ K := by
  refine ⟨P.1.mul_mem hx hy, ?_⟩
  intro h
  exact hxK (hK.between K.one_mem h (by simpa using hx) (by simpa using hy))

/-- Replace the signs inside a convex subgroup, retaining all signs outside it. -/
def replaceCone (hK : ConeConvex P K) (Q : Subsemigroup K) : Subsemigroup G where
  carrier := {g | (g ∈ P.1 ∧ g ∉ K) ∨ ∃ hg : g ∈ K, (⟨g, hg⟩ : K) ∈ Q}
  mul_mem' := by
    rintro x y (⟨hx, hxK⟩ | ⟨hxK, hx⟩) (⟨hy, hyK⟩ | ⟨hyK, hy⟩)
    · exact Or.inl (hK.positive_outside_mul_positive hx hxK hy)
    · exact Or.inl (hK.positive_outside_mul_inside hx hxK hyK)
    · exact Or.inl (hK.inside_mul_positive_outside hxK hy hyK)
    · exact Or.inr ⟨K.mul_mem hxK hyK, Q.mul_mem hx hy⟩

@[simp] theorem mem_replaceCone_of_mem (hK : ConeConvex P K) (Q : Subsemigroup K)
    (g : K) : (g : G) ∈ hK.replaceCone Q ↔ g ∈ Q := by
  change (((g : G) ∈ P.1 ∧ (g : G) ∉ K) ∨ ∃ hg : (g : G) ∈ K,
    (⟨(g : G), hg⟩ : K) ∈ Q) ↔ g ∈ Q
  simp [g.property]

 theorem replaceCone_positive (hK : ConeConvex P K) {Q : Subsemigroup K}
    (hQ : IsPositiveCone Q) : IsPositiveCone (hK.replaceCone Q) := by
  constructor
  · intro h
    have : (1 : K) ∈ Q := (mem_replaceCone_of_mem hK Q 1).mp h
    exact hQ.1 this
  · intro g
    by_cases hg : g ∈ K
    · rcases hQ.2 (⟨g, hg⟩ : K) with he | hp | hn
      · exact Or.inl (congrArg Subtype.val he)
      · exact Or.inr (Or.inl (Or.inr ⟨hg, hp⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨K.inv_mem hg, hn⟩))
    · rcases P.2.2 g with he | hp | hn
      · exact Or.inl he
      · exact Or.inr (Or.inl (Or.inl ⟨hp, hg⟩))
      · exact Or.inr (Or.inr (Or.inl ⟨hn, by simpa using hg⟩))

/-- Finite determination passes to every convex subgroup. -/
theorem finitelyDetermined_restrict (hK : ConeConvex P K) (hfd : FinitelyDetermined P.1) :
    FinitelyDetermined (Subsemigroup.comap K.subtype.toMulHom P.1) := by
  classical
  obtain ⟨S, hSP, hS⟩ := hfd
  let T : Finset K := S.preimage Subtype.val Subtype.val_injective.injOn
  refine ⟨T, ?_, ?_⟩
  · intro g hg
    exact hSP (Finset.mem_preimage.mp hg)
  · intro Q hQ hTQ
    have hreplace : hK.replaceCone Q = P.1 := hS _ (hK.replaceCone_positive hQ) (by
      intro g hg
      by_cases hgK : g ∈ K
      · exact Or.inr ⟨hgK, hTQ (Finset.mem_preimage.mpr hg)⟩
      · exact Or.inl ⟨hSP hg, hgK⟩)
    ext g
    change g ∈ Q ↔ (g : G) ∈ P.1
    rw [← hreplace, mem_replaceCone_of_mem]

/-- Non-isolation of the restricted cone obstructs finite determination upstairs. -/
theorem not_finitelyDetermined (hK : ConeConvex P K)
    (hsub : ¬ FinitelyDetermined (Subsemigroup.comap K.subtype.toMulHom P.1)) :
    ¬ FinitelyDetermined P.1 := fun h => hsub (hK.finitelyDetermined_restrict h)

end ConeConvex
end FnZPositiveCones
