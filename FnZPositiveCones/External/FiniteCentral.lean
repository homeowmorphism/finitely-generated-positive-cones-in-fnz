module

public import FnZPositiveCones.External.ConvexExtension
public import FnZPositiveCones.External.Cofinal

@[expose] public section

/-!
# Finite positive generation and the convex subgroup bounded by central powers

These results reduce, but do not settle, the noncofinal-center case. In particular,
finite positive generation is not used as an unsupported cofinality assertion.
-/
namespace FnZPositiveCones

universe u
variable {G : Type u} [Group G]

/-- A semigroup generating family for a strict total cone generates the group. -/
theorem positiveCone_subgroup_closure {P : Subsemigroup G} (hP : IsPositiveCone P)
    (S : Set G) (hS : Subsemigroup.closure S = P) : Subgroup.closure S = ⊤ := by
  have hp : ∀ g ∈ P, g ∈ Subgroup.closure S := by
    intro g hg
    have hle : Subsemigroup.closure S ≤ (Subgroup.closure S).toSubsemigroup :=
      Subsemigroup.closure_le.mpr (fun _ h => Subgroup.subset_closure h)
    exact hle (hS.symm ▸ hg)
  apply top_unique
  intro g _
  rcases hP.2 g with rfl | hg | hg
  · exact (Subgroup.closure S).one_mem
  · exact hp g hg
  · simpa using (Subgroup.closure S).inv_mem (hp g⁻¹ hg)

/-- Finite positive generation in particular gives finite group generation. -/
theorem groupFG_of_semigroupFG_positiveCone {P : Subsemigroup G}
    (hP : IsPositiveCone P) (hfg : SemigroupFG P) : Group.FG G := by
  obtain ⟨S, hS⟩ := hfg
  exact Group.fg_iff.mpr ⟨S, positiveCone_subgroup_closure hP S hS, S.finite_toSet⟩

namespace ConeConvex
variable {P : PositiveCone G} {K : Subgroup G}

/-- In a product of positive elements lying in a convex subgroup, each factor lies there. -/
theorem factors_mem (hK : ConeConvex P K) {x y : G}
    (hx : x ∈ P.1) (hy : y ∈ P.1) (hxy : x * y ∈ K) : x ∈ K ∧ y ∈ K := by
  have hxK : x ∈ K := hK.between K.one_mem hxy (by simpa using hx) (by simpa using hy)
  exact ⟨hxK, by simpa using K.mul_mem (K.inv_mem hxK) hxy⟩

/-- Positive words lying in a convex subgroup use only generators in that subgroup. -/
theorem restricted_closure_eq (hK : ConeConvex P K) (S : Set G)
    (hS : Subsemigroup.closure S = P.1) :
    Subsemigroup.comap K.subtype.toMulHom P.1 =
      Subsemigroup.closure (Subtype.val ⁻¹' S : Set K) := by
  apply le_antisymm
  · intro g hg
    have hg' : (g : G) ∈ Subsemigroup.closure S := hS.symm ▸ hg
    have hall : ∀ x ∈ Subsemigroup.closure S, ∀ hx : x ∈ K,
        (⟨x, hx⟩ : K) ∈ Subsemigroup.closure (Subtype.val ⁻¹' S : Set K) := by
      intro x hx
      induction hx using Subsemigroup.closure_induction with
      | mem x hx =>
        intro hxK
        exact Subsemigroup.subset_closure hx
      | mul x y hx hy ihx ihy =>
        intro hxy
        obtain ⟨hxK, hyK⟩ := hK.factors_mem (hS ▸ hx) (hS ▸ hy) hxy
        exact Subsemigroup.mul_mem _ (ihx hxK) (ihy hyK)
    exact hall g hg' g.property
  · apply Subsemigroup.closure_le.mpr
    intro g hg
    exact hS ▸ Subsemigroup.subset_closure hg

/-- Finite semigroup generation, not only finite determination, descends to convex subgroups. -/
theorem semigroupFG_restrict (hK : ConeConvex P K) (hfg : SemigroupFG P.1) :
    SemigroupFG (Subsemigroup.comap K.subtype.toMulHom P.1) := by
  classical
  obtain ⟨S, hS⟩ := hfg
  refine ⟨S.preimage Subtype.val Subtype.val_injective.injOn, ?_⟩
  rw [Finset.coe_preimage]
  exact (hK.restricted_closure_eq S hS).symm

end ConeConvex

namespace LeftGroupOrder
/-- Restriction uses the same comparisons and only left invariance. -/
noncomputable def restrictSubgroup (O : LeftGroupOrder G) (K : Subgroup G) : LeftGroupOrder K := by
  let := O.order
  exact {
    order := inferInstance
    mul_le_mul_left := fun a b c hab => O.mul_le_mul_left a b c hab }
end LeftGroupOrder

namespace LeftGroupOrder
variable (O : LeftGroupOrder G) (z : G) (hcentral : ∀ g : G, Commute z g)
include hcentral

private theorem mul_upper_bound {x y : G} {m n : ℤ}
    (hx : O.order.le x (z ^ m)) (hy : O.order.le y (z ^ n)) :
    O.order.le (x * y) (z ^ (m + n)) := by
  let := O.order
  have h1 := O.mul_le_mul_left y (z ^ n) x hy
  have h2 := O.mul_le_mul_left x (z ^ m) (z ^ n) hx
  rw [((hcentral x).zpow_left n).eq] at h2
  have h := h1.trans h2
  simpa [← zpow_add, add_comm] using h

private theorem mul_lower_bound {x y : G} {m n : ℤ}
    (hx : O.order.le (z ^ m) x) (hy : O.order.le (z ^ n) y) :
    O.order.le (z ^ (m + n)) (x * y) := by
  let := O.order
  have h1 := O.mul_le_mul_left (z ^ n) y x hy
  have h2 := O.mul_le_mul_left (z ^ m) x (z ^ n) hx
  rw [((hcentral x).zpow_left n).eq] at h2
  have h := h2.trans h1
  simpa [← zpow_add, add_comm] using h

private theorem inv_lower_of_upper {x : G} {n : ℤ}
    (hx : O.order.le x (z ^ n)) : O.order.le (z ^ (-n)) x⁻¹ := by
  have h := O.mul_le_mul_left x (z ^ n) x⁻¹ hx
  rw [inv_mul_cancel, ← ((hcentral x⁻¹).zpow_left n).eq] at h
  have h' := O.mul_le_mul_left 1 (z ^ n * x⁻¹) (z ^ (-n)) h
  simpa [← mul_assoc, ← zpow_add] using h'

private theorem inv_upper_of_lower {x : G} {n : ℤ}
    (hx : O.order.le (z ^ n) x) : O.order.le x⁻¹ (z ^ (-n)) := by
  have h := O.mul_le_mul_left (z ^ n) x x⁻¹ hx
  rw [inv_mul_cancel, ← ((hcentral x⁻¹).zpow_left n).eq] at h
  have h' := O.mul_le_mul_left (z ^ n * x⁻¹) 1 (z ^ (-n)) h
  simpa [← mul_assoc, ← zpow_add] using h'

/-- The elements bounded on both sides by powers of the central element. -/
def centralBoundedSubgroup : Subgroup G where
  carrier := {g | ∃ m n : ℤ, O.order.le (z ^ m) g ∧ O.order.le g (z ^ n)}
  one_mem' := ⟨0, 0, by simp, by simp⟩
  mul_mem' := by
    rintro x y ⟨m, n, hm, hn⟩ ⟨p, q, hp, hq⟩
    exact ⟨m + p, n + q, mul_lower_bound O z hcentral hm hp,
      mul_upper_bound O z hcentral hn hq⟩
  inv_mem' := by
    rintro x ⟨m, n, hm, hn⟩
    exact ⟨-n, -m, inv_lower_of_upper O z hcentral hn, inv_upper_of_lower O z hcentral hm⟩

@[simp] theorem mem_centralBoundedSubgroup (g : G) :
    g ∈ O.centralBoundedSubgroup z hcentral ↔
      ∃ m n : ℤ, O.order.le (z ^ m) g ∧ O.order.le g (z ^ n) := Iff.rfl

/-- The bounded subgroup is convex for the chosen left order. -/
theorem centralBoundedSubgroup_ordConnected :
    (letI := O.order; Set.OrdConnected (O.centralBoundedSubgroup z hcentral : Set G)) := by
  let := O.order
  constructor
  rintro x ⟨m, n, hm, hn⟩ y ⟨p, q, hp, hq⟩ g ⟨hxg, hgy⟩
  exact ⟨m, q, hm.trans hxg, hgy.trans hq⟩

/-- It contains every central power. -/
theorem zpow_mem_centralBoundedSubgroup (k : ℤ) :
    z ^ k ∈ O.centralBoundedSubgroup z hcentral := ⟨k, k, O.order.le_refl _, O.order.le_refl _⟩

/-- The central element is cofinal after restricting to its bounded subgroup. -/
theorem centralBoundedSubgroup_isCofinal :
    (O.restrictSubgroup (O.centralBoundedSubgroup z hcentral)).IsCofinal
      (⟨z, by simpa using O.zpow_mem_centralBoundedSubgroup z hcentral 1⟩ :
        O.centralBoundedSubgroup z hcentral) := by
  intro g
  obtain ⟨m, n, hm, hn⟩ := g.property
  exact ⟨m, n, hm, hn⟩

/-- Ambient cofinality is exactly the assertion that the bounded subgroup is the whole group. -/
theorem isCofinal_iff_centralBoundedSubgroup_eq_top :
    O.IsCofinal z ↔ O.centralBoundedSubgroup z hcentral = ⊤ := by
  constructor
  · intro h
    exact top_unique (fun g _ => h g)
  · intro h g
    have hg : g ∈ O.centralBoundedSubgroup z hcentral := by rw [h]; trivial
    exact hg

/-- Cofinality reduces to bounding any given subgroup-generating family. -/
theorem isCofinal_of_generators_bounded (S : Set G) (hS : Subgroup.closure S = ⊤)
    (hbound : ∀ s ∈ S, ∃ m n : ℤ, O.order.le (z ^ m) s ∧ O.order.le s (z ^ n)) :
    O.IsCofinal z := by
  apply (O.isCofinal_iff_centralBoundedSubgroup_eq_top z hcentral).mpr
  apply top_unique
  rw [← hS]
  exact (Subgroup.closure_le _).mpr hbound

end LeftGroupOrder

/-- For the supplied finite positive generators, the missing cofinality assertion is
exactly a bound on each generator, not a consequence silently provided by finiteness. -/
theorem positiveCone_isCofinal_iff_generator_bounds (P : PositiveCone G)
    (S : Finset G) (hS : Subsemigroup.closure (S : Set G) = P.1)
    (z : G) (hcentral : ∀ g : G, Commute z g) :
    (coneLeftOrder P).IsCofinal z ↔ ∀ s ∈ S, ∃ m n : ℤ,
      (coneLeftOrder P).order.le (z ^ m) s ∧ (coneLeftOrder P).order.le s (z ^ n) := by
  constructor
  · intro h s _
    exact h s
  · intro h
    exact (coneLeftOrder P).isCofinal_of_generators_bounded z hcentral S
      (positiveCone_subgroup_closure P.2 S hS) h

/-- The cone on the central bounded subgroup inherits finite positive generation. -/
theorem centralBoundedSubgroup_semigroupFG (P : PositiveCone G) (hfg : SemigroupFG P.1)
    (z : G) (hcentral : ∀ g : G, Commute z g) :
    SemigroupFG (Subsemigroup.comap
      ((coneLeftOrder P).centralBoundedSubgroup z hcentral).subtype.toMulHom P.1) := by
  apply ConeConvex.semigroupFG_restrict _ hfg
  exact (coneLeftOrder P).centralBoundedSubgroup_ordConnected z hcentral

/-- The convex subgroup bounded by central powers is finitely generated as a group. -/
theorem centralBoundedSubgroup_groupFG (P : PositiveCone G) (hfg : SemigroupFG P.1)
    (z : G) (hcentral : ∀ g : G, Commute z g) :
    Group.FG ((coneLeftOrder P).centralBoundedSubgroup z hcentral) :=
  groupFG_of_semigroupFG_positiveCone (positiveCone_restrict _ P.2)
    (centralBoundedSubgroup_semigroupFG P hfg z hcentral)

/-- Its image under any group homomorphism is finitely generated as well. -/
theorem centralBoundedSubgroup_image_groupFG {H : Type*} [Group H]
    (P : PositiveCone G) (hfg : SemigroupFG P.1)
    (z : G) (hcentral : ∀ g : G, Commute z g) (f : G →* H) :
    Group.FG (f.comp ((coneLeftOrder P).centralBoundedSubgroup z hcentral).subtype).range := by
  let := centralBoundedSubgroup_groupFG P hfg z hcentral
  infer_instance

end FnZPositiveCones
