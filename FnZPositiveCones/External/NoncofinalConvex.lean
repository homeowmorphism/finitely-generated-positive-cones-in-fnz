module

public import FnZPositiveCones.External.ConvexExtension
public import FnZPositiveCones.Cone.Opposite

@[expose] public section

/-! Convex layers and finite determination, for MMRT's finite-chain reduction. -/

namespace FnZPositiveCones
namespace NoncofinalConvex

universe u
variable {G : Type u} [Group G]

private theorem convex_of_between (P : PositiveCone G) (K : Subgroup G)
    (h : ∀ {x y z : G}, x ∈ K → z ∈ K → x⁻¹ * y ∈ P.1 → y⁻¹ * z ∈ P.1 → y ∈ K) :
    ConeConvex P K := by
  let := coneLinearOrder P
  constructor
  intro x hx z hz y hy
  rcases hy with ⟨hxy, hyz⟩
  change x = y ∨ x⁻¹ * y ∈ P.1 at hxy
  change y = z ∨ y⁻¹ * z ∈ P.1 at hyz
  rcases hxy with rfl | hxy
  · exact hx
  rcases hyz with rfl | hyz
  · exact hz
  exact h hx hz hxy hyz

/-- Reversing all inequalities preserves convexity. -/
theorem convex_opposite {P : PositiveCone G} {K : Subgroup G} (hK : ConeConvex P K) :
    ConeConvex P.opposite K := by
  apply convex_of_between
  intro x y z hx hz hxy hyz
  change (x⁻¹ * y)⁻¹ ∈ P.1 at hxy
  change (y⁻¹ * z)⁻¹ ∈ P.1 at hyz
  simp only [mul_inv_rev, inv_inv] at hxy hyz
  exact hK.between hz hx hyz hxy

def restrictedCone (P : PositiveCone G) (L : Subgroup G) : PositiveCone L :=
  ⟨Subsemigroup.comap L.subtype.toMulHom P.1, positiveCone_restrict L P.2⟩

/-- Convexity restricts along every subgroup, with the correct subgroup tower. -/
theorem convex_restrict {P : PositiveCone G} {K : Subgroup G} (hK : ConeConvex P K)
    (L : Subgroup G) : ConeConvex (restrictedCone P L) (K.subgroupOf L) := by
  apply convex_of_between
  intro x y z hx hz hxy hyz
  exact hK.between hx hz hxy hyz

/-- Reverse the layer between two convex subgroups, preserving both the lower
subgroup's original signs and every sign outside the upper subgroup. -/
def flipLayer (P : PositiveCone G) (K L : Subgroup G)
    (hK : ConeConvex P K) (hL : ConeConvex P L) : PositiveCone G := by
  let R := restrictedCone P L
  let hinner : ConeConvex R.opposite (K.subgroupOf L) := convex_opposite (convex_restrict hK L)
  let inner := hinner.replaceCone (Subsemigroup.comap (K.subgroupOf L).subtype.toMulHom R.1)
  have hinnerpos : IsPositiveCone inner := hinner.replaceCone_positive
    (positiveCone_restrict (K.subgroupOf L) R.2)
  exact ⟨hL.replaceCone inner, hL.replaceCone_positive hinnerpos⟩

theorem mem_flipLayer_outside {P : PositiveCone G} {K L : Subgroup G}
    (hK : ConeConvex P K) (hL : ConeConvex P L) {g : G} (hg : g ∉ L) :
    g ∈ (flipLayer P K L hK hL).1 ↔ g ∈ P.1 := by
  simp [flipLayer, ConeConvex.replaceCone, hg]

theorem mem_flipLayer_inside {P : PositiveCone G} {K L : Subgroup G}
    (hK : ConeConvex P K) (hL : ConeConvex P L) {g : G} (hgL : g ∈ L) (hgK : g ∈ K) :
    g ∈ (flipLayer P K L hK hL).1 ↔ g ∈ P.1 := by
  simp [flipLayer, ConeConvex.replaceCone, restrictedCone, Subgroup.mem_subgroupOf, hgL, hgK]

theorem mem_flipLayer_layer {P : PositiveCone G} {K L : Subgroup G}
    (hK : ConeConvex P K) (hL : ConeConvex P L) {g : G} (hgL : g ∈ L) (hgK : g ∉ K) :
    g ∈ (flipLayer P K L hK hL).1 ↔ g⁻¹ ∈ P.1 := by
  simp [flipLayer, ConeConvex.replaceCone, restrictedCone, PositiveCone.opposite,
    oppositeSubsemigroup, Subgroup.mem_subgroupOf, hgL, hgK]

private theorem exists_positive_difference (P : PositiveCone G) {K L : Subgroup G}
    (hne : ¬ K ≤ L) : ∃ g : G, g ∈ K ∧ g ∉ L ∧ g ∈ P.1 := by
  have hex : ∃ g : G, g ∈ K ∧ g ∉ L := by
    by_contra h
    apply hne
    intro g hg
    by_contra hn
    exact h ⟨g, hg, hn⟩
  obtain ⟨g, hgK, hgL⟩ := hex
  rcases P.2.2 g with he | hp | hp
  · exact (hgL (he ▸ L.one_mem)).elim
  · exact ⟨g, hgK, hgL, hp⟩
  · refine ⟨g⁻¹, K.inv_mem hgK, ?_, hp⟩
    intro h
    exact hgL (by simpa using L.inv_mem h)

/-- Convex subgroups form a chain; this does not require finite determination. -/
theorem convex_comparable {P : PositiveCone G} {K L : Subgroup G}
    (hK : ConeConvex P K) (hL : ConeConvex P L) : K ≤ L ∨ L ≤ K := by
  classical
  by_cases hKL : K ≤ L
  · exact Or.inl hKL
  right
  obtain ⟨k, hkK, hkL, hkp⟩ := exists_positive_difference P hKL
  let := coneLinearOrder P
  have h1k : (1 : G) ≤ k := by
    change 1 = k ∨ 1⁻¹ * k ∈ P.1
    exact Or.inr (by simpa using hkp)
  have hpos {g : G} (hgL : g ∈ L) (hgp : g ∈ P.1) : g ∈ K := by
    have h1g : (1 : G) ≤ g := by
      change 1 = g ∨ 1⁻¹ * g ∈ P.1
      exact Or.inr (by simpa using hgp)
    rcases le_total g k with hgk | hkg
    · exact hK.out K.one_mem hkK ⟨h1g, hgk⟩
    · exact (hkL (hL.out L.one_mem hgL ⟨h1k, hkg⟩)).elim
  intro g hgL
  rcases P.2.2 g with he | hp | hp
  · exact he ▸ K.one_mem
  · exact hpos hgL hp
  · simpa using K.inv_mem (hpos (L.inv_mem hgL) hp)

/-- A finite determining set must meet every nonempty layer between convex
subgroups. Reversing precisely that layer proves the assertion. -/
theorem determining_set_meets_difference (P : PositiveCone G) (S : Finset G)
    (hSP : (S : Set G) ⊆ (P.1 : Set G))
    (hdet : ∀ Q : Subsemigroup G, IsPositiveCone Q →
      (S : Set G) ⊆ (Q : Set G) → Q = P.1)
    {K L : Subgroup G} (hK : ConeConvex P K) (hL : ConeConvex P L) (hne : ¬ L ≤ K) :
    ∃ s ∈ S, s ∈ L ∧ s ∉ K := by
  by_contra hn
  have hall : ∀ s ∈ S, s ∈ L → s ∈ K := by
    intro s hs hsL
    by_contra hsK
    exact hn ⟨s, hs, hsL, hsK⟩
  have hQ : (S : Set G) ⊆ ((flipLayer P K L hK hL).1 : Set G) := by
    intro s hs
    by_cases hsL : s ∈ L
    · exact (mem_flipLayer_inside hK hL hsL (hall s hs hsL)).mpr (hSP hs)
    · exact (mem_flipLayer_outside hK hL hsL).mpr (hSP hs)
  have heq := hdet _ (flipLayer P K L hK hL).2 hQ
  obtain ⟨g, hgL, hgK, hgp⟩ := exists_positive_difference P hne
  have hgQ : g ∈ (flipLayer P K L hK hL).1 := by rwa [heq]
  exact positiveCone_inv_not_mem P.2 hgp ((mem_flipLayer_layer hK hL hgL hgK).mp hgQ)

/-- MMRT Lemma 4.3 in contrapositive form: an isolated cone has only finitely
many convex subgroups. The proof uses actual alternative strict cones. -/
theorem finite_convex_subgroups (P : PositiveCone G) (hfd : FinitelyDetermined P.1) :
    Set.Finite {K : Subgroup G | ConeConvex P K} := by
  classical
  obtain ⟨S, hSP, hdet⟩ := hfd
  let f : {K : Subgroup G // ConeConvex P K} → (S → Bool) :=
    fun K s => decide ((s : G) ∈ K.1)
  have hf : Function.Injective f := by
    intro K L he
    apply Subtype.ext
    have hmem (s : G) (hs : s ∈ S) : s ∈ K.1 ↔ s ∈ L.1 := by
      have h := congrFun he (⟨s, hs⟩ : S)
      simpa only [f, decide_eq_decide] using h
    apply le_antisymm
    · by_contra hn
      obtain ⟨s, hs, hsK, hsL⟩ := determining_set_meets_difference P S hSP hdet L.2 K.2 hn
      exact hsL ((hmem s hs).mp hsK)
    · by_contra hn
      obtain ⟨s, hs, hsL, hsK⟩ := determining_set_meets_difference P S hSP hdet K.2 L.2 hn
      exact hsK ((hmem s hs).mpr hsL)
  have hfinite : Finite {K : Subgroup G // ConeConvex P K} := Finite.of_injective f hf
  exact Set.finite_coe_iff.mp hfinite

/-- Consequently every proper convex subgroup has a minimal convex overgroup.
This checks the finite-chain reduction preceding MMRT Claim 2. -/
theorem exists_minimal_convex_overgroup (P : PositiveCone G) (hfd : FinitelyDetermined P.1)
    (K : Subgroup G) (hne : K ≠ ⊤) :
    ∃ L : Subgroup G, ConeConvex P L ∧ K < L ∧
      ∀ M : Subgroup G, ConeConvex P M → K < M → M ≤ L → L ≤ M := by
  have hfin : Set.Finite {L : Subgroup G | ConeConvex P L ∧ K < L} :=
    (finite_convex_subgroups P hfd).subset (fun _ h => h.1)
  have htop : ConeConvex P (⊤ : Subgroup G) := by
    let := coneLinearOrder P
    exact Set.ordConnected_univ
  have hnon : ({L : Subgroup G | ConeConvex P L ∧ K < L} : Set (Subgroup G)).Nonempty :=
    ⟨⊤, htop, lt_top_iff_ne_top.mpr hne⟩
  obtain ⟨L, hL, hmin⟩ := hfin.exists_minimal hnon
  exact ⟨L, hL.1, hL.2, fun M hM hKM hML => hmin ⟨hM, hKM⟩ hML⟩

end NoncofinalConvex
end FnZPositiveCones
