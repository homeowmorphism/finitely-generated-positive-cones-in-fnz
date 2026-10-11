module

public import FnZPositiveCones.External.FiniteCentral

@[expose] public section

/-!
# Algebraic parts of the noncofinal-center argument

The infinite-index conclusion of MMRT Proposition 4.12, Claim 3, follows
directly from convexity, without a dynamical realization or normality.
-/

namespace FnZPositiveCones
universe u
variable {G : Type u} [Group G]

namespace LeftGroupOrder

/-- A convex subgroup contains every positive root of each of its elements. -/
theorem mem_convex_of_pow_mem (O : LeftGroupOrder G) (K : Subgroup G)
    (hK : letI := O.order; Set.OrdConnected (K : Set G))
    {g : G} {n : ℕ} (hn : 0 < n) (hpow : g ^ n ∈ K) : g ∈ K := by
  let := O.order
  have hpositive {a : G} (ha : 1 ≤ a) (haK : a ^ n ∈ K) : a ∈ K := by
    have hmono : Monotone (fun k : ℕ => a ^ k) := by
      apply monotone_nat_of_le_succ
      intro k
      simpa only [mul_one, pow_succ] using O.mul_le_mul_left 1 a (a ^ k) ha
    apply hK.out K.one_mem haK
    exact ⟨ha, by simpa only [pow_one] using hmono (by omega : 1 ≤ n)⟩
  rcases le_total 1 g with hg | hg
  · exact hpositive hg hpow
  · have hi : 1 ≤ g⁻¹ := by
      simpa only [inv_mul_cancel, mul_one] using O.mul_le_mul_left g 1 g⁻¹ hg
    have hiK : g⁻¹ ∈ K := hpositive hi (by simpa using K.inv_mem hpow)
    simpa using K.inv_mem hiK

/-- A finite-index convex subgroup of a left-ordered group is the entire group. -/
theorem convex_eq_top_of_index_ne_zero (O : LeftGroupOrder G) (K : Subgroup G)
    (hK : letI := O.order; Set.OrdConnected (K : Set G)) (hi : K.index ≠ 0) : K = ⊤ := by
  apply top_unique
  intro g _
  obtain ⟨n, hn, _, hgn⟩ := Subgroup.exists_pow_mem_of_index_ne_zero hi g
  exact O.mem_convex_of_pow_mem K hK hn hgn

/-- MMRT Proposition 4.12, Claim 3, for arbitrary proper convex subgroups.
Mathlib records infinite subgroup index as `index = 0`. -/
theorem convex_index_eq_zero (O : LeftGroupOrder G) (K : Subgroup G)
    (hK : letI := O.order; Set.OrdConnected (K : Set G)) (hne : K ≠ ⊤) : K.index = 0 := by
  by_contra hi
  exact hne (O.convex_eq_top_of_index_ne_zero K hK hi)

/-- The subgroup bounded by central powers has infinite index when the center
is not cofinal. No normality of that subgroup is assumed. -/
theorem centralBoundedSubgroup_index_eq_zero (O : LeftGroupOrder G) (z : G)
    (hcentral : ∀ g : G, Commute z g) (hnon : ¬ O.IsCofinal z) :
    (O.centralBoundedSubgroup z hcentral).index = 0 := by
  apply O.convex_index_eq_zero _ (O.centralBoundedSubgroup_ordConnected z hcentral)
  exact fun h => hnon ((O.isCofinal_iff_centralBoundedSubgroup_eq_top z hcentral).mpr h)

end LeftGroupOrder
end FnZPositiveCones
