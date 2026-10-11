module

public import FnZPositiveCones.Gamma.Isomorphism
public import FnZPositiveCones.Cover.ExplicitBasis
public import FnZPositiveCones.Construction.Product
public import FnZPositiveCones.Construction.Bound
public import FnZPositiveCones.External.BaseCone

@[expose] public section

/-! The supporting construction in every even free rank, including rank two.
The paper's main theorem is stated in `Main.lean`. -/
namespace FnZPositiveCones

/-- The conditional construction separates the local subgroup argument from the base cone. -/
theorem conditionalEvenRank : ConditionalEvenRankGoal := by
  intro hbase n hn hEven
  obtain ⟨d, rfl⟩ : ∃ d, n = d + 1 := ⟨n - 1, by omega⟩
  have hd : 0 < d := by omega
  let : NeZero d := ⟨by omega⟩
  have hodd : Odd d := by
    obtain ⟨k, hk⟩ := hEven
    exact ⟨k - 1, by omega⟩
  have hcone := secondSubgroup_hasFGPositiveCone markedProjection d
    markedProjection_C hodd hbase
  exact hasFGPositiveCone_transport
    (secondSubgroupFnZEquiv H_marked_product_equiv d (coverRankEquiv d)) hcone

/-- The constructed cone needs at most six generators per cover sheet and one wrap generator. -/
theorem conditionalEvenRankBound (hbase : BaseConeGoal) : BoundedEvenRankGoal := by
  intro n hn hEven
  obtain ⟨d, rfl⟩ : ∃ d, n = d + 1 := ⟨n - 1, by omega⟩
  let : NeZero d := ⟨by omega⟩
  have hodd : Odd d := by
    obtain ⟨k, hk⟩ := hEven
    exact ⟨k - 1, by omega⟩
  have hcone := secondSubgroup_hasFGPositiveConeWithBound markedProjection d
    markedProjection_C hodd hbase
  exact hasFGPositiveConeWithBound_transport
    (secondSubgroupFnZEquiv H_marked_product_equiv d (coverRankEquiv d)) hcone

/-- An unconditional upper bound; no optimality is asserted. -/
theorem evenRank_generator_bound : BoundedEvenRankGoal := conditionalEvenRankBound baseCone

end FnZPositiveCones
