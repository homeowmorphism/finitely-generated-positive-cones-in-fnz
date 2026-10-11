module

import all FnZPositiveCones

/-! Kernel axiom audit for the implemented source-correspondence results. -/
#print FnZPositiveCones.EvenRankGoal
#print FnZPositiveCones.ClassificationGoal
#print FnZPositiveCones.LeftOrderOddRankObstructionGoal
#print FnZPositiveCones.OddRankObstructionGoal
#check FnZPositiveCones.mmrt_no_isolated_order_odd
#check FnZPositiveCones.oddRankObstruction
#print axioms FnZPositiveCones.mmrt_no_isolated_order_odd
#print axioms FnZPositiveCones.oddRankObstruction
example : ∀ n : ℕ, 2 ≤ n → Odd n →
    ∀ O : FnZPositiveCones.LeftGroupOrder
      (FreeGroup (Fin n) × Multiplicative ℤ), ¬ IsOpen {O} :=
  FnZPositiveCones.mmrt_no_isolated_order_odd
example : ∀ n : ℕ, 2 ≤ n → Odd n →
    ∀ P : Subsemigroup (FreeGroup (Fin n) × Multiplicative ℤ),
      FnZPositiveCones.IsPositiveCone P →
        ¬ FnZPositiveCones.FinitelyDetermined P :=
  FnZPositiveCones.oddRankObstruction
#check FnZPositiveCones.hasFGPositiveCone_iff_even
#print axioms FnZPositiveCones.hasFGPositiveCone_iff_even
#print axioms FnZPositiveCones.even_of_hasFGPositiveCone
example : ∀ n : ℕ, 2 ≤ n →
    (FnZPositiveCones.HasFGPositiveCone
      (FreeGroup (Fin n) × Multiplicative ℤ) ↔ Even n) :=
  FnZPositiveCones.hasFGPositiveCone_iff_even
example : ¬FnZPositiveCones.HasFGPositiveCone
    (FreeGroup (Fin 3) × Multiplicative ℤ) :=
  FnZPositiveCones.oddRank_noFGPositiveCone_unconditional 3 (by decide) (by decide)
#print axioms FnZPositiveCones.positiveCone_rigidity
#print axioms FnZPositiveCones.positiveCone_transport
#print axioms FnZPositiveCones.finiteGenerationImpliesFiniteDetermination
#print axioms FnZPositiveCones.finiteDetermination_iff_leftOrder_isolated
#print axioms FnZPositiveCones.positiveConeHomeomorphLeftOrder
#print axioms FnZPositiveCones.positiveSchreier_closure_eq
#print axioms FnZPositiveCones.positiveSchreier_finiteGeneration
#print axioms FnZPositiveCones.weightedRightAction_mul
#print axioms FnZPositiveCones.stabilizerWeightHom
#print axioms FnZPositiveCones.gamma_sandwich_mem
#print axioms FnZPositiveCones.gammaH_index
#print axioms FnZPositiveCones.gammaH_generators
#print axioms FnZPositiveCones.base_one_not_mem
#print axioms FnZPositiveCones.base_total
#print axioms FnZPositiveCones.baseCone
#print axioms FnZPositiveCones.gammaH_positive_generators
#print axioms FnZPositiveCones.sixWeightTable_relations
#print axioms FnZPositiveCones.gammaWeightHom_comp_markedProduct
#print axioms FnZPositiveCones.H_marked_product_equiv
#print axioms FnZPositiveCones.psi_C
#print axioms FnZPositiveCones.cover_stabilizer_index
#print axioms FnZPositiveCones.doubling_orbit_parity
#print axioms FnZPositiveCones.doubling_even_two_orbits
#print axioms FnZPositiveCones.sourceRelabel
#print axioms FnZPositiveCones.sourceRelabel_conjugates_x
#print axioms FnZPositiveCones.sourceRelabel_conjugates_y
#print axioms FnZPositiveCones.staggeredX_fixed_iff
#print axioms FnZPositiveCones.staggeredY_fixed_iff
#print axioms FnZPositiveCones.sourceAlternatingWord_state
#print axioms FnZPositiveCones.oddRankObstruction_of_leftOrderObstruction
#print axioms FnZPositiveCones.oddRank_noFGPositiveCone
#print axioms FnZPositiveCones.coverRankEquiv
#print axioms FnZPositiveCones.secondSubgroupProductEquiv
#print axioms FnZPositiveCones.secondSubgroupFGCone
#check FnZPositiveCones.conditionalEvenRank
#check FnZPositiveCones.conditionalClassification
#check FnZPositiveCones.evenRank_hasFGPositiveCone
#print axioms FnZPositiveCones.conditionalEvenRank
#print axioms FnZPositiveCones.conditionalClassification
#print axioms FnZPositiveCones.evenRank_hasFGPositiveCone
#check FnZPositiveCones.evenRank_generator_bound
#print axioms FnZPositiveCones.evenRank_generator_bound
#print axioms FnZPositiveCones.MMRTParity.even_of_one_boundary
#print axioms FnZPositiveCones.InfiniteFreeRank.not_finitelyDetermined
#print axioms FnZPositiveCones.ConeConvex.finitelyDetermined_restrict
#print axioms FnZPositiveCones.LeftGroupOrder.exists_unique_power_floor
#print axioms FnZPositiveCones.isOpen_singleton_of_continuous_local_section
#print axioms FnZPositiveCones.ConeConvex.semigroupFG_restrict
#print axioms FnZPositiveCones.centralBoundedSubgroup_groupFG
#print axioms FnZPositiveCones.positiveCone_isCofinal_iff_generator_bounds
#print axioms FnZPositiveCones.cofinalProductCircularGroupOrder
#print axioms FnZPositiveCones.CircularGroupOrder.toNormalizedIntCocycle_isCircular
#print axioms FnZPositiveCones.NormalizedIntCocycle.freeProductEquiv
#print axioms FnZPositiveCones.NormalizedIntCocycle.freeProductPositive_isPositiveCone
#print axioms FnZPositiveCones.isOpen_positiveCofinal
#print axioms FnZPositiveCones.NormalizedIntCocycle.continuous_freeProductCone
#print axioms FnZPositiveCones.NormalizedIntCocycle.freeProductCone_injective
#print axioms FnZPositiveCones.continuous_circularFreeProductCone
#print axioms FnZPositiveCones.isOpen_singleton_of_circularFreeProductCone
#print axioms FnZPositiveCones.finitelyDetermined_opposite_iff
#print axioms FnZPositiveCones.cofinalProductCocycle_eq_circular
#print axioms FnZPositiveCones.cofinalProductExtensionEquiv
#print axioms FnZPositiveCones.circularFreeProductCone_cofinalProductCircularGroupOrder
#print axioms FnZPositiveCones.isOpen_singleton_cofinalProductCircularGroupOrder
#print FnZPositiveCones.CircularOddRankObstructionGoal
#print FnZPositiveCones.IsolatedOddRankCenterCofinalGoal
#check FnZPositiveCones.oddRankObstruction_of_circular_of_cofinal
#print axioms FnZPositiveCones.oddRankObstruction_of_circular_of_cofinal

example : ∀ n : ℕ, 2 ≤ n → Even n →
    FnZPositiveCones.HasFGPositiveCone (FreeGroup (Fin n) × Multiplicative ℤ) :=
  FnZPositiveCones.evenRank_hasFGPositiveCone

example : FnZPositiveCones.HasFGPositiveCone (FreeGroup (Fin 2) × Multiplicative ℤ) :=
  FnZPositiveCones.evenRank_hasFGPositiveCone 2 (by decide) (by decide)
