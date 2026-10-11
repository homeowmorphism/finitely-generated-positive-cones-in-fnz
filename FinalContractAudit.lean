module

/- Import each module with proof bodies: `import all` is not transitive. -/
import all FnZPositiveCones
import all FnZPositiveCones.Actions.Weighted
import all FnZPositiveCones.Classification
import all FnZPositiveCones.ClassificationFromCircular
import all FnZPositiveCones.Cone.Basic
import all FnZPositiveCones.Cone.Discrete
import all FnZPositiveCones.Cone.Opposite
import all FnZPositiveCones.Cone.OppositeFG
import all FnZPositiveCones.Cone.Topology
import all FnZPositiveCones.Construction.Bound
import all FnZPositiveCones.Construction.Product
import all FnZPositiveCones.Construction.Subgroup
import all FnZPositiveCones.Construction
import all FnZPositiveCones.Cover.BasisSchreier
import all FnZPositiveCones.Cover.BasisWeighted
import all FnZPositiveCones.Cover.ExplicitBasis
import all FnZPositiveCones.Cover.Modular
import all FnZPositiveCones.Cover.SourceCoordinates
import all FnZPositiveCones.External.BaseCone
import all FnZPositiveCones.External.CircularCocycle
import all FnZPositiveCones.External.CircularComponentConfiguration
import all FnZPositiveCones.External.CircularComponentEndpoints
import all FnZPositiveCones.External.CircularCyclicAccumulation
import all FnZPositiveCones.External.CircularDerivedTransfer
import all FnZPositiveCones.External.CircularDomainComponents
import all FnZPositiveCones.External.CircularDynamics
import all FnZPositiveCones.External.CircularDynamicsAffectedObstruction
import all FnZPositiveCones.External.CircularDynamicsAffectedTrace
import all FnZPositiveCones.External.CircularDynamicsCircleDomains
import all FnZPositiveCones.External.CircularDynamicsCircleFilled
import all FnZPositiveCones.External.CircularDynamicsCircleLocal
import all FnZPositiveCones.External.CircularDynamicsCircularHull
import all FnZPositiveCones.External.CircularDynamicsCoincidence
import all FnZPositiveCones.External.CircularDynamicsColors
import all FnZPositiveCones.External.CircularDynamicsCompletion
import all FnZPositiveCones.External.CircularDynamicsDomainTransport
import all FnZPositiveCones.External.CircularDynamicsDomains
import all FnZPositiveCones.External.CircularDynamicsExpansion
import all FnZPositiveCones.External.CircularDynamicsGapDomains
import all FnZPositiveCones.External.CircularDynamicsGapWords
import all FnZPositiveCones.External.CircularDynamicsHull
import all FnZPositiveCones.External.CircularDynamicsLocal
import all FnZPositiveCones.External.CircularDynamicsNormalization
import all FnZPositiveCones.External.CircularDynamicsObstruction
import all FnZPositiveCones.External.CircularDynamicsPrincipalChain
import all FnZPositiveCones.External.CircularDynamicsSeparatedDomains
import all FnZPositiveCones.External.CircularDynamicsSeparation
import all FnZPositiveCones.External.CircularDynamicsSeparationAdapter
import all FnZPositiveCones.External.CircularDynamicsSuccessor
import all FnZPositiveCones.External.CircularDynamicsTraces
import all FnZPositiveCones.External.CircularEndpointMaps
import all FnZPositiveCones.External.CircularExpandedDomains
import all FnZPositiveCones.External.CircularExpandedFiniteArcs
import all FnZPositiveCones.External.CircularExpandedOpen
import all FnZPositiveCones.External.CircularExpandedRegularity
import all FnZPositiveCones.External.CircularExpandedSeparation
import all FnZPositiveCones.External.CircularFGDomains
import all FnZPositiveCones.External.CircularFGPingPong
import all FnZPositiveCones.External.CircularFGSeparation
import all FnZPositiveCones.External.CircularFGSeparationTopology
import all FnZPositiveCones.External.CircularGapConnectivity
import all FnZPositiveCones.External.CircularGapCoordinate
import all FnZPositiveCones.External.CircularInjectivity
import all FnZPositiveCones.External.CircularIntervalAccumulation
import all FnZPositiveCones.External.CircularIntervalFamilies
import all FnZPositiveCones.External.CircularIntervalGaps
import all FnZPositiveCones.External.CircularIntervalSuccessor
import all FnZPositiveCones.External.CircularInvariantAccumulation
import all FnZPositiveCones.External.CircularInvariantComponents
import all FnZPositiveCones.External.CircularIsolatedComplete
import all FnZPositiveCones.External.CircularIsolatedComponents
import all FnZPositiveCones.External.CircularIsolatedDiscrete
import all FnZPositiveCones.External.CircularIsolatedDomains
import all FnZPositiveCones.External.CircularIsolatedReduction
import all FnZPositiveCones.External.CircularIsolatedRobust
import all FnZPositiveCones.External.CircularIsolatedSeparation
import all FnZPositiveCones.External.CircularIsolatedSuccessor
import all FnZPositiveCones.External.CircularLastLetterDensity
import all FnZPositiveCones.External.CircularLastLetterDynamics
import all FnZPositiveCones.External.CircularNormalizedOrbit
import all FnZPositiveCones.External.CircularPrincipalGapPrefixes
import all FnZPositiveCones.External.CircularQuotient
import all FnZPositiveCones.External.CircularSuccessorAccumulation
import all FnZPositiveCones.External.CircularSuffixSeparation
import all FnZPositiveCones.External.CircularTopology
import all FnZPositiveCones.External.CocycleExtension
import all FnZPositiveCones.External.CocycleTopology
import all FnZPositiveCones.External.Cofinal
import all FnZPositiveCones.External.CofinalCocycle
import all FnZPositiveCones.External.CofinalIsolationReverse
import all FnZPositiveCones.External.CofinalTopology
import all FnZPositiveCones.External.ConvexExtension
import all FnZPositiveCones.External.CyclicConvexSubgroups
import all FnZPositiveCones.External.FiniteCentral
import all FnZPositiveCones.External.FreeAbelianSubgroup
import all FnZPositiveCones.External.FreeGroupNonIsolation
import all FnZPositiveCones.External.FreeGroupOrbitPerturbation
import all FnZPositiveCones.External.InfiniteRank
import all FnZPositiveCones.External.IsolatedQuotientCone
import all FnZPositiveCones.External.Noncofinal
import all FnZPositiveCones.External.NoncofinalComponentPerturbation
import all FnZPositiveCones.External.NoncofinalConvex
import all FnZPositiveCones.External.NoncofinalConvexJump
import all FnZPositiveCones.External.NoncofinalConvexJumpAdapter
import all FnZPositiveCones.External.NoncofinalCrossingExistence
import all FnZPositiveCones.External.NoncofinalCrossings
import all FnZPositiveCones.External.NoncofinalDenseAction
import all FnZPositiveCones.External.NoncofinalDynamics
import all FnZPositiveCones.External.NoncofinalEndpointAction
import all FnZPositiveCones.External.NoncofinalEnvelope
import all FnZPositiveCones.External.NoncofinalFiniteModel
import all FnZPositiveCones.External.NoncofinalFixedCrossing
import all FnZPositiveCones.External.NoncofinalFixedPoints
import all FnZPositiveCones.External.NoncofinalFlexibleComponents
import all FnZPositiveCones.External.NoncofinalFreeCone
import all FnZPositiveCones.External.NoncofinalFreeSubgroup
import all FnZPositiveCones.External.NoncofinalFreeTower
import all FnZPositiveCones.External.NoncofinalFreeTowerModel
import all FnZPositiveCones.External.NoncofinalIsolatedReduction
import all FnZPositiveCones.External.NoncofinalIsolatedTower
import all FnZPositiveCones.External.NoncofinalIsolationAdapter
import all FnZPositiveCones.External.NoncofinalMinimalAction
import all FnZPositiveCones.External.NoncofinalPerturbation
import all FnZPositiveCones.External.NoncofinalPrecone
import all FnZPositiveCones.External.NoncofinalPrimitiveEntry
import all FnZPositiveCones.External.NoncofinalPrimitiveTranslate
import all FnZPositiveCones.External.NoncofinalQuotientCone
import all FnZPositiveCones.External.NoncofinalRayPerturbation
import all FnZPositiveCones.External.NoncofinalSubgroupProduct
import all FnZPositiveCones.External.NoncofinalTrajectory
import all FnZPositiveCones.External.OddRank
import all FnZPositiveCones.External.OddRankComplete
import all FnZPositiveCones.External.OddRankObstruction
import all FnZPositiveCones.External.OddReduction
import all FnZPositiveCones.External.OrderedActions
import all FnZPositiveCones.External.OrderedActionsCircle
import all FnZPositiveCones.External.OrderedActionsCircleGaps
import all FnZPositiveCones.External.OrderedActionsCircleRealization
import all FnZPositiveCones.External.OrderedActionsCollapse
import all FnZPositiveCones.External.OrderedActionsCompletion
import all FnZPositiveCones.External.OrderedActionsDiscrete
import all FnZPositiveCones.External.OrderedActionsFactorFibers
import all FnZPositiveCones.External.OrderedActionsFill
import all FnZPositiveCones.External.OrderedActionsGapAction
import all FnZPositiveCones.External.OrderedActionsGaps
import all FnZPositiveCones.External.OrderedActionsHolder
import all FnZPositiveCones.External.OrderedActionsRealization
import all FnZPositiveCones.External.OrderedActionsSemiconjugacy
import all FnZPositiveCones.External.OrderedActionsStabilizer
import all FnZPositiveCones.External.OrderedActionsTranslation
import all FnZPositiveCones.External.PingPongCircleComponents
import all FnZPositiveCones.External.PingPongCombinatorics
import all FnZPositiveCones.External.PingPongGapPotential
import all FnZPositiveCones.External.PingPongGapSurjection
import all FnZPositiveCones.External.PingPongGaps
import all FnZPositiveCones.Gamma.Basic
import all FnZPositiveCones.Gamma.Certificate
import all FnZPositiveCones.Gamma.Isomorphism
import all FnZPositiveCones.Gamma.MarkedProduct
import all FnZPositiveCones.Gamma.PositiveCone
import all FnZPositiveCones.Gamma.Schreier
import all FnZPositiveCones.Gamma.Weighted
import all FnZPositiveCones.Interfaces
import all FnZPositiveCones.Main
import all FnZPositiveCones.Schreier.Positive

noncomputable section

-- Check the whole retained library, including private and generated declarations.
-- Module origins, rather than declaration namespaces, determine project membership.
open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env := (← getEnv).setExporting false
  let isProjectModule (n : Name) :=
    n == `FnZPositiveCones || n.toString.startsWith "FnZPositiveCones."
  let modules := env.header.modules.filter (isProjectModule ·.module)
  unless !modules.isEmpty do
    throwError "No project modules loaded for the axiom audit"
  for mod in modules do
    unless mod.importAll do
      throwError "Project module needs an explicit import all for auditing: {mod.module}"
  let names : Array Name := env.constants.fold (init := #[]) fun names name _ =>
    match env.getModuleIdxFor? name with
    | some idx =>
      if isProjectModule env.header.moduleNames[idx.toNat]! then names.push name else names
    | none => names
  unless !names.isEmpty do
    throwError "No project declarations found for the axiom audit"
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in names do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "Project declaration {name} uses forbidden axiom {axiomName}"
  logInfo m!"Standard-axiom audit passed for {names.size} declarations in {modules.size} project modules"

open FnZPositiveCones
open CircularDynamics

example : BaseConeGoal → EvenRankGoal := conditionalEvenRank
example : BaseConeGoal → OddRankObstructionGoal → ClassificationGoal := conditionalClassification
example : ∀ n : ℕ, 2 ≤ n → Even n →
    HasFGPositiveCone (FreeGroup (Fin n) × Multiplicative ℤ) := evenRank_hasFGPositiveCone
example : ∀ n : ℕ, 2 ≤ n →
    (HasFGPositiveCone (FreeGroup (Fin n) × Multiplicative ℤ) ↔ Even n) :=
  hasFGPositiveCone_iff_even
example : ∀ n : ℕ, 2 ≤ n → Odd n → ∀ O : LeftGroupOrder
    (FreeGroup (Fin n) × Multiplicative ℤ), ¬IsOpen ({O} : Set _) :=
  mmrt_no_isolated_order_odd
example : ∀ n : ℕ, 2 ≤ n → Odd n → ∀ P : Subsemigroup
    (FreeGroup (Fin n) × Multiplicative ℤ), IsPositiveCone P → ¬FinitelyDetermined P :=
  oddRankObstruction
example : CircularOddRankObstructionGoal := circularOddRankObstruction
example : IsolatedOddRankCenterCofinalGoal := NoncofinalEndpointAction.isolatedOddRankCenterCofinal
example : ∀ n : ℕ, 2 ≤ n → Even n →
    HasFGPositiveConeWithBound (FreeGroup (Fin n) × Multiplicative ℤ) (6 * (n - 1) + 1) :=
  evenRank_generator_bound
example : HasFGPositiveCone (FreeGroup (Fin 2) × Multiplicative ℤ) :=
  evenRank_hasFGPositiveCone 2 (by decide) (by decide)
example : HasFGPositiveConeWithBound (FreeGroup (Fin 2) × Multiplicative ℤ) 7 :=
  evenRank_generator_bound 2 (by decide) (by decide)
example : ¬HasFGPositiveCone (FreeGroup (Fin 3) × Multiplicative ℤ) :=
  oddRank_noFGPositiveCone_unconditional 3 (by decide) (by decide)

example : (1 : Gamma2) ∉ Subsemigroup.closure ({aGamma, bGamma} : Set Gamma2) :=
  base_one_not_mem
example : ∀ g : Gamma2, g = 1 ∨
    g ∈ Subsemigroup.closure ({aGamma, bGamma} : Set Gamma2) ∨
    g⁻¹ ∈ Subsemigroup.closure ({aGamma, bGamma} : Set Gamma2) := base_total
example : H_marked_product_equiv gammaC =
    productY⁻¹ * productX⁻¹ * productY * productX * productZ⁻¹ := psi_C
example : Function.LeftInverse H_marked_product_equiv.symm H_marked_product_equiv :=
  H_marked_product_equiv.symm_apply_apply
example : Function.RightInverse H_marked_product_equiv.symm H_marked_product_equiv :=
  H_marked_product_equiv.apply_symm_apply
example (d : ℕ) [NeZero d] : coverSubgroup d ≃* FreeGroup (Fin (d + 1)) := coverRankEquiv d
example : coverSubgroup 1 ≃* FreeGroup (Fin 2) := coverRankEquiv 1
example (d : ℕ) [NeZero d] : Subgroup gammaH := secondSubgroup markedProjection d
example (d : ℕ) [NeZero d] : secondSubgroup markedProjection d ≃* FnZ (d + 1) :=
  secondSubgroupFnZEquiv H_marked_product_equiv d (coverRankEquiv d)
example (d : ℕ) (hd : Odd d) : IsUnit (2 : ZMod d) := two_isUnit_of_odd d hd
example : IsUnit (2 : ZMod 9) := two_isUnit_of_odd 9 (by decide)

example {G : Type*} [Group G] {K : Subgroup G} {T : Set G}
    (hT : Subgroup.IsComplement (K : Set G) T) (g : G) :
    g * (rightRep hT g)⁻¹ ∈ K := mul_rightRep_inv_mem hT g
example {G : Type*} [Group G] {K : Subgroup G} {T S : Set G}
    (hT : Subgroup.IsComplement (K : Set G) T) :
    (1 : K) ∉ positiveSchreierSet hT S := by
  rintro ⟨t, ht, s, hs, he, hn⟩
  exact hn rfl
example {G : Type*} [Group G] {K : Subgroup G} {T S : Set G}
    (hT : Subgroup.IsComplement (K : Set G) T) (hT1 : (1 : G) ∈ T)
    {P : Subsemigroup G} (hP : IsPositiveCone P) (hS : P = Subsemigroup.closure S)
    (hpos : ∀ t ∈ T, ∀ s ∈ S,
      schreierDelta hT t s = 1 ∨ (schreierDelta hT t s : G) ∈ P) :
    Subsemigroup.comap K.subtype.toMulHom P =
      Subsemigroup.closure (positiveSchreierSet hT S) :=
  positiveSchreier_closure_eq hT hT1 hP hS hpos

example {ι : Type*} [Finite ι] [Nontrivial ι]
    {C : CircularGroupOrder (FreeGroup ι)} (R : CircularRealization C)
    (hi : IsOpen ({C} : Set _)) (s t : ι × Bool) (hst : s ≠ t) :
    Disjoint (closure (letterOrbit (realizationGenerators R) 0 s))
      (closure (letterOrbit (realizationGenerators R) 0 t)) :=
  R.firstLetter_closures_disjoint_of_isolated hi s t hst
example {ι : Type*} [DecidableEq ι] [Nonempty ι] [Finite ι]
    {C : CircularGroupOrder (FreeGroup ι)} (R : CircularRealization C)
    (h : FreeGroup ι) (hh : C.IsSuccessor h)
    (hsep : ∀ s t, s ≠ t →
      Disjoint (closure (letterOrbit (realizationGenerators R) 0 s))
        (closure (letterOrbit (realizationGenerators R) 0 t))) :
    FiniteNormalizedDomains R := finiteNormalizedDomains R h hh hsep

#print axioms positiveSchreier_closure_eq
#print axioms positiveSchreier_finiteGeneration
#print axioms weightedRightAction_mul
#print axioms stabilizerWeightHom
#print axioms base_one_not_mem
#print axioms base_total
#print axioms H_marked_product_equiv
#print axioms psi_C
#print axioms coverRankEquiv
#print axioms conditionalEvenRank
#print axioms conditionalClassification
#print axioms evenRank_hasFGPositiveCone
#print axioms evenRank_generator_bound
#print axioms hasFGPositiveCone_iff_even
#print axioms NoncofinalEndpointAction.isolatedOddRankCenterCofinal
#print axioms CircularRealization.firstLetter_closures_disjoint_of_isolated
#print axioms circularOddRankObstruction
#print axioms mmrt_no_isolated_order_odd
#print axioms oddRankObstruction

-- Traverse proof constants rather than imports: the geometry module also
-- contains FG constructors, which are not used by the isolated-order proof.
open Lean in
run_cmd do
  let env ← getEnv
  let mut todo : Array Name := #[``mmrt_no_isolated_order_odd]
  let mut seen : Std.HashSet Name := {}
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    if !seen.contains n then
      seen := seen.insert n
      let some ci := env.find? n |
        throwError "Project dependency unavailable to proof traversal: {n}"
      let deps := ci.type.getUsedConstants ++
        ((ci.value? true).map Expr.getUsedConstants |>.getD #[])
      for m in deps do
        if (privateToUserName m).toString.startsWith "FnZPositiveCones." then
          todo := todo.push m
  for n in [``NoncofinalPrecone.center_cofinal_of_semigroupFG,
      ``hasFGPositiveCone_exists_finiteNormalizedDomains,
      ``semigroupFG_exists_finiteNormalizedDomains] do
    if seen.contains n then
      throwError "Unexpected FG-only theorem in O00 proof dependency closure: {n}"
    logInfo m!"O00 does not depend on FG-only theorem: {n}"
  for n in [``NormalizedIntervalData.even_card,
      ``NormalizedIntervalData.backward_forward,
      ``CircularDynamics.finiteNormalizedDomains,
      ``NoncofinalEndpointAction.isolatedOddRankCenterCofinal,
      ``isolatedCircularSeparation] do
    unless seen.contains n do
      throwError "Expected checked prerequisite absent from O00 dependency traversal: {n}"
    logInfo m!"O00 checked prerequisite present: {n}"
