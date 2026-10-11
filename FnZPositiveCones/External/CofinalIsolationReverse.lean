module

public import FnZPositiveCones.External.CofinalCocycle
public import FnZPositiveCones.External.CofinalTopology
public import FnZPositiveCones.External.OrderedActionsCircleRealization

@[expose] public section

/-! Reverse isolation transfer using locally constant representatives and
the finitely many marked free-generator heights. -/

namespace FnZPositiveCones.CofinalIsolationReverse

open scoped Topology
open Filter

universe u
variable {G : Type u} [Group G]

/-- The actual open domain of the cofinal circular quotient. -/
abbrev Domain (G : Type u) [Group G] :=
  {O : LeftGroupOrder (G × Multiplicative ℤ) //
    O.order.lt 1 (cofinalProductZ G) ∧ O.IsCofinal (cofinalProductZ G)}

noncomputable def quotient (O : Domain G) : CircularGroupOrder G :=
  cofinalProductCircularGroupOrder O.1 O.2.1 O.2.2

noncomputable def representative (O : Domain G) (g : G) : G × Multiplicative ℤ :=
  cofinalProductRepresentative O.1 O.2.1 O.2.2 g

/-- A normalized representative is locally constant on the cofinal domain.
For nonidentity elements both inequalities defining its fundamental interval
are strict; the identity representative is constant everywhere. -/
theorem representative_eventually_eq (O : Domain G) (g : G) :
    ∀ᶠ Q : Domain G in 𝓝 O, representative Q g = representative O g := by
  by_cases hg : g = 1
  · subst g
    exact Eventually.of_forall (fun Q => by simp [representative])
  have hlo : ∀ᶠ Q : Domain G in 𝓝 O, Q.1.order.lt 1 (representative O g) :=
    ((isOpen_leftOrder_lt 1 (representative O g)).preimage continuous_subtype_val).mem_nhds
      (cofinalProductRepresentative_pos O.1 O.2.1 O.2.2 hg)
  have hhi : ∀ᶠ Q : Domain G in 𝓝 O,
      Q.1.order.lt (representative O g) (cofinalProductZ G) :=
    ((isOpen_leftOrder_lt (representative O g) (cofinalProductZ G)).preimage
      continuous_subtype_val).mem_nhds
      (O.1.fundamentalRepresentative_mem O.2.1 O.2.2 (g, 1)).2
  filter_upwards [hlo, hhi] with Q hQlo hQhi
  let := Q.1.order
  have hf : O.1.powerFloor O.2.1 O.2.2 (g, 1) = Q.1.powerFloor Q.2.1 Q.2.2 (g, 1) :=
    Q.1.fundamentalRepresentative_unique_exponent Q.2.1 Q.2.2 (g, 1) _ ⟨hQlo.le, hQhi⟩
  simp only [representative, cofinalProductRepresentative, LeftGroupOrder.fundamentalRepresentative, hf]

/-- Fixed left-order sign coordinates are locally constant on this domain. -/
theorem leftSign_eventually_eq (O : Domain G) (a b : G × Multiplicative ℤ) :
    ∀ᶠ Q : Domain G in 𝓝 O, leftOrderSign Q.1 (a, b) = leftOrderSign O.1 (a, b) := by
  have hc : Continuous (fun Q : Domain G => leftOrderSign Q.1 (a, b)) :=
    ((continuous_apply (a, b)).comp
      (show Continuous (leftOrderSign (G := G × Multiplicative ℤ)) from
        continuous_induced_dom)).comp continuous_subtype_val
  exact ((isOpen_discrete ({leftOrderSign O.1 (a, b)} : Set Bool)).preimage hc).mem_nhds rfl

/-- Every circular sign is locally constant in the cofinal quotient. -/
theorem quotient_sign_eventually_eq (O : Domain G) (a b c : G) :
    ∀ᶠ Q : Domain G in 𝓝 O,
      circularOrderSign (quotient Q) (a, b, c) = circularOrderSign (quotient O) (a, b, c) := by
  classical
  filter_upwards [representative_eventually_eq O a, representative_eventually_eq O b,
    representative_eventually_eq O c,
    leftSign_eventually_eq O (representative O a) (representative O b),
    leftSign_eventually_eq O (representative O b) (representative O c),
    leftSign_eventually_eq O (representative O c) (representative O a)] with
    Q ha hb hc hab hbc hca
  have hab' : Q.1.order.lt (representative O a) (representative O b) ↔
      O.1.order.lt (representative O a) (representative O b) := by
    simpa only [leftOrderSign, decide_eq_decide] using hab
  have hbc' : Q.1.order.lt (representative O b) (representative O c) ↔
      O.1.order.lt (representative O b) (representative O c) := by
    simpa only [leftOrderSign, decide_eq_decide] using hbc
  have hca' : Q.1.order.lt (representative O c) (representative O a) ↔
      O.1.order.lt (representative O c) (representative O a) := by
    simpa only [leftOrderSign, decide_eq_decide] using hca
  simp only [circularOrderSign, decide_eq_decide]
  change ((Q.1.order.lt (representative Q a) (representative Q b) ∧
      Q.1.order.lt (representative Q b) (representative Q c)) ∨
    (Q.1.order.lt (representative Q b) (representative Q c) ∧
      Q.1.order.lt (representative Q c) (representative Q a)) ∨
    (Q.1.order.lt (representative Q c) (representative Q a) ∧
      Q.1.order.lt (representative Q a) (representative Q b))) ↔
    ((O.1.order.lt (representative O a) (representative O b) ∧
      O.1.order.lt (representative O b) (representative O c)) ∨
    (O.1.order.lt (representative O b) (representative O c) ∧
      O.1.order.lt (representative O c) (representative O a)) ∨
    (O.1.order.lt (representative O c) (representative O a) ∧
      O.1.order.lt (representative O a) (representative O b)))
  rw [ha, hb, hc, hab', hbc', hca']

/-- The quotient map is continuous on its positive-cofinal domain. -/
theorem continuous_quotient : Continuous (quotient (G := G)) := by
  apply continuous_induced_rng.mpr
  apply continuous_pi
  rintro ⟨a, b, c⟩
  apply continuous_iff_continuousAt.mpr
  intro O
  exact continuousAt_const.congr_of_eventuallyEq (quotient_sign_eventually_eq O a b c)

section FreeGroup
variable {ι : Type u}

/-- With finitely many marked generators their entire integer-height vector
is constant on one neighborhood. -/
theorem generatorHeights_eventually_eq [Finite ι] (O : Domain (FreeGroup ι)) :
    ∀ᶠ Q : Domain (FreeGroup ι) in 𝓝 O,
      cofinalGeneratorHeights Q.1 Q.2.1 Q.2.2 = cofinalGeneratorHeights O.1 O.2.1 O.2.2 := by
  have hh : ∀ᶠ Q : Domain (FreeGroup ι) in 𝓝 O, ∀ i : ι,
      representative Q (FreeGroup.of i) = representative O (FreeGroup.of i) :=
    Filter.eventually_all.mpr (fun i => representative_eventually_eq O (FreeGroup.of i))
  filter_upwards [hh] with Q hQ
  funext i
  exact congrArg (fun g : FreeGroup ι × Multiplicative ℤ => -g.2.toAdd) (hQ i)

/-- The isolated circular quotient and fixed marked heights determine the
complete original left order by the checked cocycle recovery theorem. -/
theorem domain_isolated_of_quotient_isolated [Finite ι] (O : Domain (FreeGroup ι))
    (hi : IsOpen ({quotient O} : Set (CircularGroupOrder (FreeGroup ι)))) :
    IsOpen ({O} : Set (Domain (FreeGroup ι))) := by
  have hq : ∀ᶠ Q : Domain (FreeGroup ι) in 𝓝 O, quotient Q = quotient O :=
    (hi.preimage continuous_quotient).mem_nhds rfl
  have he : ∀ᶠ Q : Domain (FreeGroup ι) in 𝓝 O, Q = O := by
    filter_upwards [hq, generatorHeights_eventually_eq O] with Q hQ hh
    apply Subtype.ext
    have hcones : leftOrderCone Q.1 = leftOrderCone O.1 := by
      rw [← circularFreeProductCone_cofinalProductCircularGroupOrder Q.1 Q.2.1 Q.2.2,
        ← circularFreeProductCone_cofinalProductCircularGroupOrder O.1 O.2.1 O.2.2, hh]
      exact congrArg (circularFreeProductCone (cofinalGeneratorHeights O.1 O.2.1 O.2.2)) hQ
    simpa only [coneLeftOrder_leftOrderCone] using congrArg coneLeftOrder hcones
  apply isOpen_iff_mem_nhds.mpr
  intro Q hQ
  rcases hQ with rfl
  exact he

/-- Reverse isolation transfer on a finite-rank free-group product. The
positive-cofinal locus is open, so subtype isolation is ambient isolation. -/
theorem isOpen_singleton_of_cofinalProductCircularGroupOrder [Finite ι]
    (O : LeftGroupOrder (FreeGroup ι × Multiplicative ℤ))
    (hz : O.order.lt 1 (cofinalProductZ (FreeGroup ι)))
    (hc : O.IsCofinal (cofinalProductZ (FreeGroup ι)))
    (hi : IsOpen ({cofinalProductCircularGroupOrder O hz hc} :
      Set (CircularGroupOrder (FreeGroup ι)))) :
    IsOpen ({O} : Set (LeftGroupOrder (FreeGroup ι × Multiplicative ℤ))) := by
  let Q : Domain (FreeGroup ι) := ⟨O, hz, hc⟩
  have hQ : IsOpen ({Q} : Set (Domain (FreeGroup ι))) :=
    domain_isolated_of_quotient_isolated Q hi
  have hdom := isOpen_positiveCofinal (cofinalProductZ (FreeGroup ι)) cofinalProductZ_central
  simpa only [Set.image_singleton] using hdom.isOpenMap_subtype_val _ hQ

/-- Every checked lift realization of an isolated circular order has an
isolated left order, independently of the chosen realization. -/
theorem liftOrder_isolated [Finite ι] {C : CircularGroupOrder (FreeGroup ι)}
    (R : CircularRealization C) (hi : IsOpen ({C} : Set (CircularGroupOrder (FreeGroup ι)))) :
    IsOpen ({R.liftOrder} : Set (LeftGroupOrder (FreeGroup ι × Multiplicative ℤ))) := by
  apply isOpen_singleton_of_cofinalProductCircularGroupOrder R.liftOrder R.positive R.cofinal
  simpa only [R.quotient_eq] using hi

end FreeGroup
end FnZPositiveCones.CofinalIsolationReverse
