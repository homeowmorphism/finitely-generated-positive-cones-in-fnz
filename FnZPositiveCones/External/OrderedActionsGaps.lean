module

public import FnZPositiveCones.External.OrderedActionsDiscrete

@[expose] public section

namespace FnZPositiveCones
universe u
variable {G : Type u} [Group G]

/-- A product element in the fundamental interval is the representative of its projection. -/
theorem cofinalProductRepresentative_eq_of_mem (O : LeftGroupOrder (G × Multiplicative ℤ))
    (hz : O.order.lt 1 (cofinalProductZ G)) (hc : O.IsCofinal (cofinalProductZ G))
    (a : G × Multiplicative ℤ) (ha : O.order.le 1 a ∧ O.order.lt a (cofinalProductZ G)) :
    cofinalProductRepresentative O hz hc a.1 = a := by
  have haf := O.fundamentalRepresentative_eq_self hz hc ha
  have he : a = cofinalProductZ G ^ a.2.toAdd * (a.1, 1) := by
    apply Prod.ext
    · simp [cofinalProductZ]
    · apply Multiplicative.toAdd.injective
      simp [cofinalProductZ]
  change O.fundamentalRepresentative hz hc (a.1, 1) = a
  rw [he, O.fundamentalRepresentative_zpow_mul] at haf
  exact haf.trans he.symm

namespace CircularRealization
variable {C : CircularGroupOrder G} (R : CircularRealization C)

/-- A circular successor is a least-positive step in the normalized real lift. -/
theorem leastPositive_of_successor {a : G} (ha : C.IsSuccessor a) :
    R.liftOrder.IsLeastPositive (cofinalProductRepresentative R.liftOrder R.positive R.cofinal a) := by
  let := R.liftOrder.order
  let b := cofinalProductRepresentative R.liftOrder R.positive R.cofinal a
  have hb := R.liftOrder.fundamentalRepresentative_mem R.positive R.cofinal (a, 1)
  have hbne : b ≠ 1 := by
    intro he
    apply ha.1
    simpa [b] using congrArg Prod.fst he
  refine ⟨lt_of_le_of_ne hb.1 hbne.symm, ?_⟩
  intro g hg
  by_contra hn
  have hgb : g < b := lt_of_not_ge hn
  have hgz : g < cofinalProductZ G := hgb.trans hb.2
  have hr := cofinalProductRepresentative_eq_of_mem R.liftOrder R.positive R.cofinal g ⟨hg.le, hgz⟩
  apply ha.2 g.1
  have h : (cofinalProductCircularGroupOrder R.liftOrder R.positive R.cofinal).order.sbtw 1 g.1 a := by
    rw [cofinalProductCircularGroupOrder_sbtw_one, hr]
    exact ⟨hg, hgb⟩
  exact Eq.mp (congrArg (fun Q : CircularGroupOrder G => Q.order.sbtw 1 g.1 a) R.quotient_eq) h

/-- Complementary real gaps are one translated family for a specified circular successor. -/
theorem real_gap_is_translate {a : G} (ha : C.IsSuccessor a) {x : ℝ}
    (hx : x ∉ closure (Set.range (fun g => R.realLift.action g R.realLift.base))) :
    ∃ g : G × Multiplicative ℤ,
      R.realLift.action g R.realLift.base < x ∧
      x < R.realLift.action g (R.realLift.action
        (cofinalProductRepresentative R.liftOrder R.positive R.cofinal a) R.realLift.base) ∧
      Disjoint (Set.Ioo (R.realLift.action g R.realLift.base)
        (R.realLift.action g (R.realLift.action
          (cofinalProductRepresentative R.liftOrder R.positive R.cofinal a) R.realLift.base)))
        (closure (Set.range (fun k => R.realLift.action k R.realLift.base))) :=
  R.realLift.gap_is_translate (R.leastPositive_of_successor ha) hx

end CircularRealization
end FnZPositiveCones
