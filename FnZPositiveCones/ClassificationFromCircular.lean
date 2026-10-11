module

public import FnZPositiveCones.External.NoncofinalPrecone
public import FnZPositiveCones.External.OddReduction
public import FnZPositiveCones.Cone.OppositeFG
public import FnZPositiveCones.Construction

@[expose] public section

/-! An FG-specific classification route: central cofinality is proved
algebraically, so only the isolated circular-order obstruction remains. -/

namespace FnZPositiveCones

/-- The circular odd-rank obstruction already excludes finitely generated
strict cones, since their center is now unconditionally cofinal. -/
theorem oddRank_noFGPositiveCone_of_circular
    (hcircular : CircularOddRankObstructionGoal)
    (n : ℕ) (hn : 2 ≤ n) (hodd : Odd n) : ¬ HasFGPositiveCone (FnZ n) := by
  rintro ⟨S, hS⟩
  let Q : PositiveCone (FnZ n) := ⟨Subsemigroup.closure (S : Set (FnZ n)), hS⟩
  have hQ : SemigroupFG Q.1 := ⟨S, rfl⟩
  have hne : cofinalProductZ (FreeGroup (Fin n)) ≠ 1 := by
    intro he
    have hh := congrArg (fun p : FnZ n => p.2.toAdd) he
    change (1 : ℤ) = 0 at hh
    omega
  have hbad (R : PositiveCone (FnZ n)) (hR : SemigroupFG R.1)
      (hz : cofinalProductZ (FreeGroup (Fin n)) ∈ R.1) : False := by
    have hpos : (coneLeftOrder R).order.lt 1 (cofinalProductZ (FreeGroup (Fin n))) := by
      simpa only [coneLeftOrder_lt, inv_one, one_mul] using hz
    have hc := NoncofinalPrecone.finite_rank_center_cofinal hn R hR
    have hlo : IsOpen ({coneLeftOrder R} : Set (LeftGroupOrder (FnZ n))) :=
      (finiteDetermination_iff_leftOrder_isolated R).mp (semigroupFG_finitelyDetermined R.2 hR)
    exact hcircular n hn hodd (cofinalProductCircularGroupOrder (coneLeftOrder R) hpos hc)
      (isOpen_singleton_cofinalProductCircularGroupOrder (coneLeftOrder R) hpos hc hlo)
  rcases Q.mem_or_mem_opposite hne with hz | hz
  · exact hbad Q hQ hz
  · exact hbad Q.opposite (semigroupFG_opposite hQ) hz

/-- The only remaining input on this route is the circular odd-rank theorem.
This does not assert the stronger isolated-left-order noncofinal obstruction. -/
theorem classification_of_circularOddRankObstruction
    (hcircular : CircularOddRankObstructionGoal) : ClassificationGoal := by
  intro n hn
  constructor
  · intro hfg
    by_contra hne
    exact oddRank_noFGPositiveCone_of_circular hcircular n hn (Nat.not_even_iff_odd.mp hne) hfg
  · exact conditionalEvenRank baseCone n hn

end FnZPositiveCones
