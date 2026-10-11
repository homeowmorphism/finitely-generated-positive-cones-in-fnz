module

public import FnZPositiveCones.External.CofinalCocycle
public import FnZPositiveCones.Cone.Opposite
public import FnZPositiveCones.External.OddRank

@[expose] public section

/-! Dynamical interfaces and their conditional adapter. The unconditional inputs
are proved in `CircularIsolatedComplete` and `NoncofinalEndpointAction`. -/
namespace FnZPositiveCones

/-- The isolated-circular-order obstruction, MMRT's ping-pong branch. -/
def CircularOddRankObstructionGoal : Prop :=
  ∀ n : ℕ, 2 ≤ n → Odd n → ∀ O : CircularGroupOrder (FreeGroup (Fin n)),
    ¬ IsOpen ({O} : Set (CircularGroupOrder (FreeGroup (Fin n))))

/-- The finite-rank noncofinal-center obstruction, in the positive
orientation. Equivalently, an isolated order must have cofinal center. -/
def IsolatedOddRankCenterCofinalGoal : Prop :=
  ∀ n : ℕ, 2 ≤ n → Odd n → ∀ P : PositiveCone (FnZ n),
    cofinalProductZ (FreeGroup (Fin n)) ∈ P.1 →
    IsOpen ({P} : Set (PositiveCone (FnZ n))) →
    (coneLeftOrder P).IsCofinal (cofinalProductZ (FreeGroup (Fin n)))

/-- All cone, orientation, cofinal quotient, and topology adapters are checked;
only the two displayed dynamical statements are assumed. -/
theorem oddRankObstruction_of_circular_of_cofinal
    (hcircular : CircularOddRankObstructionGoal)
    (hcofinal : IsolatedOddRankCenterCofinalGoal) : OddRankObstructionGoal := by
  intro n hn hodd P hP hfd
  let Q : PositiveCone (FnZ n) := ⟨P, hP⟩
  have hi : IsOpen ({Q} : Set (PositiveCone (FnZ n))) :=
    (finiteDetermination_iff_isolated Q).mp hfd
  have hne : cofinalProductZ (FreeGroup (Fin n)) ≠ 1 := by
    intro he
    have hh := congrArg (fun p : FnZ n => p.2.toAdd) he
    change (1 : ℤ) = 0 at hh
    omega
  have hbad (R : PositiveCone (FnZ n))
      (hz : cofinalProductZ (FreeGroup (Fin n)) ∈ R.1)
      (hr : IsOpen ({R} : Set (PositiveCone (FnZ n)))) : False := by
    have hpos : (coneLeftOrder R).order.lt 1 (cofinalProductZ (FreeGroup (Fin n))) := by
      simpa only [coneLeftOrder_lt, inv_one, one_mul] using hz
    have hc := hcofinal n hn hodd R hz hr
    have hlo : IsOpen ({coneLeftOrder R} : Set (LeftGroupOrder (FnZ n))) :=
      (finiteDetermination_iff_leftOrder_isolated R).mp
        ((finiteDetermination_iff_isolated R).mpr hr)
    exact hcircular n hn hodd (cofinalProductCircularGroupOrder (coneLeftOrder R) hpos hc)
      (isOpen_singleton_cofinalProductCircularGroupOrder (coneLeftOrder R) hpos hc hlo)
  rcases Q.mem_or_mem_opposite hne with hz | hz
  · exact hbad Q hz hi
  · exact hbad Q.opposite hz ((isOpen_singleton_opposite_iff Q).mpr hi)

end FnZPositiveCones
