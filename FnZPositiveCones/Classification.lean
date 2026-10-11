module

public import FnZPositiveCones.Cone.Basic
public import FnZPositiveCones.Construction
public import FnZPositiveCones.External.CircularGapConnectivity

@[expose] public section

/-! Supporting parity and classification lemmas, including the conditional
milestones. The paper's main classification theorem is stated in `Main.lean`. -/

namespace FnZPositiveCones

/-- Under the odd-rank obstruction, no finitely generated positive cone exists in odd rank. -/
theorem oddRank_noFGPositiveCone (hobs : OddRankObstructionGoal)
    (n : ℕ) (hn : 2 ≤ n) (hodd : Odd n) : ¬ HasFGPositiveCone (FnZ n) := by
  rintro ⟨S, hS⟩
  exact hobs n hn hodd _ hS (semigroupFG_finitelyDetermined hS ⟨S, rfl⟩)

/-- Parity classification follows from the existence and obstruction theorems. -/
theorem classification_of_evenRank_of_oddRankObstruction
    (hex : EvenRankGoal) (hobs : OddRankObstructionGoal) : ClassificationGoal := by
  intro n hn
  constructor
  · intro hfg
    by_contra hne
    exact oddRank_noFGPositiveCone hobs n hn (Nat.not_even_iff_odd.mp hne) hfg
  · exact hex n hn

/-- The requested conditional classification milestone, with both hypotheses explicit. -/
theorem conditionalClassification : ConditionalClassificationGoal := by
  intro hbase hobs
  exact classification_of_evenRank_of_oddRankObstruction (conditionalEvenRank hbase) hobs

/-- The remaining classification input is precisely the odd-rank obstruction. -/
theorem classification_of_oddRankObstruction (hobs : OddRankObstructionGoal) :
    ClassificationGoal :=
  classification_of_evenRank_of_oddRankObstruction (conditionalEvenRank baseCone) hobs

/-- A finitely generated strict cone supplies the actual normalized circle
domains and successor. Their checked endpoint-gap argument forces even rank. -/
theorem even_of_hasFGPositiveCone (n : ℕ) (hn : 2 ≤ n)
    (hfg : HasFGPositiveCone (FreeGroup (Fin n) × Multiplicative ℤ)) : Even n := by
  let : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  obtain ⟨C, R, ⟨D⟩, a, ha⟩ := hasFGPositiveCone_exists_finiteNormalizedDomains n hn hfg
  simpa only [Fintype.card_fin] using D.intervalData.even_card ha

/-- The odd-rank FG obstruction has no external orderability premise. -/
theorem oddRank_noFGPositiveCone_unconditional (n : ℕ) (hn : 2 ≤ n) (hodd : Odd n) :
    ¬HasFGPositiveCone (FreeGroup (Fin n) × Multiplicative ℤ) := by
  intro hfg
  exact (Nat.not_even_iff_odd.mpr hodd) (even_of_hasFGPositiveCone n hn hfg)

end FnZPositiveCones
