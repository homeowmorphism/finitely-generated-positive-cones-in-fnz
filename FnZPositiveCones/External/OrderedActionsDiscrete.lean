module

public import FnZPositiveCones.Cone.Discrete
public import FnZPositiveCones.External.OrderedActionsCircleRealization

@[expose] public section

namespace FnZPositiveCones
universe u
variable {G : Type u} [Group G] {O : LeftGroupOrder G}

namespace TightRealization

theorem orbit_gap_covBy (R : TightRealization O) {g h : G}
    (hgh : R.action g R.base < R.action h R.base)
    (hgap : Disjoint (Set.Ioo (R.action g R.base) (R.action h R.base))
      (closure (Set.range (fun k => R.action k R.base)))) :
    letI := O.order; g ⋖ h := by
  let := O.order
  have hlt (a b : G) : a < b ↔ R.action a R.base < R.action b R.base := by
    rw [lt_iff_not_ge, R.order_iff, not_le]
  refine ⟨(hlt g h).mpr hgh, ?_⟩
  intro k hgk hkh
  exact Set.disjoint_left.mp hgap ⟨(hlt g k).mp hgk, (hlt k h).mp hkh⟩
    (subset_closure ⟨k, rfl⟩)

/-- All gaps in a tight realization of a discrete group order are translates of one gap. -/
theorem gap_is_translate (R : TightRealization O) {a : G} (ha : O.IsLeastPositive a)
    {x : ℝ} (hx : x ∉ closure (Set.range (fun g => R.action g R.base))) :
    ∃ g : G, R.action g R.base < x ∧ x < R.action g (R.action a R.base) ∧
      Disjoint (Set.Ioo (R.action g R.base) (R.action g (R.action a R.base)))
        (closure (Set.range (fun k => R.action k R.base))) := by
  obtain ⟨g, h, hg, hh, hd⟩ := R.orbit_gap x hx
  have hcov := R.orbit_gap_covBy (hg.trans hh) hd
  have he := (O.covBy_iff_of_isLeastPositive ha g h).mp hcov
  subst h
  simp only [map_mul, OrderedActions.realAut_mul_apply] at hh hd
  exact ⟨g, hg, hh, hd⟩

end TightRealization

/-- The least positive element in a nontrivial cofinal product has nontrivial projection. -/
theorem least_positive_projection_ne_one [Nontrivial G]
    (O : LeftGroupOrder (G × Multiplicative ℤ))
    (hz : O.order.lt 1 (cofinalProductZ G)) (hc : O.IsCofinal (cofinalProductZ G))
    {a : G × Multiplicative ℤ} (ha : O.IsLeastPositive a) : a.1 ≠ 1 := by
  let := O.order
  intro hfst
  let k : ℤ := a.2.toAdd
  have he : a = cofinalProductZ G ^ k := by
    apply Prod.ext
    · simpa [cofinalProductZ] using hfst
    · apply Multiplicative.toAdd.injective
      simp [cofinalProductZ, k]
  have hmono := O.zpow_strictMono hz
  have hkpos : (0 : ℤ) < k := hmono.lt_iff_lt.mp (by simpa only [zpow_zero, ← he] using ha.1)
  have hkle : k ≤ 1 := hmono.le_iff_le.mp (by simpa only [zpow_one, ← he] using ha.2 _ hz)
  have hk : k = 1 := by omega
  have haeq : a = cofinalProductZ G := by simpa only [hk, zpow_one] using he
  obtain ⟨g, hg⟩ := exists_ne (1 : G)
  let r := cofinalProductRepresentative O hz hc g
  have hr := O.fundamentalRepresentative_mem hz hc (g, 1)
  have hrne : r ≠ 1 := by
    intro heq
    have hh := congrArg Prod.fst heq
    exact hg (by simpa [r] using hh)
  have hrpos : (1 : G × Multiplicative ℤ) < r := lt_of_le_of_ne hr.1 hrne.symm
  have hh := ha.2 r hrpos
  rw [haeq] at hh
  exact not_lt_of_ge hh hr.2

/-- A specified immediate successor in a circular group order. -/
def CircularGroupOrder.IsSuccessor (C : CircularGroupOrder G) (a : G) : Prop :=
  a ≠ 1 ∧ ∀ g : G, ¬ C.order.sbtw 1 g a

/-- Least positivity in the cofinal product gives an actual circular successor. -/
theorem least_positive_gives_circular_successor [Nontrivial G]
    (O : LeftGroupOrder (G × Multiplicative ℤ))
    (hz : O.order.lt 1 (cofinalProductZ G)) (hc : O.IsCofinal (cofinalProductZ G))
    {a : G × Multiplicative ℤ} (ha : O.IsLeastPositive a) :
    (cofinalProductCircularGroupOrder O hz hc).IsSuccessor a.1 := by
  let := O.order
  have hne := least_positive_projection_ne_one O hz hc ha
  have haz : a < cofinalProductZ G := lt_of_le_of_ne (ha.2 _ hz) (by
    intro he
    apply hne
    simpa [cofinalProductZ] using congrArg Prod.fst he)
  have haf := O.fundamentalRepresentative_eq_self hz hc ⟨ha.1.le, haz⟩
  have he : a = cofinalProductZ G ^ a.2.toAdd * (a.1, 1) := by
    apply Prod.ext
    · simp [cofinalProductZ]
    · apply Multiplicative.toAdd.injective
      simp [cofinalProductZ]
  have hrep : cofinalProductRepresentative O hz hc a.1 = a := by
    conv_lhs => change O.fundamentalRepresentative hz hc (a.1, 1)
    rw [he, O.fundamentalRepresentative_zpow_mul] at haf
    exact haf.trans he.symm
  refine ⟨hne, ?_⟩
  intro g h
  rw [cofinalProductCircularGroupOrder_sbtw_one, hrep] at h
  exact not_lt_of_ge (ha.2 _ h.1) h.2

/-- Finite strict generation supplies this successor without a dynamical external theorem. -/
theorem semigroupFG_circular_successor [Nontrivial G] (P : PositiveCone (G × Multiplicative ℤ))
    (hfg : SemigroupFG P.1) (hz : (coneLeftOrder P).order.lt 1 (cofinalProductZ G))
    (hc : (coneLeftOrder P).IsCofinal (cofinalProductZ G)) :
    ∃ a : G, (cofinalProductCircularGroupOrder (coneLeftOrder P) hz hc).IsSuccessor a := by
  obtain ⟨a, ha⟩ := semigroupFG_isLeastPositive P hfg
  exact ⟨a.1, least_positive_gives_circular_successor _ hz hc ha⟩

end FnZPositiveCones
