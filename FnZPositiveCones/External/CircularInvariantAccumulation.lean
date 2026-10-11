module

public import FnZPositiveCones.External.CircularInvariantComponents
public import FnZPositiveCones.External.CircularCyclicAccumulation

@[expose] public section

/-! Tightness excludes cyclic-orbit accumulation inside an invariant gap. -/
namespace FnZPositiveCones.CircularRealization
open CircularDynamics
universe u
variable {ι : Type u} {C : CircularGroupOrder (FreeGroup ι)} (R : CircularRealization C)
variable {S : Set StandardCircle}

/-- An actual complement interval with cyclic stabilizer contains no
accumulation point of the full marked real orbit. -/
theorem derived_real_orbit_disjoint_baseComponent_of_cyclic
    (hS : IsClosed S) (hne : S.Nonempty) (h0 : 0 ∉ S)
    (hinv : ∀ g, R.action g '' S = S)
    [IsCyclic (R.invariantComponentStabilizer S)] :
    Disjoint (derivedSet (Set.range (fun g => R.realLift.action g 0)))
      (complementBaseComponent S) := by
  let H := R.invariantComponentStabilizer S
  let ρ : H →* (ℝ ≃o ℝ) := R.realLift.action.comp H.subtype
  let D := Set.range (fun g => R.realLift.action g 0)
  let J := complementBaseComponent S
  have hJopen : IsOpen J := (isOpen_liftedComplement hS).connectedComponentIn
  have hlocal : J ∩ D = Set.range (fun g : H => ρ g 0) := by
    ext y
    constructor
    · rintro ⟨hyJ, g, rfl⟩
      exact ⟨⟨g, (R.mem_invariantComponentStabilizer_iff h0 hinv g).mpr hyJ⟩, rfl⟩
    · rintro ⟨g, rfl⟩
      exact ⟨(R.mem_invariantComponentStabilizer_iff h0 hinv g.val).mp g.property,
        g.val, rfl⟩
  apply Set.disjoint_left.mpr
  intro p hp hpJ
  have hpH : p ∈ derivedSet (Set.range (fun g : H => ρ g 0)) := by
    rw [← hlocal]
    exact hp.nhds_inter (hJopen.mem_nhds hpJ)
  have hfix : ∀ g : H, ρ g p = p := OrderedActions.cyclic_real_orbit_derived_fixed ρ 0 hpH
  have hpcl : p ∈ closure D := derivedSet_subset_closure _ hp
  obtain ⟨a, b, ha, hb, hJ⟩ := complementBaseComponent_eq_Ioo hS hne h0
  change J = Set.Ioo a b at hJ
  have hpab : p ∈ Set.Ioo a b := hJ ▸ hpJ
  have horbit_mem (g : FreeGroup ι × Multiplicative ℤ)
      (hg : R.realLift.action g 0 ∈ J) : g ∈ H :=
    (R.mem_invariantComponentStabilizer_iff h0 hinv g).mpr hg
  rcases lt_trichotomy p 0 with hp0 | rfl | hp0
  · obtain ⟨q, haq, hqp⟩ := exists_between hpab.1
    have hqJ : q ∈ J := hJ.symm ▸ ⟨haq, hqp.trans hpab.2⟩
    have hno (y : ℝ) (hy : y ∈ Set.Ioo a p) : y ∉ D := by
      rintro ⟨g, rfl⟩
      have hgJ : R.realLift.action g 0 ∈ J := hJ.symm ▸ ⟨hy.1, hy.2.trans hpab.2⟩
      let k : H := ⟨g, horbit_mem g hgJ⟩
      have ht := (ρ k).strictMono hp0
      rw [hfix k] at ht
      exact (ht.trans hy.2).false
    have hqcl : q ∉ closure D := by
      intro hq
      obtain ⟨y, hy, hyD⟩ := mem_closure_iff.mp hq (Set.Ioo a p) isOpen_Ioo ⟨haq, hqp⟩
      exact hno y hy hyD
    have hqcl' : q ∉ closure (Set.range (fun g => R.realLift.action g R.realLift.base)) := by
      simpa only [R.base_zero] using hqcl
    obtain ⟨g, k, hgq, hqk, hgap⟩ := R.realLift.orbit_gap q hqcl'
    simp only [R.base_zero] at hgq hqk hgap
    have hkp : R.realLift.action k 0 ≤ p := by
      by_contra h
      exact Set.disjoint_left.mp hgap ⟨hgq.trans hqp, lt_of_not_ge h⟩ hpcl
    have hkJ : R.realLift.action k 0 ∈ J :=
      hJ.symm ▸ ⟨haq.trans hqk, hkp.trans_lt hpab.2⟩
    let k' : H := ⟨k, horbit_mem k hkJ⟩
    have ht := (ρ k').strictMono hp0
    rw [hfix k'] at ht
    exact (not_lt_of_ge hkp) ht
  · have hr : Set.range (fun g : H => ρ g 0) = {0} := by
      ext y
      constructor
      · rintro ⟨g, rfl⟩
        exact hfix g
      · rintro rfl
        exact ⟨1, by simp⟩
    exact Set.Infinite.of_accPt hpH (hr ▸ Set.finite_singleton 0)
  · obtain ⟨q, hpq, hqb⟩ := exists_between hpab.2
    have hqJ : q ∈ J := hJ.symm ▸ ⟨hpab.1.trans hpq, hqb⟩
    have hno (y : ℝ) (hy : y ∈ Set.Ioo p b) : y ∉ D := by
      rintro ⟨g, rfl⟩
      have hgJ : R.realLift.action g 0 ∈ J := hJ.symm ▸ ⟨hpab.1.trans hy.1, hy.2⟩
      let k : H := ⟨g, horbit_mem g hgJ⟩
      have ht := (ρ k).strictMono hp0
      rw [hfix k] at ht
      exact (hy.1.trans ht).false
    have hqcl : q ∉ closure D := by
      intro hq
      obtain ⟨y, hy, hyD⟩ := mem_closure_iff.mp hq (Set.Ioo p b) isOpen_Ioo ⟨hpq, hqb⟩
      exact hno y hy hyD
    have hqcl' : q ∉ closure (Set.range (fun g => R.realLift.action g R.realLift.base)) := by
      simpa only [R.base_zero] using hqcl
    obtain ⟨g, k, hgq, hqk, hgap⟩ := R.realLift.orbit_gap q hqcl'
    simp only [R.base_zero] at hgq hqk hgap
    have hpg : p ≤ R.realLift.action g 0 := by
      by_contra h
      exact Set.disjoint_left.mp hgap ⟨lt_of_not_ge h, hpq.trans hqk⟩ hpcl
    have hgJ : R.realLift.action g 0 ∈ J :=
      hJ.symm ▸ ⟨hpab.1.trans_le hpg, hgq.trans hqb⟩
    let g' : H := ⟨g, horbit_mem g hgJ⟩
    have ht := (ρ g').strictMono hp0
    rw [hfix g'] at ht
    exact (not_lt_of_ge hpg) ht

end FnZPositiveCones.CircularRealization
