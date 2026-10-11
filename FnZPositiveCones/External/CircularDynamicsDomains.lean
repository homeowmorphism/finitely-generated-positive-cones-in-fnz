module

public import FnZPositiveCones.External.CircularDynamicsSeparation
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
public import Mathlib.Topology.Instances.Real.Lemmas

@[expose] public section

/-! Compactness and actual complementary intervals for separated orbit colors. -/
namespace FnZPositiveCones
namespace CircularDynamics

/-- Local constancy on a compact set supplies one radius valid at every point.
No finiteness assumption on the color type is needed. -/
theorem compact_local_color_uniform {X C : Type*} [PseudoMetricSpace X]
    (K : Set X) (hK : IsCompact K) (color : X → C)
    (hlocal : ∀ x ∈ K, ∃ ε > 0, ∀ y ∈ K, dist x y < ε → color x = color y) :
    ∃ δ > 0, ∀ x ∈ K, ∀ y ∈ K, dist x y < δ → color x = color y := by
  classical
  choose ε hε hm using fun x : K => hlocal x x.property
  obtain ⟨δ, hδ, hcover⟩ := lebesgue_number_lemma_of_metric (c := fun x : K => Metric.ball (x : X) (ε x)) hK
    (fun _ => Metric.isOpen_ball) (by
      intro x hx
      exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, Metric.mem_ball_self (hε ⟨x, hx⟩)⟩)
  refine ⟨δ, hδ, ?_⟩
  intro x hx y hy hxy
  obtain ⟨z, hz⟩ := hcover x hx
  have hzx := hm z x hx (by simpa [Metric.mem_ball, dist_comm] using hz (Metric.mem_ball_self hδ))
  have hzy := hm z y hy (by simpa [Metric.mem_ball, dist_comm] using hz (by simpa [dist_comm] using hxy))
  exact hzx.symm.trans hzy

/-- An actual complementary interval with both endpoints in the closed set.
The definition itself does not assert that the set is closed. -/
def IsRealGap (K : Set ℝ) (a b : ℝ) : Prop :=
  a ∈ K ∧ b ∈ K ∧ a < b ∧ ∀ x ∈ K, x ∉ Set.Ioo a b

/-- Different complementary intervals are ordered by their left endpoints. -/
theorem realGap_right_le_of_left_lt {K : Set ℝ} {a b c d : ℝ}
    (hab : IsRealGap K a b) (hcd : IsRealGap K c d) (hac : a < c) : b ≤ c := by
  by_contra h
  exact hab.2.2.2 c hcd.1 ⟨hac, lt_of_not_ge h⟩

/-- A left endpoint determines its actual complementary interval. -/
theorem realGap_right_unique {K : Set ℝ} {a b c : ℝ}
    (hab : IsRealGap K a b) (hac : IsRealGap K a c) : b = c := by
  apply le_antisymm
  · by_contra h
    exact hab.2.2.2 c hac.2.1 ⟨hac.2.2.1, lt_of_not_ge h⟩
  · by_contra h
    exact hac.2.2.2 b hab.2.1 ⟨hab.2.2.1, lt_of_not_ge h⟩

/-- A bounded set has only finitely many complementary intervals longer than a
fixed positive length. This is an interval statement, not an assumed bound on
components or endpoints. -/
theorem finite_long_realGaps (K : Set ℝ) (hbelow : BddBelow K) (habove : BddAbove K)
    {δ : ℝ} (hδ : 0 < δ) :
    Set.Finite {p : ℝ × ℝ | IsRealGap K p.1 p.2 ∧ δ ≤ p.2 - p.1} := by
  let S : Set (ℝ × ℝ) := {p | IsRealGap K p.1 p.2 ∧ δ ≤ p.2 - p.1}
  let f : ℝ × ℝ → ℤ := fun p => ⌊p.1 / δ⌋
  have hinj : Set.InjOn f S := by
    intro p hp q hq heq
    have hbound : ∀ p q : ℝ × ℝ, p ∈ S → q ∈ S → f p = f q → ¬p.1 < q.1 := by
      intro p q hp hq heq hpq
      have hb := realGap_right_le_of_left_lt hp.1 hq.1 hpq
      have hfloor := Int.floor_le (p.1 / δ)
      have hlt := Int.lt_floor_add_one (q.1 / δ)
      change ⌊p.1 / δ⌋ = ⌊q.1 / δ⌋ at heq
      rw [← heq] at hlt
      have hdiv : q.1 / δ < p.1 / δ + 1 := by linarith
      have hdiff : q.1 < p.1 + δ := by
        have := (div_lt_iff₀ hδ).mp hdiv
        field_simp at this
        nlinarith
      have hlength := hp.2
      linarith
    have hleft : p.1 = q.1 := le_antisymm
      (le_of_not_gt (hbound q p hq hp heq.symm))
      (le_of_not_gt (hbound p q hp hq heq))
    apply Prod.ext hleft
    exact realGap_right_unique hp.1 (hleft ▸ hq.1)
  obtain ⟨l, hl⟩ := hbelow
  obtain ⟨r, hr⟩ := habove
  have hfin : (f '' S).Finite := by
    apply (Set.finite_Icc (⌊l / δ⌋ : ℤ) ⌊r / δ⌋).subset
    rintro z ⟨p, hp, rfl⟩
    exact ⟨Int.floor_mono (div_le_div_of_nonneg_right (hl hp.1.1) hδ.le),
      Int.floor_mono (div_le_div_of_nonneg_right (hr hp.1.1) hδ.le)⟩
  exact (Set.finite_image_iff hinj).mp hfin

/-- Actual transition gaps of a locally monochrome compact subset of a line are
finite. This supplies the compactness step in constructing finite color domains. -/
theorem finite_real_color_transition_gaps {C : Type*} (K : Set ℝ) (hK : IsCompact K)
    (color : ℝ → C)
    (hlocal : ∀ x ∈ K, ∃ ε > 0, ∀ y ∈ K, dist x y < ε → color x = color y) :
    Set.Finite {p : ℝ × ℝ | IsRealGap K p.1 p.2 ∧ color p.1 ≠ color p.2} := by
  obtain ⟨δ, hδ, hm⟩ := compact_local_color_uniform K hK color hlocal
  apply (finite_long_realGaps K hK.bddBelow hK.bddAbove hδ).subset
  intro p hp
  refine ⟨hp.1, le_of_not_gt ?_⟩
  intro hsmall
  apply hp.2
  apply hm p.1 hp.1.1 p.2 hp.1.2.1
  simpa [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hp.1.2.2.1.le), neg_sub] using hsmall


/-- Every union of color classes is closed inside the compact set: local
constancy, rather than a preassigned finite palette, is the essential input. -/
theorem compact_local_color_predicate {X C : Type*} [MetricSpace X]
    (K : Set X) (hK : IsCompact K) (color : X → C)
    (hlocal : ∀ x ∈ K, ∃ ε > 0, ∀ y ∈ K, dist x y < ε → color x = color y)
    (P : C → Prop) : IsCompact {x | x ∈ K ∧ P (color x)} := by
  obtain ⟨δ, hδ, hm⟩ := compact_local_color_uniform K hK color hlocal
  apply hK.of_isClosed_subset _ (fun _ h => h.1)
  apply isClosed_of_closure_subset
  intro x hx
  have hxK : x ∈ K := hK.isClosed.closure_subset
    (closure_mono (show {x | x ∈ K ∧ P (color x)} ⊆ K from fun _ h => h.1) hx)
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.mp hx δ hδ
  exact ⟨hxK, (hm x hxK y hy.1 hxy).symm ▸ hy.2⟩

/-- Differently colored points of the compact set are separated by an actual
complementary interval whose endpoint colors differ. -/
theorem real_color_transition_gap_between {C : Type*} (K : Set ℝ) (hK : IsCompact K)
    (color : ℝ → C)
    (hlocal : ∀ x ∈ K, ∃ ε > 0, ∀ y ∈ K, dist x y < ε → color x = color y)
    {x y : ℝ} (hx : x ∈ K) (hy : y ∈ K) (hxy : x < y)
    (hcolor : color x ≠ color y) :
    ∃ a b, x ≤ a ∧ b ≤ y ∧ IsRealGap K a b ∧ color a ≠ color b := by
  let A : Set ℝ := {z | z ∈ K ∧ color z = color x} ∩ Set.Icc x y
  have hA : IsCompact A := (compact_local_color_predicate K hK color hlocal
    (fun c => c = color x)).inter_right isClosed_Icc
  obtain ⟨a, ha⟩ := hA.exists_isGreatest ⟨x, ⟨⟨hx, rfl⟩, le_rfl, hxy.le⟩⟩
  let B : Set ℝ := {z | z ∈ K ∧ color z ≠ color x} ∩ Set.Icc a y
  have hB : IsCompact B := (compact_local_color_predicate K hK color hlocal
    (fun c => c ≠ color x)).inter_right isClosed_Icc
  obtain ⟨b, hb⟩ := hB.exists_isLeast ⟨y, ⟨⟨hy, hcolor.symm⟩, ha.1.2.2, le_rfl⟩⟩
  have hab : a < b := lt_of_le_of_ne hb.1.2.1 (by
    intro heq
    apply hb.1.1.2
    simpa [← heq] using ha.1.1.2)
  refine ⟨a, b, ha.1.2.1, hb.1.2.2,
    ⟨ha.1.1.1, hb.1.1.1, hab, ?_⟩, ?_⟩
  · intro z hz hzab
    by_cases hc : color z = color x
    · have hza := ha.2 (show z ∈ A from
        ⟨⟨hz, hc⟩, ha.1.2.1.trans hzab.1.le, hzab.2.le.trans hb.1.2.2⟩)
      exact (not_le_of_gt hzab.1) hza
    · have hbz := hb.2 (show z ∈ B from
        ⟨⟨hz, hc⟩, hzab.1.le, hzab.2.le.trans hb.1.2.2⟩)
      exact (not_le_of_gt hzab.2) hbz
  · intro hc
    exact hb.1.1.2 (hc.symm.trans ha.1.1.2)

/-- A finite set of cuts outside the compact set separates all its distinct
colors. The cuts are midpoints of genuine transition gaps. -/
theorem exists_finite_color_cuts {C : Type*} (K : Set ℝ) (hK : IsCompact K)
    (color : ℝ → C)
    (hlocal : ∀ x ∈ K, ∃ ε > 0, ∀ y ∈ K, dist x y < ε → color x = color y) :
    ∃ T : Finset ℝ, (∀ t ∈ T, t ∉ K) ∧
      ∀ x ∈ K, ∀ y ∈ K, x < y → color x ≠ color y → ∃ t ∈ T, x < t ∧ t < y := by
  classical
  let S := (finite_real_color_transition_gaps K hK color hlocal).toFinset
  let T := S.image (fun p => (p.1 + p.2) / 2)
  refine ⟨T, ?_, ?_⟩
  · intro t ht htK
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ht
    have hp' : IsRealGap K p.1 p.2 ∧ color p.1 ≠ color p.2 := by simpa [S] using hp
    apply hp'.1.2.2.2 ((p.1 + p.2) / 2) htK
    constructor <;> linarith [hp'.1.2.2.1]
  · intro x hx y hy hxy hc
    obtain ⟨a, b, hxa, hby, hab, hcab⟩ :=
      real_color_transition_gap_between K hK color hlocal hx hy hxy hc
    refine ⟨(a + b) / 2, ?_, ?_, ?_⟩
    · apply Finset.mem_image.mpr
      refine ⟨(a, b), ?_, rfl⟩
      simpa [S] using (show IsRealGap K a b ∧ color a ≠ color b from ⟨hab, hcab⟩)
    · linarith [hab.2.2.1]
    · linarith [hab.2.2.1]


/-- The closed region determined by a finite set of cuts and the cuts lying to
its right. Intersecting with the compact set gives an actual compact cell. -/
def cutRegion (T S : Finset ℝ) : Set ℝ :=
  (⋂ t ∈ S, Set.Iic t) ∩ ⋂ t ∈ T \ S, Set.Ici t

theorem mem_cutRegion_iff (T S : Finset ℝ) (x : ℝ) :
    x ∈ cutRegion T S ↔ (∀ t ∈ S, x ≤ t) ∧ ∀ t ∈ T \ S, t ≤ x := by
  simp [cutRegion]

theorem isClosed_cutRegion (T S : Finset ℝ) : IsClosed (cutRegion T S) := by
  exact (isClosed_iInter (fun _ => isClosed_iInter (fun _ => isClosed_Iic))).inter
    (isClosed_iInter (fun _ => isClosed_iInter (fun _ => isClosed_Ici)))

/-- A finite disjoint interval cover obtained from actual transition gaps.
Each interval has endpoints in the compact set and contains just one color of
that set. Degenerate intervals are permitted for isolated points. -/
theorem exists_finite_monochrome_intervals {C : Type*} (K : Set ℝ) (hK : IsCompact K)
    (color : ℝ → C)
    (hlocal : ∀ x ∈ K, ∃ ε > 0, ∀ y ∈ K, dist x y < ε → color x = color y) :
    ∃ (I : Type) (_ : Fintype I) (a b : I → ℝ),
      (∀ i, a i ∈ K ∧ b i ∈ K ∧ a i ≤ b i) ∧
      (∀ x ∈ K, ∃ i, x ∈ Set.Icc (a i) (b i)) ∧
      (∀ i, ∀ x ∈ K, x ∈ Set.Icc (a i) (b i) → color x = color (a i)) ∧
      (∀ i j, i ≠ j → Disjoint (Set.Icc (a i) (b i)) (Set.Icc (a j) (b j))) := by
  classical
  obtain ⟨T, hTK, hsep⟩ := exists_finite_color_cuts K hK color hlocal
  let I := {S : Finset ℝ // S ∈ T.powerset ∧ (K ∩ cutRegion T S).Nonempty}
  have : Finite I := Finite.of_injective
    (fun i : I => (⟨i.val, i.property.1⟩ : {S // S ∈ T.powerset}))
    (by intro i j h; apply Subtype.ext; exact congrArg (fun x : {S : Finset ℝ // S ∈ T.powerset} => x.val) h)
  let : Fintype I := Fintype.ofFinite I
  have hc : ∀ i : I, IsCompact (K ∩ cutRegion T i.val) :=
    fun i => hK.inter_right (isClosed_cutRegion T i.val)
  choose a ha using fun i : I => (hc i).exists_isLeast i.property.2
  choose b hb using fun i : I => (hc i).exists_isGreatest i.property.2
  have hab : ∀ i, a i ≤ b i := fun i => (ha i).2 (hb i).1
  have haK : ∀ i, a i ∈ K := fun i => (ha i).1.1
  have hbK : ∀ i, b i ∈ K := fun i => (hb i).1.1
  have hleft : ∀ i, ∀ t ∈ i.val, b i < t := by
    intro i t ht
    have hle := ((mem_cutRegion_iff T i.val (b i)).mp (hb i).1.2).1 t ht
    apply lt_of_le_of_ne hle
    intro heq
    exact hTK t ((Finset.mem_powerset.mp i.property.1) ht) (heq ▸ hbK i)
  have hright : ∀ i, ∀ t ∈ T \ i.val, t < a i := by
    intro i t ht
    have hle := ((mem_cutRegion_iff T i.val (a i)).mp (ha i).1.2).2 t ht
    apply lt_of_le_of_ne hle
    intro heq
    exact hTK t (Finset.mem_sdiff.mp ht).1 (heq.symm ▸ haK i)
  refine ⟨I, inferInstance, a, b, (fun i => ⟨haK i, hbK i, hab i⟩), ?_, ?_, ?_⟩
  · intro x hx
    let S := T.filter (fun t => x < t)
    have hxreg : x ∈ cutRegion T S := by
      apply (mem_cutRegion_iff T S x).mpr
      constructor
      · intro t ht
        exact (Finset.mem_filter.mp ht).2.le
      · intro t ht
        have hn := (Finset.mem_sdiff.mp ht).2
        have htT := (Finset.mem_sdiff.mp ht).1
        by_contra h
        exact hn (Finset.mem_filter.mpr ⟨htT, lt_of_not_ge h⟩)
    let i : I := ⟨S, Finset.mem_powerset.mpr (Finset.filter_subset _ _), ⟨x, hx, hxreg⟩⟩
    exact ⟨i, (ha i).2 ⟨hx, hxreg⟩, (hb i).2 ⟨hx, hxreg⟩⟩
  · intro i x hx hxi
    by_contra hcol
    have hax : a i < x := lt_of_le_of_ne hxi.1 (by
      intro heq; exact hcol (congrArg color heq.symm))
    obtain ⟨t, htT, hat, htx⟩ := hsep (a i) (haK i) x hx hax (fun h => hcol h.symm)
    by_cases ht : t ∈ i.val
    · have hbt := hleft i t ht
      linarith [hxi.2]
    · have hta := hright i t (Finset.mem_sdiff.mpr ⟨htT, ht⟩)
      linarith
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    apply hij
    apply Subtype.ext
    apply Finset.ext
    intro t
    constructor
    · intro hti
      by_contra htj
      have htT := (Finset.mem_powerset.mp i.property.1) hti
      have hti' := hleft i t hti
      have htj' := hright j t (Finset.mem_sdiff.mpr ⟨htT, htj⟩)
      linarith [hxi.2, hxj.1]
    · intro htj
      by_contra hti
      have htT := (Finset.mem_powerset.mp j.property.1) htj
      have htj' := hleft j t htj
      have hti' := hright i t (Finset.mem_sdiff.mpr ⟨htT, hti⟩)
      linarith [hxj.2, hxi.1]

end CircularDynamics
end FnZPositiveCones
