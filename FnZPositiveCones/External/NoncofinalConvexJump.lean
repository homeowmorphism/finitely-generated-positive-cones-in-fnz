module

public import FnZPositiveCones.External.NoncofinalCrossings
public import FnZPositiveCones.External.NoncofinalConvex
public import Mathlib.Order.Quotient

@[expose] public section

/-!
# Ordered left cosets of a convex subgroup

This branch uses left cosets `g * C` and left multiplication, as in MMRT
Lemma 4.11. It is independent of the right-coset/right-action convention in
the positive Schreier construction. No normality assumption is used here.
-/

namespace FnZPositiveCones.NoncofinalConvexJump

open NoncofinalCrossings

section CyclicIntervals

variable {X : Type*} [LinearOrder X]

private theorem pow_le_base (f : X ≃o X) {x : X} (hx : f x ≤ x) (n : ℕ) :
    (f ^ n) x ≤ x := by
  induction n with
  | zero => simp
  | succ n ih =>
    simpa only [pow_succ', RelIso.mul_apply] using (f.monotone ih).trans hx

/-- The direction of motion is constant throughout a cyclic-orbit interval. -/
theorem orbitInterval_motion_le (f : X ≃o X) {x y : X} (hx : f x ≤ x)
    (hy : y ∈ orbitInterval f x) : f y ≤ y := by
  by_contra h
  have hfy : y < f y := lt_of_not_ge h
  obtain ⟨m, n, hm, hn⟩ := hy
  rcases lt_trichotomy x y with hxy | rfl | hyx
  · have hi : f⁻¹ y < y := f.strictMono.lt_iff_lt.mp (by simpa using hfy)
    have hneg (k : ℕ) : ((f⁻¹) ^ k) x < y := by
      induction k with
      | zero => simpa using hxy
      | succ k ih =>
        simpa only [pow_succ', RelIso.mul_apply] using ((f⁻¹).strictMono ih).trans hi
    have hb (k : ℤ) : (f ^ k) x < y := by
      cases k with
      | ofNat k => simpa using (pow_le_base f hx k).trans_lt hxy
      | negSucc k => simpa only [zpow_negSucc, inv_pow] using hneg (k + 1)
    exact (hb n).not_ge hn
  · exact hfy.not_ge hx
  · have hi : x ≤ f⁻¹ x := f.le_iff_le.mp (by simpa using hx)
    have hpos (k : ℕ) : y < (f ^ k) x := by
      induction k with
      | zero => simpa using hyx
      | succ k ih =>
        simpa only [pow_succ', RelIso.mul_apply] using hfy.trans (f.strictMono ih)
    have hneg (k : ℕ) : x ≤ ((f⁻¹) ^ k) x := by
      induction k with
      | zero => simp
      | succ k ih =>
        simpa only [pow_succ', RelIso.mul_apply] using hi.trans ((f⁻¹).monotone ih)
    have hb (k : ℤ) : y < (f ^ k) x := by
      cases k with
      | ofNat k => simpa using hpos k
      | negSucc k => simpa only [zpow_negSucc, inv_pow] using hyx.trans_le (hneg (k + 1))
    exact (hb m).not_ge hm

private theorem outside_lt_all {S : Set X} (hS : Set.OrdConnected S)
    {u x : X} (hu : u ∉ S) (hx : x ∈ S) (hux : u < x) : ∀ y ∈ S, u < y := by
  intro y hy
  by_contra h
  exact hu (hS.out hy hx ⟨le_of_not_gt h, hux.le⟩)

private theorem all_lt_outside {S : Set X} (hS : Set.OrdConnected S)
    {u x : X} (hu : u ∉ S) (hx : x ∈ S) (hxu : x < u) : ∀ y ∈ S, y < u := by
  intro y hy
  by_contra h
  exact hu (hS.out hx hy ⟨hxu.le, le_of_not_gt h⟩)

/-- In a crossing-free action, an element sending the basepoint into a nontrivial
cyclic interval preserves that entire interval. This proves the subgroup step
in DNR Theorem 3.2.27 rather than assuming an interval-preservation property. -/
theorem mapsTo_orbitInterval_of_base_mem {H : Type*} [Group H]
    (ρ : H →* (X ≃o X)) (hno : NoCrossings ρ) (f g : H) (x : X)
    (hf : ρ f x ≠ x) (hg : ρ g x ∈ orbitInterval (ρ f) x) :
    Set.MapsTo (ρ g) (orbitInterval (ρ f) x) (orbitInterval (ρ f) x) := by
  intro y hy
  by_contra hgy
  have hconn := orbitInterval_ordConnected (ρ f) x
  have hneq : ρ g y ≠ ρ g x := fun h => hgy (h ▸ hg)
  rcases lt_or_gt_of_ne hneq with hlo | hhi
  · obtain ⟨n, hn⟩ := exists_zpow_lt_of_mem (ρ f) hf hg
    let a := f ^ (-n) * g
    have hax : x < ρ a x := by
      simpa only [a, map_mul, map_zpow, RelIso.mul_apply, zpow_neg, map_inv,
        RelIso.inv_apply_self] using ((ρ f) ^ (-n)).strictMono hn
    have hay : ρ a y < y := by
      have hbelow := outside_lt_all hconn hgy hg hlo
        (((ρ f) ^ n) y) (orbitInterval_zpow_mem (ρ f) hy n)
      simpa only [a, map_mul, map_zpow, RelIso.mul_apply, zpow_neg, map_inv,
        RelIso.inv_apply_self] using ((ρ f) ^ (-n)).strictMono hbelow
    have hay' : ρ a y ∉ orbitInterval (ρ f) x := by
      intro h
      have hm := orbitInterval_zpow_mem (ρ f) h n
      apply hgy
      simpa only [a, map_mul, map_zpow, RelIso.mul_apply, zpow_neg, map_inv,
        RelIso.apply_inv_self] using hm
    have hx' : x ∉ orbitInterval (ρ a) y := by
      intro h
      exact hax.not_ge (orbitInterval_motion_le (ρ a) hay.le h)
    rcases orbitIntervals_laminar ρ hno f a x y with hd | hfa | haf
    · exact Set.disjoint_left.mp hd hy (mem_orbitInterval_self _ _)
    · exact hx' (hfa (mem_orbitInterval_self _ _))
    · exact hay' (haf (by simpa using zpow_mem_orbitInterval (ρ a) y 1))
  · obtain ⟨n, hn⟩ := exists_zpow_gt_of_mem (ρ f) hf hg
    let a := f ^ (-n) * g
    have hax : ρ a x < x := by
      simpa only [a, map_mul, map_zpow, RelIso.mul_apply, zpow_neg, map_inv,
        RelIso.inv_apply_self] using ((ρ f) ^ (-n)).strictMono hn
    have hay : y < ρ a y := by
      have habove := all_lt_outside hconn hgy hg hhi
        (((ρ f) ^ n) y) (orbitInterval_zpow_mem (ρ f) hy n)
      simpa only [a, map_mul, map_zpow, RelIso.mul_apply, zpow_neg, map_inv,
        RelIso.inv_apply_self] using ((ρ f) ^ (-n)).strictMono habove
    have hay' : ρ a y ∉ orbitInterval (ρ f) x := by
      intro h
      have hm := orbitInterval_zpow_mem (ρ f) h n
      apply hgy
      simpa only [a, map_mul, map_zpow, RelIso.mul_apply, zpow_neg, map_inv,
        RelIso.apply_inv_self] using hm
    have hx' : x ∉ orbitInterval (ρ a) y := by
      intro h
      exact hay.not_ge (orbitInterval_motion_le (ρ a) hax.le
        (mem_orbitInterval_symm (ρ a) h))
    rcases orbitIntervals_laminar ρ hno f a x y with hd | hfa | haf
    · exact Set.disjoint_left.mp hd hy (mem_orbitInterval_self _ _)
    · exact hx' (hfa (mem_orbitInterval_self _ _))
    · exact hay' (haf (by simpa using zpow_mem_orbitInterval (ρ a) y 1))

/-- The basepoint condition also gives inverse preservation, so its preimage is
a subgroup rather than just a multiplicatively closed set. -/
theorem mem_preservingSubgroup_iff_base_mem {H : Type*} [Group H]
    (ρ : H →* (X ≃o X)) (hno : NoCrossings ρ) (f g : H) (x : X)
    (hf : ρ f x ≠ x) :
    g ∈ preservingSubgroup ρ (orbitInterval (ρ f) x) ↔
      ρ g x ∈ orbitInterval (ρ f) x := by
  constructor
  · intro hg
    exact hg.1 (mem_orbitInterval_self _ _)
  · intro hg
    refine ⟨mapsTo_orbitInterval_of_base_mem ρ hno f g x hf hg, ?_⟩
    have he := orbitInterval_eq_of_mem (ρ f) hg
    have hfg : ρ f (ρ g x) ≠ ρ g x := by
      intro h
      have hs := orbitInterval_eq_singleton_of_fixed (ρ f) h
      have hx : x ∈ orbitInterval (ρ f) (ρ g x) := mem_orbitInterval_symm (ρ f) hg
      have hfx : ρ f x ∈ orbitInterval (ρ f) (ρ g x) := by
        rw [he]
        simpa using zpow_mem_orbitInterval (ρ f) x 1
      rw [hs] at hx hfx
      exact hf (hfx.trans hx.symm)
    have hx : ρ g⁻¹ (ρ g x) ∈ orbitInterval (ρ f) (ρ g x) := by
      simpa only [map_inv, RelIso.inv_apply_self] using mem_orbitInterval_symm (ρ f) hg
    have hm := mapsTo_orbitInterval_of_base_mem ρ hno f g⁻¹ (ρ g x) hfg hx
    simpa only [he] using hm

end CyclicIntervals

universe u
variable {G : Type u} [Group G]

/-- Every fiber of the left-coset quotient is order convex. -/
theorem cosetFiber_ordConnected (O : LeftGroupOrder G) (C : Subgroup G)
    (hC : letI := O.order; Set.OrdConnected (C : Set G)) (q : G ⧸ C) :
    letI := O.order
    Set.OrdConnected (Quotient.mk (QuotientGroup.leftRel C) ⁻¹' {q}) := by
  let := O.order
  induction q using Quotient.inductionOn with
  | h a =>
    constructor
    intro x hx z hz y hy
    have hxC : a⁻¹ * x ∈ C := QuotientGroup.eq.mp hx.symm
    have hzC : a⁻¹ * z ∈ C := QuotientGroup.eq.mp hz.symm
    have hyC : a⁻¹ * y ∈ C := hC.out hxC hzC
      ⟨O.mul_le_mul_left x y a⁻¹ hy.1, O.mul_le_mul_left y z a⁻¹ hy.2⟩
    exact (QuotientGroup.eq.mpr hyC).symm

/-- Mathlib's condensation order on left cosets of a convex subgroup. -/
@[instance_reducible] noncomputable def cosetLinearOrder (O : LeftGroupOrder G) (C : Subgroup G)
    (hC : letI := O.order; Set.OrdConnected (C : Set G)) : LinearOrder (G ⧸ C) := by
  classical
  let := O.order
  let : ∀ q : G ⧸ C, Set.OrdConnected (Quotient.mk (QuotientGroup.leftRel C) ⁻¹' {q}) :=
    cosetFiber_ordConnected O C hC
  exact Quotient.instLinearOrder

/-- Comparison of concrete representatives, including equality of cosets. -/
theorem coset_mk_le_mk (O : LeftGroupOrder G) (C : Subgroup G)
    (hC : letI := O.order; Set.OrdConnected (C : Set G)) (g h : G) :
    letI := cosetLinearOrder O C hC
    (QuotientGroup.mk g : G ⧸ C) ≤ QuotientGroup.mk h ↔ O.order.le g h ∨ g⁻¹ * h ∈ C := by
  classical
  let := O.order
  let : ∀ q : G ⧸ C, Set.OrdConnected (Quotient.mk (QuotientGroup.leftRel C) ⁻¹' {q}) :=
    cosetFiber_ordConnected O C hC
  simpa only [QuotientGroup.leftRel_apply] using
    (Quotient.mk_le_mk (s := QuotientGroup.leftRel C) (x := g) (y := h))

/-- Left multiplication is well-defined on left cosets without a normality hypothesis. -/
def cosetPerm (C : Subgroup G) (g : G) : Equiv.Perm (G ⧸ C) where
  toFun := Quotient.map (fun h => g * h) (by
    intro a b h
    apply QuotientGroup.leftRel_apply.mpr
    simpa only [mul_inv_rev, mul_assoc, inv_mul_cancel_left] using
      (QuotientGroup.leftRel_apply.mp h))
  invFun := Quotient.map (fun h => g⁻¹ * h) (by
    intro a b h
    apply QuotientGroup.leftRel_apply.mpr
    simpa only [mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left] using
      (QuotientGroup.leftRel_apply.mp h))
  left_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | h a => simp only [Quotient.map_mk, inv_mul_cancel_left]
  right_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | h a => simp only [Quotient.map_mk, mul_inv_cancel_left]

@[simp] theorem cosetPerm_mk (C : Subgroup G) (g h : G) :
    cosetPerm C g (QuotientGroup.mk h) = QuotientGroup.mk (g * h) := rfl

/-- The genuine action by order automorphisms of the ordered left-coset space. -/
noncomputable def cosetAction (O : LeftGroupOrder G) (C : Subgroup G)
    (hC : letI := O.order; Set.OrdConnected (C : Set G)) :
    letI := cosetLinearOrder O C hC
    G →* ((G ⧸ C) ≃o (G ⧸ C)) := by
  let := O.order
  let := cosetLinearOrder O C hC
  exact {
    toFun := fun g => {
      toEquiv := cosetPerm C g
      map_rel_iff' := by
        intro q r
        induction q using Quotient.inductionOn with
        | h a =>
          induction r using Quotient.inductionOn with
          | h b =>
            rw [cosetPerm_mk, cosetPerm_mk, coset_mk_le_mk, coset_mk_le_mk]
            have hle : g * a ≤ g * b ↔ a ≤ b := by
              constructor
              · intro h
                simpa only [inv_mul_cancel_left] using O.mul_le_mul_left _ _ g⁻¹ h
              · exact O.mul_le_mul_left a b g
            simp only [hle, mul_inv_rev, mul_assoc, inv_mul_cancel_left] }
    map_one' := by
      ext q
      induction q using Quotient.inductionOn with
      | h a =>
        change QuotientGroup.mk (1 * a) = QuotientGroup.mk a
        rw [one_mul]
    map_mul' := by
      intro g h
      ext q
      induction q using Quotient.inductionOn with
      | h a =>
        change QuotientGroup.mk ((g * h) * a) = QuotientGroup.mk (g * (h * a))
        rw [mul_assoc] }

@[simp] theorem cosetAction_mk (O : LeftGroupOrder G) (C : Subgroup G)
    (hC : letI := O.order; Set.OrdConnected (C : Set G)) (g h : G) :
    cosetAction O C hC g (QuotientGroup.mk h) = QuotientGroup.mk (g * h) := rfl

@[simp] theorem cosetAction_base (O : LeftGroupOrder G) (C : Subgroup G)
    (hC : letI := O.order; Set.OrdConnected (C : Set G)) (g : G) :
    cosetAction O C hC g (QuotientGroup.mk 1) = QuotientGroup.mk g := by
  rw [cosetAction_mk, mul_one]

theorem coset_base_fixed_iff (O : LeftGroupOrder G) (C : Subgroup G)
    (hC : letI := O.order; Set.OrdConnected (C : Set G)) (g : G) :
    cosetAction O C hC g (QuotientGroup.mk 1) = QuotientGroup.mk 1 ↔ g ∈ C := by
  rw [cosetAction_base, QuotientGroup.eq]
  simp only [mul_one, inv_mem_iff]

/-- The cyclic interval preimage is convex in the original left order. -/
theorem cyclicPreservingSubgroup_convex (O : LeftGroupOrder G) (C : Subgroup G)
    (hC : letI := O.order; Set.OrdConnected (C : Set G))
    (hno : letI := cosetLinearOrder O C hC; NoCrossings (cosetAction O C hC))
    {f : G} (hf : f ∉ C) :
    letI := O.order
    letI := cosetLinearOrder O C hC
    Set.OrdConnected (preservingSubgroup (cosetAction O C hC)
      (orbitInterval (cosetAction O C hC f) (QuotientGroup.mk 1)) : Set G) := by
  let := O.order
  let := cosetLinearOrder O C hC
  have hfix : cosetAction O C hC f (QuotientGroup.mk 1) ≠ QuotientGroup.mk 1 :=
    fun h => hf ((coset_base_fixed_iff O C hC f).mp h)
  constructor
  intro a ha b hb z hz
  simp only [SetLike.mem_coe] at ha hb ⊢
  rw [mem_preservingSubgroup_iff_base_mem _ hno f _ _ hfix, cosetAction_base] at ha hb ⊢
  apply (orbitInterval_ordConnected _ _).out ha hb
  exact ⟨(coset_mk_le_mk O C hC a z).mpr (Or.inl hz.1),
    (coset_mk_le_mk O C hC z b).mpr (Or.inl hz.2)⟩

/-- For a maximal proper convex subgroup, every element outside it has a cyclic
orbit spanning the entire ordered coset space when crossings are absent. -/
theorem orbitInterval_coset_eq_univ (O : LeftGroupOrder G) (C : Subgroup G)
    (hC : letI := O.order; Set.OrdConnected (C : Set G))
    (hmax : ∀ S : Subgroup G, (letI := O.order; Set.OrdConnected (S : Set G)) →
      C < S → S = ⊤)
    (hno : letI := cosetLinearOrder O C hC; NoCrossings (cosetAction O C hC))
    {f : G} (hf : f ∉ C) :
    letI := cosetLinearOrder O C hC
    orbitInterval (cosetAction O C hC f) (QuotientGroup.mk 1) = Set.univ := by
  let := O.order
  let := cosetLinearOrder O C hC
  let ρ := cosetAction O C hC
  let x : G ⧸ C := QuotientGroup.mk 1
  let S := preservingSubgroup ρ (orbitInterval (ρ f) x)
  have hfix : ρ f x ≠ x := fun h => hf ((coset_base_fixed_iff O C hC f).mp h)
  have hCS : C ≤ S := by
    intro g hg
    rw [mem_preservingSubgroup_iff_base_mem ρ hno f g x hfix]
    have he : ρ g x = x := (coset_base_fixed_iff O C hC g).mpr hg
    rw [he]
    exact mem_orbitInterval_self _ _
  have hfS : f ∈ S := by
    rw [mem_preservingSubgroup_iff_base_mem ρ hno f f x hfix]
    simpa using zpow_mem_orbitInterval (ρ f) x 1
  have hStop : S = ⊤ := hmax S (cyclicPreservingSubgroup_convex O C hC hno hf)
    (lt_of_le_of_ne hCS (fun he => hf (he ▸ hfS)))
  apply Set.eq_univ_of_forall
  intro q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  have hg : g ∈ S := hStop ▸ Subgroup.mem_top g
  have hm := (mem_preservingSubgroup_iff_base_mem ρ hno f g x hfix).mp hg
  simpa only [ρ, x, cosetAction_base] using hm

/-- There is a coset strictly above the identity coset for every proper convex subgroup. -/
theorem exists_coset_gt_base (O : LeftGroupOrder G) (C : Subgroup G)
    (hC : letI := O.order; Set.OrdConnected (C : Set G)) (hne : C ≠ ⊤) :
    letI := cosetLinearOrder O C hC
    ∃ y : G ⧸ C, QuotientGroup.mk 1 < y := by
  let := cosetLinearOrder O C hC
  obtain ⟨g, hg⟩ := IsConcreteLE.exists_of_lt (lt_top_iff_ne_top.mpr hne)
  have hneq : (QuotientGroup.mk g : G ⧸ C) ≠ QuotientGroup.mk 1 := by
    intro h
    exact hg.2 ((coset_base_fixed_iff O C hC g).mp (by simpa using h))
  rcases lt_or_gt_of_ne hneq with hlo | hhi
  · refine ⟨QuotientGroup.mk g⁻¹, ?_⟩
    simpa only [cosetAction_mk, inv_mul_cancel, mul_one] using
      (cosetAction O C hC g⁻¹).strictMono hlo
  · exact ⟨QuotientGroup.mk g, hhi⟩

/-- DNR Theorem 3.2.27, the normality conclusion used in MMRT Lemma 4.11.
The quotient order and action are constructed without assuming normality. -/
theorem normal_of_maximal_convex_noCrossings (O : LeftGroupOrder G) (C : Subgroup G)
    (hC : letI := O.order; Set.OrdConnected (C : Set G)) (hne : C ≠ ⊤)
    (hmax : ∀ S : Subgroup G, (letI := O.order; Set.OrdConnected (S : Set G)) →
      C < S → S = ⊤)
    (hno : letI := cosetLinearOrder O C hC; NoCrossings (cosetAction O C hC)) :
    C.Normal := by
  let := cosetLinearOrder O C hC
  let : Nontrivial (G ⧸ C) := QuotientGroup.nontrivial_iff.mpr hne
  let ρ := cosetAction O C hC
  have he : C = noncofinalSubgroup ρ hno := by
    ext f
    constructor
    · intro hf
      obtain ⟨y, hy⟩ := exists_coset_gt_base O C hC hne
      have hfix : ρ f (QuotientGroup.mk 1) = QuotientGroup.mk 1 :=
        (coset_base_fixed_iff O C hC f).mpr hf
      exact ⟨QuotientGroup.mk 1, y, hy, by intro n; simpa only [fixed_zpow _ hfix] using hy⟩
    · intro hf
      by_contra hf'
      obtain ⟨x, y, hxy, hb⟩ := hf
      have hu := orbitInterval_coset_eq_univ O C hC hmax hno hf'
      have hx : x ∈ orbitInterval (ρ f) (QuotientGroup.mk 1) := by rw [hu]; trivial
      have heq := orbitInterval_eq_of_mem (ρ f) hx
      have hy : y ∈ orbitInterval (ρ f) x := by rw [heq, hu]; trivial
      obtain ⟨m, n, hm, hn⟩ := hy
      exact (hb n).not_ge hn
  rw [he]
  infer_instance

/-- A nonnormal maximal convex subgroup forces an actual crossing in its ordered
left-coset action. This is the contrapositive needed for the noncofinal branch. -/
theorem exists_crossing_of_maximal_convex_not_normal (O : LeftGroupOrder G) (C : Subgroup G)
    (hC : letI := O.order; Set.OrdConnected (C : Set G)) (hne : C ≠ ⊤)
    (hmax : ∀ S : Subgroup G, (letI := O.order; Set.OrdConnected (S : Set G)) →
      C < S → S = ⊤) (hnormal : ¬ C.Normal) :
    letI := cosetLinearOrder O C hC
    ∃ f g : G, ∃ u v w : G ⧸ C,
      Crossing (cosetAction O C hC f) (cosetAction O C hC g) u v w := by
  let := cosetLinearOrder O C hC
  by_contra h
  apply hnormal
  apply normal_of_maximal_convex_noCrossings O C hC hne hmax
  intro f g u v w hc
  exact h ⟨f, g, u, v, w, hc⟩

end FnZPositiveCones.NoncofinalConvexJump
