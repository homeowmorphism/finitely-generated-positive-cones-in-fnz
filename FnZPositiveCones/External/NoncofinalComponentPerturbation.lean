module

public import FnZPositiveCones.External.NoncofinalFixedCrossing
public import Mathlib.Topology.Connected.LocallyConnected

@[expose] public section

/-!
# Perturbation on the actual nonfixed component

The support may be bounded or unbounded. Agreement after left-composition is
on the preimage of the support complement: if the support lies above `l`, the
modified map agrees with `a` whenever `a x ≤ l`, equivalently `x ≤ a⁻¹ l`.
-/

namespace FnZPositiveCones.NoncofinalComponentPerturbation

open NoncofinalPerturbation
open scoped Topology

abbrev motionComponent (f : ℝ ≃o ℝ) (t : ℝ) : Set ℝ :=
  connectedComponentIn {x : ℝ | f x ≠ x} t

theorem motionComponent_ordConnected (f : ℝ ≃o ℝ) (t : ℝ) :
    Set.OrdConnected (motionComponent f t) := isPreconnected_connectedComponentIn.ordConnected

theorem motionComponent_isOpen (f : ℝ ≃o ℝ) (t : ℝ) : IsOpen (motionComponent f t) :=
  (isOpen_ne_fun f.continuous continuous_id).connectedComponentIn

/-- The image of the basepoint stays in the same component of nonfixed points. -/
theorem apply_mem_motionComponent (f : ℝ ≃o ℝ) (t : ℝ) (ht : f t ≠ t) :
    f t ∈ motionComponent f t := by
  rcases lt_or_gt_of_ne ht with hlo | hhi
  · have hsub : Set.Icc (f t) t ⊆ {x : ℝ | f x ≠ x} := by
      intro x hx he
      by_cases hxt : x = t
      · exact ht (hxt ▸ he)
      · have hxlt : x < t := lt_of_le_of_ne hx.2 hxt
        have h := f.strictMono hxlt
        rw [he] at h
        exact h.not_ge hx.1
    exact isPreconnected_Icc.subset_connectedComponentIn ⟨hlo.le, le_rfl⟩ hsub
      ⟨le_rfl, hlo.le⟩
  · have hsub : Set.Icc t (f t) ⊆ {x : ℝ | f x ≠ x} := by
      intro x hx he
      by_cases hxt : t = x
      · exact ht (hxt.symm ▸ he)
      · have hxlt : t < x := lt_of_le_of_ne hx.1 hxt
        have h := f.strictMono hxlt
        rw [he] at h
        exact h.not_ge hx.2
    exact isPreconnected_Icc.subset_connectedComponentIn ⟨le_rfl, hhi.le⟩ hsub
      ⟨hhi.le, le_rfl⟩

/-- The defining automorphism preserves its entire nonfixed component in both directions. -/
theorem motionComponent_invariant (f : ℝ ≃o ℝ) (t : ℝ) (ht : f t ≠ t) :
    ∀ x : ℝ, x ∈ motionComponent f t ↔ f x ∈ motionComponent f t := by
  have himg : f '' {x : ℝ | f x ≠ x} = {x : ℝ | f x ≠ x} := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact f.injective.ne hx
    · intro hy
      change f y ≠ y at hy
      refine ⟨f⁻¹ y, ?_, RelIso.apply_inv_self f y⟩
      intro he
      apply hy
      simpa only [RelIso.apply_inv_self] using congrArg f he
  have he := f.toHomeomorph.image_connectedComponentIn
    (s := {y : ℝ | f y ≠ y}) (x := t) ht
  change f '' motionComponent f t = connectedComponentIn (f '' {y : ℝ | f y ≠ y}) (f t) at he
  rw [himg, ← connectedComponentIn_eq (apply_mem_motionComponent f t ht)] at he
  change f '' motionComponent f t = motionComponent f t at he
  intro x
  constructor
  · intro hx
    rw [← he]
    exact ⟨x, hx, rfl⟩
  · intro hx
    rw [← he] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    exact f.injective hyx ▸ hy

/-- Invariance of a set automatically extends to all integer powers. -/
theorem invariant_zpow (f : ℝ ≃o ℝ) (S : Set ℝ)
    (hf : ∀ x : ℝ, x ∈ S ↔ f x ∈ S) (n : ℤ) :
    ∀ x : ℝ, x ∈ S ↔ (f ^ n) x ∈ S := by
  apply zpow_induction_left (g := f) (P := fun a => ∀ x, x ∈ S ↔ a x ∈ S)
  · intro x
    simp
  · intro a ha x
    change x ∈ S ↔ f (a x) ∈ S
    exact (ha x).trans (hf (a x))
  · intro a ha x
    change x ∈ S ↔ f⁻¹ (a x) ∈ S
    have hi : a x ∈ S ↔ f⁻¹ (a x) ∈ S := by
      simpa only [RelIso.apply_inv_self] using (hf (f⁻¹ (a x))).symm
    exact (ha x).trans hi

/-- Any two points of the same nonfixed component lie between integer iterates.
The lower-bound contradiction uses an actual fixed infimum inside the component. -/
theorem exists_zpow_lt_in_component (f : ℝ ≃o ℝ) (t : ℝ) {x y : ℝ}
    (hx : x ∈ motionComponent f t) (hy : y ∈ motionComponent f t) :
    ∃ k : ℤ, (f ^ k) y < x := by
  by_contra hn
  have hb : BddBelow (Set.range (fun k : ℤ => (f ^ k) y)) := by
    refine ⟨x, ?_⟩
    rintro _ ⟨k, rfl⟩
    exact le_of_not_gt (fun hk => hn ⟨k, hk⟩)
  have hxi : x ≤ sInf (Set.range (fun k : ℤ => (f ^ k) y)) := by
    apply le_csInf (Set.range_nonempty _)
    rintro _ ⟨k, rfl⟩
    exact le_of_not_gt (fun hk => hn ⟨k, hk⟩)
  have hiy : sInf (Set.range (fun k : ℤ => (f ^ k) y)) ≤ y := csInf_le hb ⟨0, by simp⟩
  have hi := (motionComponent_ordConnected f t).out hx hy ⟨hxi, hiy⟩
  exact (connectedComponentIn_subset _ _ hi)
    (NoncofinalDynamics.orbit_sInf_fixed (MonoidHom.id _) f y hb)

/-- Actual component-supported power, with its inverse checked by `truncate`. -/
noncomputable def componentTwist (f : ℝ ≃o ℝ) (t : ℝ) (ht : f t ≠ t) (k : ℤ) : ℝ ≃o ℝ :=
  truncate (f ^ k) (motionComponent f t) (motionComponent_ordConnected f t)
    (invariant_zpow f _ (motionComponent_invariant f t ht) k)

/-- Component entry is the exact local geometric input needed to create a fixed point.
Neither boundedness nor a finite upper endpoint of the component is assumed. -/
theorem exists_fixed_componentTwist_mul (f a : ℝ ≃o ℝ) (l t : ℝ) (ht : f t ≠ t)
    (hlt : l < t) (hleft : Set.Ioc l t ⊆ motionComponent f t)
    (hlower : motionComponent f t ⊆ Set.Ioi l) (ha : a l ∈ motionComponent f t) :
    ∃ k : ℤ, ∃ x : ℝ, l < x ∧ (componentTwist f t ht k * a) x = x := by
  have hnhds : a ⁻¹' motionComponent f t ∈ 𝓝 l :=
    ((motionComponent_isOpen f t).preimage a.continuous).mem_nhds ha
  obtain ⟨v, w, hlvw, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp hnhds
  obtain ⟨x, hlx, hx⟩ := exists_between (lt_min hlt hlvw.2)
  have hxJ : x ∈ motionComponent f t := hleft ⟨hlx, (lt_min_iff.mp hx).1.le⟩
  have haxJ : a x ∈ motionComponent f t := hsub ⟨hlvw.1.trans hlx, (lt_min_iff.mp hx).2⟩
  obtain ⟨k, hk⟩ := exists_zpow_lt_in_component f t hxJ haxJ
  let b := componentTwist f t ht k * a
  have hbl : l < b l := by
    change l < componentTwist f t ht k (a l)
    rw [componentTwist, truncate_of_mem _ _ _ _ ha]
    exact hlower ((invariant_zpow f _ (motionComponent_invariant f t ht) k (a l)).mp ha)
  have hbx : b x < x := by
    change componentTwist f t ht k (a x) < x
    rwa [componentTwist, truncate_of_mem _ _ _ _ haxJ]
  obtain ⟨y, hy, hby⟩ := exists_mem_Icc_isFixedPt b.continuous.continuousOn hlx.le hbl.le hbx.le
  refine ⟨k, y, lt_of_le_of_ne hy.1 ?_, hby⟩
  intro he
  subst y
  exact hbl.ne' hby

/-- Central invariance of the actual component preserves the commutation relation. -/
theorem componentTwist_commute (f q : ℝ ≃o ℝ) (t : ℝ) (ht : f t ≠ t)
    (hcomm : Commute f q)
    (hqJ : ∀ x : ℝ, x ∈ motionComponent f t ↔ q x ∈ motionComponent f t) (k : ℤ) :
    Commute (componentTwist f t ht k) q :=
  truncate_commute (f ^ k) q _ (motionComponent_ordConnected f t)
    (invariant_zpow f _ (motionComponent_invariant f t ht) k) hqJ (hcomm.zpow_left k)

/-- Exact agreement is outside the support preimage, including all protected old images. -/
theorem componentTwist_mul_agrees (f a : ℝ ≃o ℝ) (t : ℝ) (ht : f t ≠ t)
    (k : ℤ) {x : ℝ} (hx : a x ∉ motionComponent f t) :
    (componentTwist f t ht k * a) x = a x :=
  truncate_of_not_mem (f ^ k) _ (motionComponent_ordConnected f t)
    (invariant_zpow f _ (motionComponent_invariant f t ht) k) hx

/-- If the component is above `l`, agreement holds through `a⁻¹(l)`. -/
theorem componentTwist_mul_agrees_of_le (f a : ℝ ≃o ℝ) (l t : ℝ) (ht : f t ≠ t)
    (hlower : motionComponent f t ⊆ Set.Ioi l) (k : ℤ) {x : ℝ} (hx : x ≤ a⁻¹ l) :
    (componentTwist f t ht k * a) x = a x := by
  apply componentTwist_mul_agrees
  intro h
  have hax : a x ≤ l := by simpa only [RelIso.apply_inv_self] using a.monotone hx
  exact (hlower h).not_ge hax

/-- The complete local entry-to-perturbation contract: an explicit supported
power creates a fixed point, preserves the central relation, and preserves
all protected old images outside the component. No global dynamical property
of the modified representation is asserted without an additional argument. -/
theorem exists_component_perturbation (f a q : ℝ ≃o ℝ) (l t : ℝ) (ht : f t ≠ t)
    (hlt : l < t) (hleft : Set.Ioc l t ⊆ motionComponent f t)
    (hlower : motionComponent f t ⊆ Set.Ioi l) (ha : a l ∈ motionComponent f t)
    (hfq : Commute f q) (haq : Commute a q)
    (hqJ : ∀ x : ℝ, x ∈ motionComponent f t ↔ q x ∈ motionComponent f t) :
    ∃ k : ℤ, Commute (componentTwist f t ht k * a) q ∧
      (∃ x : ℝ, l < x ∧ (componentTwist f t ht k * a) x = x) ∧
      ∀ x : ℝ, a x ∉ motionComponent f t → (componentTwist f t ht k * a) x = a x := by
  obtain ⟨k, x, hlx, hx⟩ := exists_fixed_componentTwist_mul f a l t ht hlt hleft hlower ha
  exact ⟨k, (componentTwist_commute f q t ht hfq hqJ k).mul_left haq,
    ⟨x, hlx, hx⟩, fun _ h => componentTwist_mul_agrees f a t ht k h⟩

end FnZPositiveCones.NoncofinalComponentPerturbation
