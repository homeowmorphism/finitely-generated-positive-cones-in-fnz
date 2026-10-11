module

public import FnZPositiveCones.External.NoncofinalComponentPerturbation

@[expose] public section

/-!
# Moving an entering component beyond a basis-dependent bound

Once a fixed-point-free map `a` enters one moving component, translate that
component by powers of `a`. The same map still enters every translated
component. This permits choosing a primitive basis first, computing all
finite trajectory bounds in that basis, and moving the component afterwards.
It makes no claim about translating a fixed point of `a` by its own powers.
-/

namespace FnZPositiveCones.NoncofinalPrimitiveTranslate

open NoncofinalComponentPerturbation

/-- An increasing homeomorphism with no fixed points has an integer orbit
unbounded above, at every point. -/
theorem exists_zpow_above (a : ℝ ≃o ℝ) (hn : ∀ x : ℝ, a x ≠ x) (l B : ℝ) :
    ∃ k : ℤ, B < (a ^ k) l := by
  by_contra! h
  have hb : BddAbove (Set.range (fun k : ℤ => (a ^ k) l)) := by
    refine ⟨B, ?_⟩
    rintro _ ⟨k, rfl⟩
    exact h k
  exact hn _ (NoncofinalDynamics.orbit_sSup_fixed (MonoidHom.id _) a l hb)

/-- Conjugation transports the actual connected component of nonfixed
points, including components with an infinite endpoint. -/
theorem image_motionComponent (e f : ℝ ≃o ℝ) {t : ℝ} (ht : f t ≠ t) :
    e '' motionComponent f t = motionComponent (e * f * e⁻¹) (e t) := by
  have himg : e '' {x : ℝ | f x ≠ x} = {x : ℝ | (e * f * e⁻¹) x ≠ x} := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa only [Set.mem_ofPred_eq, RelIso.mul_apply, RelIso.inv_apply_self]
        using e.injective.ne hx
    · intro hy
      refine ⟨e⁻¹ y, ?_, RelIso.apply_inv_self e y⟩
      intro he
      apply hy
      simp only [RelIso.mul_apply, he, RelIso.apply_inv_self]
  have he := e.toHomeomorph.image_connectedComponentIn
    (s := {x : ℝ | f x ≠ x}) (x := t) ht
  change e '' motionComponent f t = connectedComponentIn (e '' {x : ℝ | f x ≠ x}) (e t) at he
  simpa only [himg] using he

/-- Membership form of component transport. -/
theorem mem_translated_component (e f : ℝ ≃o ℝ) {t x : ℝ} (ht : f t ≠ t) :
    e x ∈ motionComponent (e * f * e⁻¹) (e t) ↔ x ∈ motionComponent f t := by
  rw [← image_motionComponent e f ht]
  exact e.injective.mem_set_image

/-- An order automorphism transports all the component geometry and central
compatibility needed by the perturbation theorem. The entering map is left
unchanged when it commutes with the translating automorphism. -/
theorem translate_component_data
    (e f a q : ℝ ≃o ℝ) (l t : ℝ)
    (ht : f t ≠ t) (hlt : l < t)
    (hleft : Set.Ioc l t ⊆ motionComponent f t)
    (hlower : motionComponent f t ⊆ Set.Ioi l)
    (ha : a l ∈ motionComponent f t)
    (hea : Commute e a) (heq : Commute e q) (hfq : Commute f q)
    (hqJ : ∀ x : ℝ, x ∈ motionComponent f t ↔ q x ∈ motionComponent f t)
    (hql : q l = l) :
    (e * f * e⁻¹) (e t) ≠ e t ∧ e l < e t ∧
    Set.Ioc (e l) (e t) ⊆ motionComponent (e * f * e⁻¹) (e t) ∧
    motionComponent (e * f * e⁻¹) (e t) ⊆ Set.Ioi (e l) ∧
    a (e l) ∈ motionComponent (e * f * e⁻¹) (e t) ∧
    Commute (e * f * e⁻¹) q ∧
    (∀ x : ℝ, x ∈ motionComponent (e * f * e⁻¹) (e t) ↔
      q x ∈ motionComponent (e * f * e⁻¹) (e t)) ∧ q (e l) = e l := by
  have heafun (x : ℝ) : a (e x) = e (a x) :=
    (congrArg (fun h : ℝ ≃o ℝ => h x) hea.eq).symm
  have heqfun (x : ℝ) : q (e x) = e (q x) :=
    (congrArg (fun h : ℝ ≃o ℝ => h x) heq.eq).symm
  refine ⟨?_, e.strictMono hlt, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [RelIso.mul_apply, RelIso.inv_apply_self] using e.injective.ne ht
  · intro x hx
    have hx' : e⁻¹ x ∈ Set.Ioc l t := by
      constructor
      · simpa only [RelIso.inv_apply_self] using (e⁻¹).strictMono hx.1
      · simpa only [RelIso.inv_apply_self] using (e⁻¹).monotone hx.2
    simpa only [RelIso.apply_inv_self] using
      (mem_translated_component e f ht).mpr (hleft hx')
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := (image_motionComponent e f ht).symm ▸ hx
    exact e.strictMono (hlower hy)
  · rw [heafun]
    exact (mem_translated_component e f ht).mpr ha
  · exact (heq.mul_left hfq).mul_left heq.inv_left
  · intro x
    obtain ⟨y, rfl⟩ := e.surjective x
    rw [heqfun, mem_translated_component e f ht, mem_translated_component e f ht]
    exact hqJ y
  · rw [heqfun, hql]

/-- Translate by a power of the same entering map after any desired bound
has been fixed. The actual entering map, and therefore its primitive basis,
does not change with the bound. -/
theorem exists_component_entry_above
    (f a q : ℝ ≃o ℝ) (l t : ℝ)
    (ht : f t ≠ t) (hlt : l < t)
    (hleft : Set.Ioc l t ⊆ motionComponent f t)
    (hlower : motionComponent f t ⊆ Set.Ioi l)
    (ha : a l ∈ motionComponent f t)
    (hn : ∀ x : ℝ, a x ≠ x)
    (haq : Commute a q) (hfq : Commute f q)
    (hqJ : ∀ x : ℝ, x ∈ motionComponent f t ↔ q x ∈ motionComponent f t)
    (hql : q l = l) (B : ℝ) :
    ∃ k : ℤ, let e := a ^ k
      B < e l ∧ (e * f * e⁻¹) (e t) ≠ e t ∧ e l < e t ∧
      Set.Ioc (e l) (e t) ⊆ motionComponent (e * f * e⁻¹) (e t) ∧
      motionComponent (e * f * e⁻¹) (e t) ⊆ Set.Ioi (e l) ∧
      a (e l) ∈ motionComponent (e * f * e⁻¹) (e t) ∧
      Commute (e * f * e⁻¹) q ∧
      (∀ x : ℝ, x ∈ motionComponent (e * f * e⁻¹) (e t) ↔
        q x ∈ motionComponent (e * f * e⁻¹) (e t)) ∧ q (e l) = e l := by
  obtain ⟨k, hk⟩ := exists_zpow_above a hn l B
  exact ⟨k, hk, translate_component_data (a ^ k) f a q l t ht hlt hleft hlower ha
    ((Commute.refl a).zpow_left k) (haq.zpow_left k) hfq hqJ hql⟩

end FnZPositiveCones.NoncofinalPrimitiveTranslate
