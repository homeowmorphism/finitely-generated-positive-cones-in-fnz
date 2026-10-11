module

public import FnZPositiveCones.External.NoncofinalDynamics
public import FnZPositiveCones.External.NoncofinalPerturbation

@[expose] public section

/-!
# A continuous replacement for the tail maps in MMRT's perturbation

Taking pointwise maxima of order automorphisms gives an explicit order
automorphism. The envelope of `a`, `a⁻¹`, `z`, and `z⁻¹` moves every point
weakly to the right and fixes precisely the common fixed points of `a` and `z`.
This avoids an unverified gluing across the central fixed-point set.
-/

namespace FnZPositiveCones
namespace NoncofinalEnvelope

universe u
variable {A : Type u} [LinearOrder A]

theorem max_strictMono (f g : A ≃o A) : StrictMono (fun x => max (f x) (g x)) := by
  intro x y hxy
  apply max_lt
  · exact (f.strictMono hxy).trans_le (le_max_left _ _)
  · exact (g.strictMono hxy).trans_le (le_max_right _ _)

/-- Pointwise maximum, with explicit inverse the pointwise minimum of inverses. -/
noncomputable def join (f g : A ≃o A) : A ≃o A :=
  (max_strictMono f g).orderIsoOfRightInverse _ (fun y => min (f.symm y) (g.symm y)) (by
    intro y
    change max (f (min (f.symm y) (g.symm y))) (g (min (f.symm y) (g.symm y))) = y
    rcases le_total (f.symm y) (g.symm y) with h | h
    · rw [min_eq_left h, f.apply_symm_apply]
      apply max_eq_left
      simpa using g.monotone h
    · rw [min_eq_right h, g.apply_symm_apply]
      apply max_eq_right
      simpa using f.monotone h)

@[simp] theorem join_apply (f g : A ≃o A) (x : A) : join f g x = max (f x) (g x) := rfl

@[simp] theorem join_symm_apply (f g : A ≃o A) (x : A) :
    (join f g).symm x = min (f.symm x) (g.symm x) := rfl

/-- Commuting with a third order automorphism is preserved under pointwise maximum. -/
theorem join_commute (f g q : A ≃o A) (hf : Commute f q) (hg : Commute g q) :
    Commute (join f g) q := by
  change join f g * q = q * join f g
  ext x
  change max (f (q x)) (g (q x)) = q (max (f x) (g x))
  rw [q.monotone.map_max]
  congr 1
  · exact congrArg (fun e : A ≃o A => e x) hf.eq
  · exact congrArg (fun e : A ≃o A => e x) hg.eq

/-- The maximum of a map and its inverse lies above the identity. -/
theorem le_join_inverse (f : A ≃o A) (x : A) : x ≤ join f f.symm x := by
  change x ≤ max (f x) (f.symm x)
  rcases le_total x (f x) with h | h
  · exact h.trans (le_max_left _ _)
  · have hi : x ≤ f.symm x := by simpa using f.symm.monotone h
    exact hi.trans (le_max_right _ _)

/-- The positive envelope of two automorphisms. -/
noncomputable def envelope (f q : A ≃o A) : A ≃o A :=
  join (join f f.symm) (join q q.symm)

theorem le_envelope (f q : A ≃o A) (x : A) : x ≤ envelope f q x :=
  (le_join_inverse f x).trans (le_max_left _ _)

theorem envelope_inverse_le (f q : A ≃o A) (x : A) : (envelope f q).symm x ≤ x := by
  simpa using le_envelope f q ((envelope f q).symm x)

/-- The envelope fixes exactly the common fixed points, including accumulation
points of the central fixed-point set. -/
theorem envelope_fixed_iff (f q : A ≃o A) (x : A) :
    envelope f q x = x ↔ f x = x ∧ q x = x := by
  have hpair (a : A ≃o A) (h : join a a.symm x ≤ x) : a x = x := by
    have hax : a x ≤ x := (le_max_left _ _).trans h
    have hix : a.symm x ≤ x := (le_max_right _ _).trans h
    have hxa : x ≤ a x := by simpa using a.monotone hix
    exact le_antisymm hax hxa
  constructor
  · intro he
    have hf : join f f.symm x ≤ x := by
      exact (le_max_left (join f f.symm x) (join q q.symm x)).trans he.le
    have hq : join q q.symm x ≤ x := by
      exact (le_max_right (join f f.symm x) (join q q.symm x)).trans he.le
    exact ⟨hpair f hf, hpair q hq⟩
  · rintro ⟨hf, hq⟩
    have hfi : f.symm x = x := by simpa only [hf] using f.symm_apply_apply x
    have hqi : q.symm x = x := by simpa only [hq] using q.symm_apply_apply x
    simp only [envelope, join_apply, hf, hq, hfi, hqi, max_self]

/-- The envelope and its inverse move strictly in opposite directions away
from the common fixed set. -/
theorem lt_envelope_of_not_common_fixed (f q : A ≃o A) {x : A}
    (hx : ¬(f x = x ∧ q x = x)) : x < envelope f q x := by
  exact lt_of_le_of_ne (le_envelope f q x) (Ne.symm (fun h => hx ((envelope_fixed_iff f q x).mp h)))

theorem envelope_inverse_lt_of_not_common_fixed (f q : A ≃o A) {x : A}
    (hx : ¬(f x = x ∧ q x = x)) : (envelope f q).symm x < x := by
  have h := (envelope f q).symm.strictMono (lt_envelope_of_not_common_fixed f q hx)
  simpa using h

/-- Centrality survives the envelope construction. -/
theorem envelope_commute (f q : A ≃o A) (hf : Commute f q) : Commute (envelope f q) q := by
  apply join_commute
  · apply join_commute f f.symm q hf
    exact hf.inv_left
  · apply join_commute q q.symm q (Commute.refl q)
    exact (Commute.refl q).inv_left

open NoncofinalPerturbation

theorem invariant_Ioi (f : A ≃o A) (p : A) (hp : f p = p) (x : A) :
    x ∈ Set.Ioi p ↔ f x ∈ Set.Ioi p := by
  have h : f p < f x ↔ p < x := f.lt_iff_lt
  simpa only [hp, Set.mem_Ioi] using h.symm

private theorem truncate_symm_apply (f : A ≃o A) (I : Set A) (hI : Set.OrdConnected I)
    (hf : ∀ x : A, x ∈ I ↔ f x ∈ I) (x : A) :
    (truncate f I hI hf).symm x = cutMap f.symm I x := rfl

/-- Splice in a new map on the right of a common fixed point, preserving the
old map on the entire left ray. The formula supplies an explicit inverse. -/
noncomputable def splice (f g : A ≃o A) (p : A) (hf : f p = p) (hg : g p = p) : A ≃o A :=
  truncate g (Set.Ioi p) Set.ordConnected_Ioi (invariant_Ioi g p hg) *
    (truncate f (Set.Ioi p) Set.ordConnected_Ioi (invariant_Ioi f p hf))⁻¹ * f

theorem splice_of_gt (f g : A ≃o A) (p : A) (hf : f p = p) (hg : g p = p)
    {x : A} (hx : p < x) : splice f g p hf hg x = g x := by
  classical
  have hfx : f x ∈ Set.Ioi p := (invariant_Ioi f p hf x).mp hx
  change truncate g (Set.Ioi p) Set.ordConnected_Ioi (invariant_Ioi g p hg)
    ((truncate f (Set.Ioi p) Set.ordConnected_Ioi (invariant_Ioi f p hf)).symm (f x)) = _
  rw [truncate_symm_apply]
  simp only [cutMap, hfx, ↓reduceIte, f.symm_apply_apply]
  exact truncate_of_mem _ _ _ _ hx

theorem splice_of_le (f g : A ≃o A) (p : A) (hf : f p = p) (hg : g p = p)
    {x : A} (hx : x ≤ p) : splice f g p hf hg x = f x := by
  classical
  have hfx : f x ∉ Set.Ioi p := fun h => not_lt_of_ge hx ((invariant_Ioi f p hf x).mpr h)
  change truncate g (Set.Ioi p) Set.ordConnected_Ioi (invariant_Ioi g p hg)
    ((truncate f (Set.Ioi p) Set.ordConnected_Ioi (invariant_Ioi f p hf)).symm (f x)) = _
  rw [truncate_symm_apply]
  simp only [cutMap, hfx, ↓reduceIte]
  exact truncate_of_not_mem _ _ _ _ hfx

theorem splice_commute (f g q : A ≃o A) (p : A)
    (hf : f p = p) (hg : g p = p) (hq : q p = p)
    (hfc : Commute f q) (hgc : Commute g q) : Commute (splice f g p hf hg) q := by
  apply Commute.mul_left _ hfc
  apply Commute.mul_left
  · exact truncate_commute g q _ Set.ordConnected_Ioi
      (invariant_Ioi g p hg) (invariant_Ioi q p hq) hgc
  · exact (truncate_commute f q _ Set.ordConnected_Ioi
      (invariant_Ioi f p hf) (invariant_Ioi q p hq) hfc).inv_left

theorem envelope_fixed (f q : A ≃o A) (p : A) (hf : f p = p) (hq : q p = p) :
    envelope f q p = p := (envelope_fixed_iff f q p).mpr ⟨hf, hq⟩

theorem envelope_inverse_fixed (f q : A ≃o A) (p : A) (hf : f p = p) (hq : q p = p) :
    (envelope f q).symm p = p := by
  simpa only [envelope_fixed f q p hf hq] using (envelope f q).symm_apply_apply p

/-- A positive tail replacement with globally compatible gluing. -/
noncomputable def positiveTail (f q : A ≃o A) (p : A) (hf : f p = p) (hq : q p = p) : A ≃o A :=
  splice f (envelope f q) p hf (envelope_fixed f q p hf hq)

/-- The corresponding negative tail replacement. -/
noncomputable def negativeTail (f q : A ≃o A) (p : A) (hf : f p = p) (hq : q p = p) : A ≃o A :=
  splice f (envelope f q).symm p hf (envelope_inverse_fixed f q p hf hq)

theorem positiveTail_ge (f q : A ≃o A) (p : A) (hf : f p = p) (hq : q p = p)
    {x : A} (hx : p < x) : x ≤ positiveTail f q p hf hq x := by
  rw [positiveTail, splice_of_gt _ _ _ _ _ hx]
  exact le_envelope f q x

theorem negativeTail_le (f q : A ≃o A) (p : A) (hf : f p = p) (hq : q p = p)
    {x : A} (hx : p < x) : negativeTail f q p hf hq x ≤ x := by
  rw [negativeTail, splice_of_gt _ _ _ _ _ hx]
  exact envelope_inverse_le f q x

theorem positiveTail_strict (f q : A ≃o A) (p : A) (hf : f p = p) (hq : q p = p)
    {x : A} (hx : p < x) (hqx : q x ≠ x) : x < positiveTail f q p hf hq x := by
  rw [positiveTail, splice_of_gt _ _ _ _ _ hx]
  exact lt_envelope_of_not_common_fixed f q (fun h => hqx h.2)

theorem negativeTail_strict (f q : A ≃o A) (p : A) (hf : f p = p) (hq : q p = p)
    {x : A} (hx : p < x) (hqx : q x ≠ x) : negativeTail f q p hf hq x < x := by
  rw [negativeTail, splice_of_gt _ _ _ _ _ hx]
  exact envelope_inverse_lt_of_not_common_fixed f q (fun h => hqx h.2)

theorem positiveTail_commute (f q : A ≃o A) (p : A) (hf : f p = p) (hq : q p = p)
    (hc : Commute f q) : Commute (positiveTail f q p hf hq) q :=
  splice_commute _ _ _ p hf _ hq hc (envelope_commute f q hc)

theorem negativeTail_commute (f q : A ≃o A) (p : A) (hf : f p = p) (hq : q p = p)
    (hc : Commute f q) : Commute (negativeTail f q p hf hq) q :=
  splice_commute _ _ _ p hf _ hq hc (envelope_commute f q hc).inv_left

/-- Both tail replacements preserve the joint fixed set with the central map. -/
theorem positiveTail_common_fixed_iff (f q : A ≃o A) (p : A)
    (hf : f p = p) (hq : q p = p) (x : A) :
    (positiveTail f q p hf hq x = x ∧ q x = x) ↔ (f x = x ∧ q x = x) := by
  rcases lt_or_ge p x with hx | hx
  · rw [positiveTail, splice_of_gt _ _ _ _ _ hx, envelope_fixed_iff]
    tauto
  · rw [positiveTail, splice_of_le _ _ _ _ _ hx]

theorem negativeTail_common_fixed_iff (f q : A ≃o A) (p : A)
    (hf : f p = p) (hq : q p = p) (x : A) :
    (negativeTail f q p hf hq x = x ∧ q x = x) ↔ (f x = x ∧ q x = x) := by
  rcases lt_or_ge p x with hx | hx
  · rw [negativeTail, splice_of_gt _ _ _ _ _ hx]
    have hi : (envelope f q).symm x = x ↔ envelope f q x = x := by
      rw [(envelope f q).symm_apply_eq, eq_comm]
    rw [hi, envelope_fixed_iff]
    tauto
  · rw [negativeTail, splice_of_le _ _ _ _ _ hx]

section GeneralAction
variable {G : Type*} [Group G] (ρ : G →* (ℝ ≃o ℝ))

private theorem image_orbit (x : ℝ) (g : G) :
    ρ g '' Set.range (fun h : G => ρ h x) = Set.range (fun h : G => ρ h x) := by
  ext y
  constructor
  · rintro ⟨_, ⟨h, rfl⟩, rfl⟩
    exact ⟨g * h, NoncofinalDynamics.act_mul ρ g h x⟩
  · rintro ⟨h, rfl⟩
    refine ⟨ρ (g⁻¹ * h) x, ⟨g⁻¹ * h, rfl⟩, ?_⟩
    rw [← NoncofinalDynamics.act_mul, mul_inv_cancel_left]

/-- Every orbit is unbounded above if there is no global fixed point. -/
theorem orbit_unbounded_above (hglobal : ∀ y : ℝ, ∃ g : G, ρ g y ≠ y) (x b : ℝ) :
    ∃ g : G, b < ρ g x := by
  by_contra hn
  have hb : BddAbove (Set.range (fun g : G => ρ g x)) := by
    refine ⟨b, ?_⟩
    rintro _ ⟨g, rfl⟩
    exact le_of_not_gt (fun h => hn ⟨g, h⟩)
  obtain ⟨g, hg⟩ := hglobal (sSup (Set.range (fun h : G => ρ h x)))
  apply hg
  rw [(ρ g).map_csSup' (Set.range_nonempty _) hb, image_orbit]

/-- Every orbit is also unbounded below. -/
theorem orbit_unbounded_below (hglobal : ∀ y : ℝ, ∃ g : G, ρ g y ≠ y) (x b : ℝ) :
    ∃ g : G, ρ g x < b := by
  by_contra hn
  have hb : BddBelow (Set.range (fun g : G => ρ g x)) := by
    refine ⟨b, ?_⟩
    rintro _ ⟨g, rfl⟩
    exact le_of_not_gt (fun h => hn ⟨g, h⟩)
  obtain ⟨g, hg⟩ := hglobal (sInf (Set.range (fun h : G => ρ h x)))
  apply hg
  rw [(ρ g).map_csInf' (Set.range_nonempty _) hb, image_orbit]

/-- A central element moving the basepoint moves every point in its group orbit. -/
theorem central_nonfixed_on_orbit (z : G) (hcentral : ∀ g : G, Commute z g)
    (x : ℝ) (hx : ρ z x ≠ x) (g : G) : ρ z (ρ g x) ≠ ρ g x := by
  intro he
  apply hx
  apply (ρ g).injective
  rw [← NoncofinalDynamics.act_mul, ← (hcentral g).eq, NoncofinalDynamics.act_mul]
  exact he

end GeneralAction

section FreeGroup
variable {ι : Type u}
variable (ρ : FreeGroup ι × Multiplicative ℤ →* (ℝ ≃o ℝ))

/-- Fixed points of all marked generators and the center are global fixed points. -/
theorem fixed_of_generators (x : ℝ)
    (hgen : ∀ i : ι, ρ (FreeGroup.of i, 1) x = x)
    (hz : ρ (cofinalProductZ (FreeGroup ι)) x = x) :
    ∀ g : FreeGroup ι × Multiplicative ℤ, ρ g x = x := by
  have hfree (g : FreeGroup ι) : ρ (g, 1) x = x := by
    induction g using FreeGroup.induction_on with
    | one => simpa only [← Prod.one_eq_mk] using NoncofinalDynamics.act_one ρ x
    | of i => exact hgen i
    | inv_of i ih =>
      have h := NoncofinalDynamics.act_inv_act ρ (FreeGroup.of i, 1) x
      rw [ih] at h
      simpa only [Prod.inv_mk, inv_one] using h
    | mul g h ihg ihh =>
      have he : (g * h, (1 : Multiplicative ℤ)) = (g, 1) * (h, 1) := by simp
      rw [he, NoncofinalDynamics.act_mul, ihh, ihg]
  have hcentral (m : Multiplicative ℤ) : ρ (1, m) x = x := by
    have he : (1, m) = cofinalProductZ (FreeGroup ι) ^ m.toAdd := by ext <;> simp [cofinalProductZ]
    rw [he]
    exact NoncofinalDynamics.fixed_zpow ρ _ hz m.toAdd
  intro g
  have he : g = (g.1, 1) * (1, g.2) := by simp
  rw [he, NoncofinalDynamics.act_mul, hcentral, hfree]

/-- Replacing a generator while preserving its joint fixed set with the center
does not create any global fixed point. -/
theorem replaceGenerator_no_global_fixed (i : ι) (a : ℝ ≃o ℝ)
    (ha : Commute a (ρ (cofinalProductZ (FreeGroup ι))))
    (hcommon : ∀ x : ℝ,
      (a x = x ∧ ρ (cofinalProductZ (FreeGroup ι)) x = x) ↔
        (ρ (FreeGroup.of i, 1) x = x ∧ ρ (cofinalProductZ (FreeGroup ι)) x = x))
    (hglobal : ∀ x : ℝ, ∃ g, ρ g x ≠ x) :
    ∀ x : ℝ, ∃ g, replaceGenerator ρ i a ha g x ≠ x := by
  intro x
  by_contra hn
  push Not at hn
  have hz : ρ (cofinalProductZ (FreeGroup ι)) x = x := by
    have h := hn (cofinalProductZ (FreeGroup ι))
    simpa only [cofinalProductZ, replaceGenerator_central] using h
  have hchosen : a x = x := by
    simpa only [replaceGenerator_chosen] using hn (FreeGroup.of i, 1)
  have hgen (j : ι) : ρ (FreeGroup.of j, 1) x = x := by
    by_cases hj : j = i
    · subst j
      exact ((hcommon x).mp ⟨hchosen, hz⟩).1
    · simpa only [replaceGenerator_other ρ i j a ha hj] using hn (FreeGroup.of j, 1)
  obtain ⟨g, hg⟩ := hglobal x
  exact hg (fixed_of_generators ρ x hgen hz g)

theorem generator_commute_center (i : ι) :
    Commute (ρ (FreeGroup.of i, 1)) (ρ (cofinalProductZ (FreeGroup ι))) :=
  (cofinalProductZ_central (FreeGroup.of i, 1)).symm.map ρ

/-- The positive-tail construction is an actual action of the full product. -/
noncomputable def positiveTailAction (i : ι) (p : ℝ)
    (hi : ρ (FreeGroup.of i, 1) p = p) (hz : ρ (cofinalProductZ (FreeGroup ι)) p = p) :
    FreeGroup ι × Multiplicative ℤ →* (ℝ ≃o ℝ) :=
  replaceGenerator ρ i (positiveTail (ρ (FreeGroup.of i, 1)) (ρ (cofinalProductZ (FreeGroup ι))) p hi hz)
    (positiveTail_commute _ _ p hi hz (generator_commute_center ρ i))

/-- The negative-tail construction is likewise an action with the same central map. -/
noncomputable def negativeTailAction (i : ι) (p : ℝ)
    (hi : ρ (FreeGroup.of i, 1) p = p) (hz : ρ (cofinalProductZ (FreeGroup ι)) p = p) :
    FreeGroup ι × Multiplicative ℤ →* (ℝ ≃o ℝ) :=
  replaceGenerator ρ i (negativeTail (ρ (FreeGroup.of i, 1)) (ρ (cofinalProductZ (FreeGroup ι))) p hi hz)
    (negativeTail_commute _ _ p hi hz (generator_commute_center ρ i))

theorem positiveTailAction_no_global_fixed (i : ι) (p : ℝ)
    (hi : ρ (FreeGroup.of i, 1) p = p) (hz : ρ (cofinalProductZ (FreeGroup ι)) p = p)
    (hglobal : ∀ x : ℝ, ∃ g, ρ g x ≠ x) :
    ∀ x : ℝ, ∃ g, positiveTailAction ρ i p hi hz g x ≠ x :=
  replaceGenerator_no_global_fixed ρ i _ _ (positiveTail_common_fixed_iff _ _ p hi hz) hglobal

theorem negativeTailAction_no_global_fixed (i : ι) (p : ℝ)
    (hi : ρ (FreeGroup.of i, 1) p = p) (hz : ρ (cofinalProductZ (FreeGroup ι)) p = p)
    (hglobal : ∀ x : ℝ, ∃ g, ρ g x ≠ x) :
    ∀ x : ℝ, ∃ g, negativeTailAction ρ i p hi hz g x ≠ x :=
  replaceGenerator_no_global_fixed ρ i _ _ (negativeTail_common_fixed_iff _ _ p hi hz) hglobal

@[simp] theorem positiveTailAction_central (i : ι) (p : ℝ)
    (hi : ρ (FreeGroup.of i, 1) p = p) (hz : ρ (cofinalProductZ (FreeGroup ι)) p = p)
    (m : Multiplicative ℤ) : positiveTailAction ρ i p hi hz (1, m) = ρ (1, m) := by
  exact replaceGenerator_central ρ i _ _ m

@[simp] theorem negativeTailAction_central (i : ι) (p : ℝ)
    (hi : ρ (FreeGroup.of i, 1) p = p) (hz : ρ (cofinalProductZ (FreeGroup ι)) p = p)
    (m : Multiplicative ℤ) : negativeTailAction ρ i p hi hz (1, m) = ρ (1, m) := by
  exact replaceGenerator_central ρ i _ _ m

/-- Strict positive motion at every sufficiently high point in the perturbed
basepoint orbit; this supplies the direct comparison-of-orders argument. -/
theorem positiveTailAction_orbit_strict (i : ι) (p : ℝ)
    (hi : ρ (FreeGroup.of i, 1) p = p) (hz : ρ (cofinalProductZ (FreeGroup ι)) p = p)
    (x : ℝ) (hx : ρ (cofinalProductZ (FreeGroup ι)) x ≠ x)
    (g : FreeGroup ι × Multiplicative ℤ)
    (hgp : p < positiveTailAction ρ i p hi hz g x) :
    positiveTailAction ρ i p hi hz g x <
      positiveTailAction ρ i p hi hz (FreeGroup.of i, 1) (positiveTailAction ρ i p hi hz g x) := by
  have hcenter : positiveTailAction ρ i p hi hz (cofinalProductZ (FreeGroup ι)) =
      ρ (cofinalProductZ (FreeGroup ι)) := positiveTailAction_central ρ i p hi hz _
  have hn := central_nonfixed_on_orbit (positiveTailAction ρ i p hi hz)
    (cofinalProductZ (FreeGroup ι)) cofinalProductZ_central x (by rwa [hcenter]) g
  rw [hcenter] at hn
  change _ < replaceGenerator ρ i _ _ (FreeGroup.of i, 1) _
  rw [replaceGenerator_chosen]
  exact positiveTail_strict _ _ p hi hz hgp hn

theorem negativeTailAction_orbit_strict (i : ι) (p : ℝ)
    (hi : ρ (FreeGroup.of i, 1) p = p) (hz : ρ (cofinalProductZ (FreeGroup ι)) p = p)
    (x : ℝ) (hx : ρ (cofinalProductZ (FreeGroup ι)) x ≠ x)
    (g : FreeGroup ι × Multiplicative ℤ)
    (hgp : p < negativeTailAction ρ i p hi hz g x) :
    negativeTailAction ρ i p hi hz (FreeGroup.of i, 1) (negativeTailAction ρ i p hi hz g x) <
      negativeTailAction ρ i p hi hz g x := by
  have hcenter : negativeTailAction ρ i p hi hz (cofinalProductZ (FreeGroup ι)) =
      ρ (cofinalProductZ (FreeGroup ι)) := negativeTailAction_central ρ i p hi hz _
  have hn := central_nonfixed_on_orbit (negativeTailAction ρ i p hi hz)
    (cofinalProductZ (FreeGroup ι)) cofinalProductZ_central x (by rwa [hcenter]) g
  rw [hcenter] at hn
  change replaceGenerator ρ i _ _ (FreeGroup.of i, 1) _ < _
  rw [replaceGenerator_chosen]
  exact negativeTail_strict _ _ p hi hz hgp hn

end FreeGroup

end NoncofinalEnvelope
end FnZPositiveCones
