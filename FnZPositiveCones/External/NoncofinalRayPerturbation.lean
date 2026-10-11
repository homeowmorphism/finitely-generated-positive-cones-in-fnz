module

public import FnZPositiveCones.External.NoncofinalCrossings
public import FnZPositiveCones.External.NoncofinalEnvelope

@[expose] public section

/-!
# Unbounded support intervals in the noncofinal perturbation

A component lying to the right of a compact set can be a ray. Crossings do
not by themselves force bounded components, so the ray case is checked here
alongside the existing bounded-interval modification.
-/

namespace FnZPositiveCones.NoncofinalRayPerturbation

open NoncofinalCrossings NoncofinalPerturbation

/-- Fixing a ray endpoint makes every integer power preserve the ray. -/
theorem invariant_Ioi_zpow (f : ℝ ≃o ℝ) (l : ℝ) (hl : f l = l) (k : ℤ) (x : ℝ) :
    x ∈ Set.Ioi l ↔ (f ^ k) x ∈ Set.Ioi l := by
  have he : (f ^ k) l = l := NoncofinalCrossings.fixed_zpow f hl k
  simpa only [Set.mem_Ioi, he] using ((f ^ k).lt_iff_lt (x := l) (y := x)).symm

/-- Integer powers descend past every point of a ray without fixed points. -/
theorem exists_zpow_lt_on_ray (f : ℝ ≃o ℝ) (l : ℝ)
    (hfix : ∀ x, l < x → f x ≠ x) {y t : ℝ} (ht : l < t) :
    ∃ k : ℤ, (f ^ k) y < t := by
  by_contra hn
  have hb : BddBelow (Set.range (fun k : ℤ => (f ^ k) y)) := by
    refine ⟨t, ?_⟩
    rintro _ ⟨k, rfl⟩
    exact le_of_not_gt (fun hk => hn ⟨k, hk⟩)
  have htl : t ≤ sInf (Set.range (fun k : ℤ => (f ^ k) y)) := by
    apply le_csInf (Set.range_nonempty _)
    rintro _ ⟨k, rfl⟩
    exact le_of_not_gt (fun hk => hn ⟨k, hk⟩)
  exact hfix _ (ht.trans_le htl)
    (NoncofinalDynamics.orbit_sInf_fixed (MonoidHom.id _) f y hb)

/-- The missing unbounded-interval case of the local perturbation: a truncated
integer power creates an interior fixed point after composition. -/
theorem exists_fixed_truncate_ray_zpow_mul (f a : ℝ ≃o ℝ) (l : ℝ)
    (hl : f l = l) (hfix : ∀ x, l < x → f x ≠ x) (ha : l < a l) :
    ∃ k : ℤ, ∃ x, l < x ∧
      (truncate (f ^ k) (Set.Ioi l) Set.ordConnected_Ioi
        (invariant_Ioi_zpow f l hl k) * a) x = x := by
  let t := l + 1
  have hlt : l < t := by dsimp [t]; linarith
  obtain ⟨k, hk⟩ := exists_zpow_lt_on_ray f l hfix (y := a t) hlt
  let b : ℝ ≃o ℝ := truncate (f ^ k) (Set.Ioi l) Set.ordConnected_Ioi
    (invariant_Ioi_zpow f l hl k) * a
  have hbl : l < b l := by
    change l < truncate (f ^ k) (Set.Ioi l) Set.ordConnected_Ioi
      (invariant_Ioi_zpow f l hl k) (a l)
    rw [truncate_of_mem (f ^ k) (Set.Ioi l) Set.ordConnected_Ioi
      (invariant_Ioi_zpow f l hl k) ha]
    exact (invariant_Ioi_zpow f l hl k (a l)).mp ha
  have hbt : b t < t := by
    change truncate (f ^ k) (Set.Ioi l) Set.ordConnected_Ioi
      (invariant_Ioi_zpow f l hl k) (a t) < t
    rwa [truncate_of_mem (f ^ k) (Set.Ioi l) Set.ordConnected_Ioi
      (invariant_Ioi_zpow f l hl k) (ha.trans (a.strictMono hlt))]
  obtain ⟨x, hx, hbx⟩ := exists_mem_Icc_isFixedPt b.continuous.continuousOn hlt.le hbl.le hbt.le
  refine ⟨k, x, lt_of_le_of_ne hx.1 ?_, hbx⟩
  intro he
  subst x
  exact hbl.ne' hbx

/-- Truncated powers still commute with the central map when it fixes the ray endpoint. -/
theorem truncate_ray_zpow_commute (f q : ℝ ≃o ℝ) (l : ℝ)
    (hl : f l = l) (hq : q l = l) (hc : Commute f q) (k : ℤ) :
    Commute (truncate (f ^ k) (Set.Ioi l) Set.ordConnected_Ioi
      (invariant_Ioi_zpow f l hl k)) q := by
  apply truncate_commute
  · intro x
    simpa only [Set.mem_Ioi, hq] using (q.lt_iff_lt (x := l) (y := x)).symm
  · exact hc.zpow_left k

/-- The ray modification preserves every old value whose image lies at or below its endpoint. -/
theorem truncate_ray_zpow_mul_agrees (f a : ℝ ≃o ℝ) (l : ℝ)
    (hl : f l = l) (k : ℤ) {x : ℝ} (hx : a x ≤ l) :
    (truncate (f ^ k) (Set.Ioi l) Set.ordConnected_Ioi
      (invariant_Ioi_zpow f l hl k) * a) x = a x := by
  exact truncate_of_not_mem (f ^ k) (Set.Ioi l) Set.ordConnected_Ioi
    (invariant_Ioi_zpow f l hl k) (not_lt_of_ge hx)

/-- A crossing has an element with a fixed lower endpoint followed by a nonempty
interval of motion. The interval need not have a finite upper endpoint. -/
theorem crossing_lower_fixed_endpoint {f g : ℝ ≃o ℝ} {u v w : ℝ}
    (hc : Crossing f g u v w) :
    ∃ l : ℝ, u ≤ l ∧ l < v ∧ f l = l ∧ f v < v ∧
      ∀ x : ℝ, l < x → x ≤ v → f x ≠ x := by
  have hfv : f v < v := by
    by_contra h
    have hvf : v ≤ f v := le_of_not_gt h
    have hn (n : ℕ) : v ≤ (f ^ n) v := by
      induction n with
      | zero => simp
      | succ n ih =>
        simpa only [pow_succ', RelIso.mul_apply] using hvf.trans (f.monotone ih)
    obtain ⟨N, M, hN, hM⟩ := hc.crosses
    exact (hn N).not_gt (hN.trans hc.middle_lt_right)
  have hvi : v ≤ f⁻¹ v := f.le_iff_le.mp (by simpa using hfv.le)
  have hninv (n : ℕ) : v ≤ ((f⁻¹) ^ n) v := by
    induction n with
    | zero => simp
    | succ n ih =>
      simpa only [pow_succ', RelIso.mul_apply] using hvi.trans ((f⁻¹).monotone ih)
  have hb (n : ℤ) : u < (f ^ n) v := by
    cases n with
    | ofNat n => simpa using hc.right_bounded n
    | negSucc n =>
      simpa only [zpow_negSucc, inv_pow] using
        (hc.left_lt_middle.trans hc.middle_lt_right).trans_le (hninv (n + 1))
  let S := Set.range (fun n : ℤ => (f ^ n) v)
  have hbounded : BddBelow S := ⟨u, by rintro _ ⟨n, rfl⟩; exact (hb n).le⟩
  have hnonempty : S.Nonempty := Set.range_nonempty _
  refine ⟨sInf S, le_csInf hnonempty (by rintro _ ⟨n, rfl⟩; exact (hb n).le), ?_, ?_, hfv, ?_⟩
  · exact (csInf_le hbounded ⟨1, by simp⟩).trans_lt hfv
  · exact NoncofinalDynamics.orbit_sInf_fixed (MonoidHom.id _) f v hbounded
  · intro x hlx hxv hfix
    have hx : x ≤ sInf S := by
      apply le_csInf hnonempty
      rintro _ ⟨n, rfl⟩
      have hm := (f ^ n).monotone hxv
      simpa only [NoncofinalCrossings.fixed_zpow f hfix] using hm
    exact hlx.not_ge hx

/-- Conjugating the crossing moves its fixed lower endpoint past any prescribed
bound. Only unbounded orbits, supplied here by absence of a global fixed point,
are needed; minimality is not assumed. The whole nonfixed component then lies
on the right of the bound, whether or not it has a finite upper endpoint. -/
theorem crossing_component_above {G : Type*} [Group G]
    (ρ : G →* (ℝ ≃o ℝ)) (hglobal : ∀ x : ℝ, ∃ g : G, ρ g x ≠ x)
    {f g : G} {u v w : ℝ} (hc : Crossing (ρ f) (ρ g) u v w) (p : ℝ) :
    ∃ a : G, ∃ l t : ℝ, p < l ∧ l < t ∧ ρ a l = l ∧ ρ a t < t ∧
      Set.Ioc l t ⊆ connectedComponentIn {x : ℝ | ρ a x ≠ x} t ∧
      connectedComponentIn {x : ℝ | ρ a x ≠ x} t ⊆ Set.Ioi l := by
  obtain ⟨l, hul, hlv, hfl, hfv, hfix⟩ := crossing_lower_fixed_endpoint hc
  obtain ⟨h, hhp⟩ := NoncofinalEnvelope.orbit_unbounded_above ρ hglobal l p
  let a := h * f * h⁻¹
  have hal : ρ a (ρ h l) = ρ h l := by
    simp only [a, map_mul, map_inv, RelIso.mul_apply, RelIso.inv_apply_self, hfl]
  have hat : ρ a (ρ h v) < ρ h v := by
    simpa only [a, map_mul, map_inv, RelIso.mul_apply, RelIso.inv_apply_self] using
      (ρ h).strictMono hfv
  have hlt : ρ h l < ρ h v := (ρ h).strictMono hlv
  have hfix' : ∀ x ∈ Set.Ioc (ρ h l) (ρ h v), ρ a x ≠ x := by
    intro x hx he
    have hx' : l < (ρ h)⁻¹ x ∧ (ρ h)⁻¹ x ≤ v := by
      constructor
      · simpa only [RelIso.inv_apply_self] using ((ρ h)⁻¹).strictMono hx.1
      · simpa only [RelIso.inv_apply_self] using ((ρ h)⁻¹).monotone hx.2
    apply hfix ((ρ h)⁻¹ x) hx'.1 hx'.2
    have hh := congrArg (fun y : ℝ => (ρ h)⁻¹ y) he
    simpa only [a, map_mul, map_inv, RelIso.mul_apply, RelIso.inv_apply_self] using hh
  have hsub : Set.Ioc (ρ h l) (ρ h v) ⊆
      connectedComponentIn {x : ℝ | ρ a x ≠ x} (ρ h v) :=
    isPreconnected_Ioc.subset_connectedComponentIn ⟨hlt, le_rfl⟩ hfix'
  refine ⟨a, ρ h l, ρ h v, hhp, hlt, hal, hat, hsub, ?_⟩
  intro x hx
  have hv : ρ h v ∈ connectedComponentIn {x : ℝ | ρ a x ≠ x} (ρ h v) :=
    mem_connectedComponentIn hat.ne
  have hconn := (isPreconnected_connectedComponentIn
    (F := {x : ℝ | ρ a x ≠ x}) (x := ρ h v)).ordConnected
  by_contra hn
  have hl := hconn.out hx hv ⟨le_of_not_gt hn, hlt.le⟩
  exact (connectedComponentIn_subset _ _ hl) hal

end FnZPositiveCones.NoncofinalRayPerturbation
