module

public import FnZPositiveCones.External.NoncofinalCrossingExistence
public import Mathlib.Topology.Homeomorph.Lemmas

@[expose] public section

/-!
# Crossings on a central fixed-point orbit

Use the lower endpoint of the central cyclic orbit instead of the free
basepoint orbit. Strict coset inequalities remain strict on this endpoint
orbit, and all its points are fixed by the central action. Consequently the
cyclic limits used to extract a moving component remain central fixed points.
-/

namespace FnZPositiveCones.NoncofinalFixedCrossing

open NoncofinalConvexJump NoncofinalCrossings NoncofinalCrossingExistence

universe u
variable {G : Type u} [Group G]

noncomputable def lowerEndpoint {O : LeftGroupOrder G} (R : TightRealization O) (z : G) : ℝ :=
  sInf (Set.range (fun n : ℤ => R.action (z ^ n) R.base))

/-- The endpoint is central-fixed, using a genuine finite lower bound. -/
theorem lowerEndpoint_fixed {O : LeftGroupOrder G} (R : TightRealization O) (z : G)
    (hb : BddBelow (Set.range (fun n : ℤ => R.action (z ^ n) R.base))) :
    R.action z (lowerEndpoint R z) = lowerEndpoint R z :=
  NoncofinalDynamics.orbit_sInf_fixed R.action z R.base hb

/-- A moving central orbit has its finite lower endpoint strictly below the basepoint. -/
theorem lowerEndpoint_lt_base {O : LeftGroupOrder G} (R : TightRealization O) (z : G)
    (hb : BddBelow (Set.range (fun n : ℤ => R.action (z ^ n) R.base)))
    (hz : R.action z R.base ≠ R.base) : lowerEndpoint R z < R.base := by
  obtain ⟨n, hn⟩ := exists_zpow_lt_of_mem (R.action z) hz (mem_orbitInterval_self _ _)
  exact (csInf_le hb ⟨n, rfl⟩).trans_lt (by simpa only [map_zpow] using hn)

/-- Strict ordered-coset comparison is preserved by the endpoint orbit.
Every `h*z^n` represents the same coset as `h`; comparing with all those
representatives puts the entire free basepoint below the second endpoint. -/
theorem coset_lt_endpoint_orbit (O : LeftGroupOrder G) (C : Subgroup G)
    (hC : letI := O.order; Set.OrdConnected (C : Set G)) (R : TightRealization O)
    (z : G) (hzC : z ∈ C)
    (hb : BddBelow (Set.range (fun n : ℤ => R.action (z ^ n) R.base)))
    (hz : R.action z R.base ≠ R.base) {g h : G}
    (hgh : letI := cosetLinearOrder O C hC
      (QuotientGroup.mk g : G ⧸ C) < QuotientGroup.mk h) :
    R.action g (lowerEndpoint R z) < R.action h (lowerEndpoint R z) := by
  let := cosetLinearOrder O C hC
  have hrep (n : ℤ) : (QuotientGroup.mk (h * z ^ n) : G ⧸ C) = QuotientGroup.mk h := by
    apply QuotientGroup.eq.mpr
    simpa only [mul_inv_rev, mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using
      C.inv_mem (C.zpow_mem hzC n)
  have hcmp (n : ℤ) : R.action g R.base < R.action h (R.action (z ^ n) R.base) := by
    have hh : (QuotientGroup.mk g : G ⧸ C) < QuotientGroup.mk (h * z ^ n) := by
      rw [hrep]
      exact hgh
    have hi := (realization_lt_iff O R g (h * z ^ n)).mp (order_lt_of_coset_lt O C hC hh)
    simpa only [map_mul, RelIso.mul_apply] using hi
  have hle : (R.action h)⁻¹ (R.action g R.base) ≤ lowerEndpoint R z := by
    apply le_csInf (Set.range_nonempty _)
    rintro _ ⟨n, rfl⟩
    simpa only [RelIso.inv_apply_self] using ((R.action h)⁻¹).monotone (hcmp n).le
  have hle' : R.action g R.base ≤ R.action h (lowerEndpoint R z) := by
    simpa only [RelIso.apply_inv_self] using (R.action h).monotone hle
  exact ((R.action g).strictMono (lowerEndpoint_lt_base R z hb hz)).trans_le hle'

/-- Centrality makes every point of the endpoint orbit central-fixed. -/
theorem endpoint_orbit_fixed {O : LeftGroupOrder G} (R : TightRealization O) (z : G)
    (hcentral : ∀ g : G, Commute z g)
    (hb : BddBelow (Set.range (fun n : ℤ => R.action (z ^ n) R.base))) (g : G) :
    R.action z (R.action g (lowerEndpoint R z)) = R.action g (lowerEndpoint R z) := by
  have hc := (hcentral g).map R.action
  have he := congrArg (fun e : ℝ ≃o ℝ => e (lowerEndpoint R z)) hc.eq
  simpa only [RelIso.mul_apply, lowerEndpoint_fixed R z hb] using he

/-- The coset crossing can be realized entirely on the central fixed-point set. -/
theorem crossing_on_fixed_orbit (O : LeftGroupOrder G) (C : Subgroup G)
    (hC : letI := O.order; Set.OrdConnected (C : Set G)) (R : TightRealization O)
    (z : G) (hzC : z ∈ C) (hcentral : ∀ g : G, Commute z g)
    (hb : BddBelow (Set.range (fun n : ℤ => R.action (z ^ n) R.base)))
    (hz : R.action z R.base ≠ R.base) {f g : G} {u v w : G ⧸ C}
    (hc : letI := cosetLinearOrder O C hC
      Crossing (cosetAction O C hC f) (cosetAction O C hC g) u v w) :
    ∃ u' v' w' : ℝ, Crossing (R.action f) (R.action g) u' v' w' ∧
      R.action z u' = u' ∧ R.action z v' = v' ∧ R.action z w' = w' := by
  let := cosetLinearOrder O C hC
  let l := lowerEndpoint R z
  have hlift {a b : G} (hab : (QuotientGroup.mk a : G ⧸ C) < QuotientGroup.mk b) :
      R.action a l < R.action b l := coset_lt_endpoint_orbit O C hC R z hzC hb hz hab
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective u
  obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective v
  obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective w
  refine ⟨R.action u l, R.action v l, R.action w l, ?_,
    endpoint_orbit_fixed R z hcentral hb u, endpoint_orbit_fixed R z hcentral hb v,
    endpoint_orbit_fixed R z hcentral hb w⟩
  refine ⟨hlift hc.left_lt_middle, hlift hc.middle_lt_right, ?_, ?_, ?_⟩
  · intro n
    have hn : (QuotientGroup.mk (g ^ n * u) : G ⧸ C) < QuotientGroup.mk v := by
      simpa only [← map_pow, cosetAction_mk] using hc.left_bounded n
    simpa only [map_mul, map_pow, RelIso.mul_apply] using hlift hn
  · intro n
    have hn : (QuotientGroup.mk u : G ⧸ C) < QuotientGroup.mk (f ^ n * v) := by
      simpa only [← map_pow, cosetAction_mk] using hc.right_bounded n
    simpa only [map_mul, map_pow, RelIso.mul_apply] using hlift hn
  · obtain ⟨N, M, hN, hM⟩ := hc.crosses
    have hN' : (QuotientGroup.mk (f ^ N * v) : G ⧸ C) < QuotientGroup.mk w := by
      simpa only [← map_pow, cosetAction_mk] using hN
    have hM' : (QuotientGroup.mk w : G ⧸ C) < QuotientGroup.mk (g ^ M * u) := by
      simpa only [← map_pow, cosetAction_mk] using hM
    exact ⟨N, M, by simpa only [map_mul, map_pow, RelIso.mul_apply] using hlift hN',
      by simpa only [map_mul, map_pow, RelIso.mul_apply] using hlift hM'⟩

/-- A commuting map fixing an orbit point also fixes the finite lower limit
of that entire integer orbit. -/
theorem fixed_sInf_orbit_of_commute (f q : ℝ ≃o ℝ) {x : ℝ}
    (hc : Commute f q) (hx : q x = x)
    (hb : BddBelow (Set.range (fun n : ℤ => (f ^ n) x))) :
    q (sInf (Set.range (fun n : ℤ => (f ^ n) x))) =
      sInf (Set.range (fun n : ℤ => (f ^ n) x)) := by
  have hfix (n : ℤ) : q ((f ^ n) x) = (f ^ n) x := by
    have he := congrArg (fun e : ℝ ≃o ℝ => e x) (hc.zpow_left n).eq
    simpa only [RelIso.mul_apply, hx] using he.symm
  rw [q.map_csInf' (Set.range_nonempty _) hb]
  congr 1
  ext y
  constructor
  · rintro ⟨_, ⟨n, rfl⟩, rfl⟩
    exact ⟨n, (hfix n).symm⟩
  · rintro ⟨n, rfl⟩
    exact ⟨(f ^ n) x, ⟨n, rfl⟩, hfix n⟩

/-- The lower endpoint extracted from a crossing is central-fixed when its
right orbit point is central-fixed. -/
theorem crossing_lower_fixed_endpoint {f g q : ℝ ≃o ℝ} {u v w : ℝ}
    (hc : Crossing f g u v w) (hcomm : Commute f q) (hv : q v = v) :
    ∃ l : ℝ, u ≤ l ∧ l < v ∧ f l = l ∧ q l = l ∧ f v < v ∧
      ∀ x : ℝ, l < x → x ≤ v → f x ≠ x := by
  obtain ⟨l, hul, hlv, hfl, hfv, hnofix⟩ :=
    NoncofinalRayPerturbation.crossing_lower_fixed_endpoint hc
  let S := Set.range (fun n : ℤ => (f ^ n) v)
  have hb : BddBelow S := by
    refine ⟨l, ?_⟩
    rintro _ ⟨n, rfl⟩
    simpa only [NoncofinalCrossings.fixed_zpow f hfl] using (f ^ n).monotone hlv.le
  have hli : l ≤ sInf S := by
    apply le_csInf (Set.range_nonempty _)
    rintro _ ⟨n, rfl⟩
    simpa only [NoncofinalCrossings.fixed_zpow f hfl] using (f ^ n).monotone hlv.le
  have hiv : sInf S ≤ v := csInf_le hb ⟨0, by simp⟩
  have hfi : f (sInf S) = sInf S :=
    NoncofinalDynamics.orbit_sInf_fixed (MonoidHom.id _) f v hb
  have hil : sInf S ≤ l := le_of_not_gt (fun h => hnofix _ h hiv hfi)
  have he : sInf S = l := le_antisymm hil hli
  have hql := fixed_sInf_orbit_of_commute f q hcomm hv hb
  rw [he] at hql
  exact ⟨l, hul, hlv, hfl, hql, hfv, hnofix⟩

/-- A commuting map fixing one point of a nonfixed component preserves the
whole component, giving exactly the invariant-set input for truncation. -/
theorem component_invariant_of_commute (f q : ℝ ≃o ℝ) (hcomm : Commute f q)
    {t : ℝ} (ht : f t ≠ t) (hqt : q t = t) :
    ∀ x : ℝ, x ∈ connectedComponentIn {y : ℝ | f y ≠ y} t ↔
      q x ∈ connectedComponentIn {y : ℝ | f y ≠ y} t := by
  have hiff (x : ℝ) : f (q x) ≠ q x ↔ f x ≠ x := by
    have he := congrArg (fun e : ℝ ≃o ℝ => e x) hcomm.eq
    change f (q x) = q (f x) at he
    rw [he, q.injective.ne_iff]
  have himg : q '' {y : ℝ | f y ≠ y} = {y : ℝ | f y ≠ y} := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hiff x).mpr hx
    · intro hy
      change f y ≠ y at hy
      refine ⟨q⁻¹ y, ?_, RelIso.apply_inv_self q y⟩
      exact (hiff (q⁻¹ y)).mp (by simpa only [RelIso.apply_inv_self] using hy)
  have he := q.toHomeomorph.image_connectedComponentIn
    (s := {y : ℝ | f y ≠ y}) (x := t) ht
  change q '' connectedComponentIn {y : ℝ | f y ≠ y} t =
    connectedComponentIn (q '' {y : ℝ | f y ≠ y}) (q t) at he
  rw [himg, hqt] at he
  intro x
  constructor
  · intro hx
    rw [← he]
    exact ⟨x, hx, rfl⟩
  · intro hx
    rw [← he] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    exact q.injective hyx ▸ hy

/-- A crossing on the central fixed-point set produces, beyond every bound,
a nonfixed component invariant under the center. Its finite lower endpoint
is fixed by both the chosen element and the center. -/
theorem central_invariant_component_above (ρ : G →* (ℝ ≃o ℝ))
    (z : G) (hcentral : ∀ g : G, Commute z g)
    (hglobal : ∀ x : ℝ, ∃ g : G, ρ g x ≠ x)
    {f g : G} {u v w : ℝ} (hc : Crossing (ρ f) (ρ g) u v w)
    (hv : ρ z v = v) (p : ℝ) :
    ∃ a : G, ∃ l t : ℝ, p < l ∧ l < t ∧ ρ a l = l ∧ ρ z l = l ∧
      ρ a t < t ∧ ρ z t = t ∧
      Set.Ioc l t ⊆ connectedComponentIn {x : ℝ | ρ a x ≠ x} t ∧
      connectedComponentIn {x : ℝ | ρ a x ≠ x} t ⊆ Set.Ioi l ∧
      ∀ x : ℝ, x ∈ connectedComponentIn {y : ℝ | ρ a y ≠ y} t ↔
        ρ z x ∈ connectedComponentIn {y : ℝ | ρ a y ≠ y} t := by
  obtain ⟨l, hul, hlv, hfl, hzl, hfv, hfix⟩ :=
    crossing_lower_fixed_endpoint hc ((hcentral f).symm.map ρ) hv
  obtain ⟨h, hhp⟩ := NoncofinalEnvelope.orbit_unbounded_above ρ hglobal l p
  let a := h * f * h⁻¹
  have hal : ρ a (ρ h l) = ρ h l := by
    simp only [a, map_mul, map_inv, RelIso.mul_apply, RelIso.inv_apply_self, hfl]
  have hat : ρ a (ρ h v) < ρ h v := by
    simpa only [a, map_mul, map_inv, RelIso.mul_apply, RelIso.inv_apply_self] using
      (ρ h).strictMono hfv
  have hzfix {x : ℝ} (hx : ρ z x = x) : ρ z (ρ h x) = ρ h x := by
    have he := congrArg (fun e : ℝ ≃o ℝ => e x) ((hcentral h).map ρ).eq
    simpa only [RelIso.mul_apply, hx] using he
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
  refine ⟨a, ρ h l, ρ h v, hhp, hlt, hal, hzfix hzl, hat, hzfix hv, hsub, ?_, ?_⟩
  · intro x hx
    have hv' : ρ h v ∈ connectedComponentIn {x : ℝ | ρ a x ≠ x} (ρ h v) :=
      mem_connectedComponentIn hat.ne
    have hconn := (isPreconnected_connectedComponentIn
      (F := {x : ℝ | ρ a x ≠ x}) (x := ρ h v)).ordConnected
    by_contra hn
    have hl := hconn.out hx hv' ⟨le_of_not_gt hn, hlt.le⟩
    exact (connectedComponentIn_subset _ _ hl) hal
  · exact component_invariant_of_commute (ρ a) (ρ z) ((hcentral a).symm.map ρ) hat.ne (hzfix hv)

/-- Noncofinality supplies the finite lower bound needed by the endpoint
construction, for every tight realization and either sign of the center. -/
theorem central_orbit_bddBelow (O : LeftGroupOrder G) (R : TightRealization O)
    (z : G) (hcentral : ∀ g : G, Commute z g) (hnon : ¬ O.IsCofinal z) :
    BddBelow (Set.range (fun n : ℤ => R.action (z ^ n) R.base)) := by
  have hfix := NoncofinalDynamics.exists_fixed_of_not_cofinal R.action O z R.base R.order_iff hnon
  have hnb := NoncofinalDynamics.central_fixedPoints_not_bddBelow
    R.action z hcentral hfix R.no_global_fixed
  obtain ⟨l, hl, hlb⟩ := (not_bddBelow_iff.mp hnb) R.base
  refine ⟨l, ?_⟩
  rintro _ ⟨n, rfl⟩
  simpa only [NoncofinalDynamics.fixed_zpow R.action z hl] using
    (R.action (z ^ n)).monotone hlb.le

/-- The endpoint and central-invariance hypotheses are all discharged from an
actual noncofinal central element and a coset crossing. -/
theorem central_component_above_of_coset_crossing (O : LeftGroupOrder G) (C : Subgroup G)
    (hC : letI := O.order; Set.OrdConnected (C : Set G)) (R : TightRealization O)
    (z : G) (hzC : z ∈ C) (hcentral : ∀ g : G, Commute z g) (hz : z ≠ 1)
    (hnon : ¬ O.IsCofinal z) {f g : G} {u v w : G ⧸ C}
    (hc : letI := cosetLinearOrder O C hC
      Crossing (cosetAction O C hC f) (cosetAction O C hC g) u v w) (p : ℝ) :
    ∃ a : G, ∃ l t : ℝ, p < l ∧ l < t ∧ R.action a l = l ∧ R.action z l = l ∧
      R.action a t < t ∧ R.action z t = t ∧
      Set.Ioc l t ⊆ connectedComponentIn {x : ℝ | R.action a x ≠ x} t ∧
      connectedComponentIn {x : ℝ | R.action a x ≠ x} t ⊆ Set.Ioi l ∧
      ∀ x : ℝ, x ∈ connectedComponentIn {y : ℝ | R.action a y ≠ y} t ↔
        R.action z x ∈ connectedComponentIn {y : ℝ | R.action a y ≠ y} t := by
  have hzb : R.action z R.base ≠ R.base := by
    intro h
    apply hz
    apply R.orbit_injective
    simpa only [map_one, RelIso.one_apply] using h
  obtain ⟨u', v', w', hc', hu', hv', hw'⟩ := crossing_on_fixed_orbit O C hC R z hzC hcentral
    (central_orbit_bddBelow O R z hcentral hnon) hzb hc
  exact central_invariant_component_above R.action z hcentral R.no_global_fixed hc' hv' p

/-- For the actual noncofinal finitely generated cone, the restricted convex
jump has centrally invariant moving components arbitrarily far to the right.
All group, order, finite-generation, and central endpoint inputs are proved. -/
theorem exists_restricted_central_components {ι : Type u} [Nontrivial ι]
    (P : PositiveCone (FreeGroup ι × Multiplicative ℤ)) (hfg : SemigroupFG P.1)
    (hnon : ¬ (coneLeftOrder P).IsCofinal (cofinalProductZ (FreeGroup ι))) :
    ∃ H : Subgroup (FreeGroup ι × Multiplicative ℤ), ConeConvex P H ∧
      ∃ hCH : boundedSubgroup P < H,
      let z := NoncofinalFreeTower.centerIn H (hCH.le
        (NoncofinalSubgroupProduct.central_mem_bounded (coneLeftOrder P)))
      ∀ R : TightRealization ((coneLeftOrder P).restrictSubgroup H), ∀ p : ℝ,
        ∃ a : H, ∃ l t : ℝ, p < l ∧ l < t ∧ R.action a l = l ∧ R.action z l = l ∧
          R.action a t < t ∧ R.action z t = t ∧
          Set.Ioc l t ⊆ connectedComponentIn {x : ℝ | R.action a x ≠ x} t ∧
          connectedComponentIn {x : ℝ | R.action a x ≠ x} t ⊆ Set.Ioi l ∧
          ∀ x : ℝ, x ∈ connectedComponentIn {y : ℝ | R.action a y ≠ y} t ↔
            R.action z x ∈ connectedComponentIn {y : ℝ | R.action a y ≠ y} t := by
  obtain ⟨H, hH, hCH, hmax, f, g, u, v, w, hc⟩ := exists_convex_jump_crossing P hfg hnon
  refine ⟨H, hH, hCH, ?_⟩
  dsimp only
  intro R p
  let hzH := hCH.le (NoncofinalSubgroupProduct.central_mem_bounded (coneLeftOrder P))
  let z := NoncofinalFreeTower.centerIn H hzH
  have hz : z ≠ 1 := by
    intro he
    have h := congrArg (fun x : H => ((x : FreeGroup ι × Multiplicative ℤ).2).toAdd) he
    change (1 : ℤ) = 0 at h
    exact Int.one_ne_zero h
  exact central_component_above_of_coset_crossing ((coneLeftOrder P).restrictSubgroup H)
    ((boundedSubgroup P).subgroupOf H) (restrictedBoundedConvex P H) R z
    (NoncofinalSubgroupProduct.central_mem_bounded (coneLeftOrder P))
    (NoncofinalFreeTower.centerIn_central H hzH) hz
    (NoncofinalFreeTower.restricted_not_cofinal (coneLeftOrder P) H hzH hCH) hc p

end FnZPositiveCones.NoncofinalFixedCrossing
