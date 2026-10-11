module

public import FnZPositiveCones.External.NoncofinalFlexibleComponents
public import FnZPositiveCones.External.NoncofinalPrimitiveTranslate
public import FnZPositiveCones.External.OrderedActionsFactorFibers

@[expose] public section

/-!
# Finite-trace adapters for the noncofinal isolation argument

These results do not infer finite generation from isolation. In the
fixed-point-free primitive case, one primitive basis is chosen before the
finite trajectory bound. Powers of that same primitive then move its entering
component beyond the bound. Thus the protected tests refer to the original
marking, and no bound uniform over all changes of basis is needed.
-/

namespace FnZPositiveCones.NoncofinalIsolationAdapter

open NoncofinalPrimitiveEntry NoncofinalComponentPerturbation

universe u
variable {G : Type u} [Group G] {ι : Type u}

/-- Pull a left order back along an explicitly invertible change of marking. -/
noncomputable def reindexOrder (O : LeftGroupOrder G) (e : G ≃* G) :
    LeftGroupOrder G := by
  letI := O.order
  exact ⟨LinearOrder.lift' e e.injective, fun g h k hgh => by
    change O.order.le (e (k * g)) (e (k * h))
    simpa only [map_mul] using O.mul_le_mul_left (e g) (e h) (e k) hgh⟩

@[simp] theorem reindexOrder_le (O : LeftGroupOrder G) (e : G ≃* G) (g h : G) :
    (reindexOrder O e).order.le g h ↔ O.order.le (e g) (e h) := Iff.rfl

@[simp] theorem reindexOrder_lt (O : LeftGroupOrder G) (e : G ≃* G) (g h : G) :
    (reindexOrder O e).order.lt g h ↔ O.order.lt (e g) (e h) := Iff.rfl

/-- For a product action without a global fixed point, a fixed point of one
primitive has conjugate fixed points arbitrarily far to the right. Therefore
the no-far-fixed-point alternative makes every primitive fixed-point-free. -/
theorem primitive_no_fixed_of_no_fixed_above
    (ρ : (FreeGroup ι × Multiplicative ℤ) →* (ℝ ≃o ℝ))
    (hglobal : ∀ x : ℝ, ∃ g, ρ g x ≠ x) (b : ℝ)
    (hfar : ∀ a : FreeGroup ι, IsPrimitive a → ∀ x : ℝ, b < x → ρ (a, 1) x ≠ x) :
    ∀ a : FreeGroup ι, IsPrimitive a → ∀ x : ℝ, ρ (a, 1) x ≠ x := by
  intro a ha x hx
  obtain ⟨g, hg⟩ := NoncofinalEnvelope.orbit_unbounded_above ρ hglobal x b
  have he : g * (a, 1) * g⁻¹ = (g.1 * a * g.1⁻¹, (1 : Multiplicative ℤ)) := by
    ext <;> simp
  have hfix : ρ (g.1 * a * g.1⁻¹, 1) (ρ g x) = ρ g x := by
    rw [← he]
    simp only [map_mul, map_inv, RelIso.mul_apply, RelIso.inv_apply_self, hx]
  exact hfar _ (primitive_conj ha g.1) _ hg hfix

/-- Primitive entry in a minimal monotone factor lifts to entry in an
upstairs interval whenever its endpoints have different factor images.
That last condition is explicit: a collapsed interval cannot be entered by
this argument. -/
theorem exists_primitive_entry_of_factor [Nontrivial ι]
    (ρ σ : (FreeGroup ι × Multiplicative ℤ) →* (ℝ ≃o ℝ)) (p : ℝ → ℝ)
    (hm : Monotone p) (hc : Continuous p) (hs : Function.Surjective p)
    (he : ∀ g x, p (ρ g x) = σ g (p x))
    (hz : σ (cofinalProductZ (FreeGroup ι)) = 1)
    (hminimal : ∀ x : ℝ, DenseRange (fun g => σ g x))
    (hn : ∀ a : FreeGroup ι, IsPrimitive a → ∀ x : ℝ, ρ (a, 1) x ≠ x)
    {l t : ℝ} (hlt : p l < p t) :
    ∃ a : FreeGroup ι, IsPrimitive a ∧ ρ (a, 1) l ∈ Set.Ioo l t := by
  let σ₀ := σ.comp (MonoidHom.inl (FreeGroup ι) (Multiplicative ℤ))
  have hmin : ∀ x : ℝ, DenseRange (fun g => σ₀ g x) :=
    OrderedActions.free_factor_minimal σ hz hminimal
  have hno := OrderedActions.primitive_no_fixed_factor ρ σ p hm hc hs he hn
  obtain ⟨a, ha, hlo, hhi⟩ := exists_primitive_entry σ₀ hmin hno hlt
  change p l < σ (a, 1) (p l) at hlo
  change σ (a, 1) (p l) < p t at hhi
  rw [← he] at hlo hhi
  refine ⟨a, ha, ?_, ?_⟩
  · exact lt_of_not_ge (fun h => hlo.not_ge (hm h))
  · exact lt_of_not_ge (fun h => hhi.not_ge (hm h))

/-- A single primitive entry suffices for perturbations preserving any
finite set of original orbit tests. The entering primitive and its basis
are fixed before the trajectory bound is computed. -/
theorem exists_finite_trace_perturbation_of_primitive_entry [Nontrivial ι]
    (O : LeftGroupOrder (FreeGroup ι × Multiplicative ℤ))
    (ρ : (FreeGroup ι × Multiplicative ℤ) →* (ℝ ≃o ℝ)) (x : ℝ)
    (hreal : ∀ g h, O.order.le g h ↔ ρ g x ≤ ρ h x)
    (hglobal : ∀ y : ℝ, ∃ g, ρ g y ≠ y)
    (hx : ρ (cofinalProductZ (FreeGroup ι)) x ≠ x)
    (hn : ∀ a : FreeGroup ι, IsPrimitive a → ∀ y : ℝ, ρ (a, 1) y ≠ y)
    (f : ℝ ≃o ℝ) (l t : ℝ) (ht : f t ≠ t) (hlt : l < t)
    (hleft : Set.Ioc l t ⊆ motionComponent f t)
    (hlower : motionComponent f t ⊆ Set.Ioi l)
    (a : FreeGroup ι) (ha : IsPrimitive a) (hentry : ρ (a, 1) l ∈ motionComponent f t)
    (hfq : Commute f (ρ (cofinalProductZ (FreeGroup ι))))
    (hqJ : ∀ y : ℝ, y ∈ motionComponent f t ↔
      ρ (cofinalProductZ (FreeGroup ι)) y ∈ motionComponent f t)
    (hql : ρ (cofinalProductZ (FreeGroup ι)) l = l)
    (F : Finset (FreeGroup ι × Multiplicative ℤ)) :
    ∃ τ : (FreeGroup ι × Multiplicative ℤ) →* (ℝ ≃o ℝ),
      O.actionCompletion τ x ≠ O ∧ (∀ g ∈ F, τ g x = ρ g x) ∧
      ∀ g ∈ F, (g ∈ (leftOrderCone (O.actionCompletion τ x)).1 ↔
        g ∈ (leftOrderCone O).1) := by
  classical
  obtain ⟨e, i, rfl⟩ := ha
  let E := productBasis e
  let O' := reindexOrder O E
  let ρ' := ρ.comp E.toMonoidHom
  have hreal' : ∀ g h, O'.order.le g h ↔ ρ' g x ≤ ρ' h x := by
    intro g h
    exact hreal (E g) (E h)
  have hglobal' : ∀ y : ℝ, ∃ g, ρ' g y ≠ y := by
    intro y
    obtain ⟨g, hg⟩ := hglobal y
    exact ⟨E.symm g, by simpa [ρ'] using hg⟩
  have hcenter : ρ' (cofinalProductZ (FreeGroup ι)) = ρ (cofinalProductZ (FreeGroup ι)) := by
    simp [ρ', E, cofinalProductZ]
  have hx' : ρ' (cofinalProductZ (FreeGroup ι)) x ≠ x := by rwa [hcenter]
  obtain ⟨B, hB⟩ := NoncofinalFlexibleComponents.exists_component_deformation_bound
    O' ρ' x hreal' hglobal' hx' (F.image E.symm) 0 i
  obtain ⟨j, hji⟩ := exists_ne i
  have hother : ∀ y : ℝ, 0 < y → ρ' (FreeGroup.of j, 1) y ≠ y := by
    intro y _
    exact hn _ ⟨e, j, rfl⟩ y
  have haq : Commute (ρ (e (FreeGroup.of i), 1)) (ρ (cofinalProductZ (FreeGroup ι))) :=
    ((cofinalProductZ_central (e (FreeGroup.of i), 1)).symm).map ρ
  obtain ⟨k, hk, ht', hlt', hleft', hlower', hentry', hfq', hqJ', hql'⟩ :=
    NoncofinalPrimitiveTranslate.exists_component_entry_above f
      (ρ (e (FreeGroup.of i), 1)) (ρ (cofinalProductZ (FreeGroup ι))) l t ht hlt
      hleft hlower hentry (hn _ ⟨e, i, rfl⟩) haq hfq hqJ hql B
  let d := ρ (e (FreeGroup.of i), 1) ^ k
  obtain ⟨τ, hτ, hagree, _⟩ := hB j hji hother (d * f * d⁻¹) (d l) (d t) ht'
    hk hlt' hleft' hlower' hentry' (by rwa [hcenter])
    (by simpa only [hcenter] using hqJ') (by simpa only [hcenter] using hql')
  let τ₀ := τ.comp E.symm.toMonoidHom
  have hneq : O.actionCompletion τ₀ x ≠ O := by
    intro heq
    apply hτ
    apply LeftGroupOrder.ext_order
    apply LinearOrder.ext_lt
    intro g h
    have heq' := congrArg (fun Q : LeftGroupOrder (FreeGroup ι × Multiplicative ℤ) =>
      Q.order.lt (E g) (E h)) heq
    simpa only [LeftGroupOrder.actionCompletion_lt, τ₀, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply, O', reindexOrder_lt] using iff_of_eq heq'
  have hagree₀ : ∀ g ∈ F, τ₀ g x = ρ g x := by
    intro g hg
    have hh := hagree (E.symm g) (Finset.mem_image.mpr ⟨g, hg, rfl⟩)
    simpa [τ₀, ρ'] using hh
  exact ⟨τ₀, hneq, hagree₀, O.actionCompletion_signs ρ τ₀ x hreal F hagree₀⟩

/-- Strict inequalities in a monotone factor lift even when its fibers are
nontrivial. Consequently a crossing lifts using any three chosen preimages. -/
theorem crossing_of_factor
    (ρ σ : G →* (ℝ ≃o ℝ)) (p : ℝ → ℝ) (hm : Monotone p)
    (he : ∀ g x, p (ρ g x) = σ g (p x))
    {f g : G} {u v w u' v' w' : ℝ}
    (hcross : NoncofinalCrossings.Crossing (σ f) (σ g) u v w)
    (hu : p u' = u) (hv : p v' = v) (hw : p w' = w) :
    NoncofinalCrossings.Crossing (ρ f) (ρ g) u' v' w' := by
  have hlt {x y : ℝ} (h : p x < p y) : x < y :=
    lt_of_not_ge (fun hle => h.not_ge (hm hle))
  have hep (a : G) (n : ℕ) (y : ℝ) : p ((ρ a ^ n) y) = (σ a ^ n) (p y) := by
    rw [← map_pow, he, map_pow]
  refine ⟨hlt (by simpa only [hu, hw] using hcross.left_lt_middle),
    hlt (by simpa only [hw, hv] using hcross.middle_lt_right), ?_, ?_, ?_⟩
  · intro n
    apply hlt
    simpa only [hep, hu, hv] using hcross.left_bounded n
  · intro n
    apply hlt
    simpa only [hep, hu, hv] using hcross.right_bounded n
  · obtain ⟨N, M, hN, hM⟩ := hcross.crosses
    exact ⟨N, M,
      hlt (by simpa only [hep, hv, hw] using hN),
      hlt (by simpa only [hep, hu, hw] using hM)⟩

/-- A crossing in a factor on which the center acts trivially supplies the
actual invariant component upstairs, and that component is not collapsed
by the factor. The central fixed point is obtained from its compact fiber. -/
theorem exists_component_of_factor_crossing
    (ρ σ : G →* (ℝ ≃o ℝ)) (p : ℝ → ℝ)
    (hm : Monotone p) (hc : Continuous p) (hs : Function.Surjective p)
    (he : ∀ g x, p (ρ g x) = σ g (p x))
    (z : G) (hcentral : ∀ g : G, Commute z g) (hz : σ z = 1)
    {f g : G} {u v w : ℝ}
    (hcross : NoncofinalCrossings.Crossing (σ f) (σ g) u v w) :
    ∃ l t : ℝ, l < t ∧ p l < p t ∧ ρ f l = l ∧ ρ z l = l ∧
      ρ f t < t ∧ ρ z t = t ∧
      Set.Ioc l t ⊆ motionComponent (ρ f) t ∧
      motionComponent (ρ f) t ⊆ Set.Ioi l ∧
      ∀ y : ℝ, y ∈ motionComponent (ρ f) t ↔ ρ z y ∈ motionComponent (ρ f) t := by
  obtain ⟨u', hu⟩ := hs u
  obtain ⟨w', hw⟩ := hs w
  obtain ⟨v', hv, hzv⟩ := OrderedActions.lift_fixedPoint_of_factor ρ σ p hm hc hs he
    z v (by simp only [hz, RelIso.one_apply])
  have hcross' := crossing_of_factor ρ σ p hm he hcross hu hv hw
  have hcomm : Commute (ρ f) (ρ z) := ((hcentral f).symm).map ρ
  obtain ⟨l, _, hlv, hfl, hzl, hfv, hnofix⟩ :=
    NoncofinalFixedCrossing.crossing_lower_fixed_endpoint hcross' hcomm hzv
  have hsub : Set.Ioc l v' ⊆ motionComponent (ρ f) v' :=
    isPreconnected_Ioc.subset_connectedComponentIn ⟨hlv, le_rfl⟩
      (fun y hy => hnofix y hy.1 hy.2)
  have hpl : p l < p v' := by
    apply lt_of_le_of_ne (hm hlv.le)
    intro hpeq
    have hfix : σ f v = v := by
      have hh := he f l
      rw [hfl, hpeq, hv] at hh
      exact hh.symm
    obtain ⟨_, _, _, _, hdown, _⟩ :=
      NoncofinalRayPerturbation.crossing_lower_fixed_endpoint hcross
    exact hdown.ne hfix
  refine ⟨l, v', hlv, hpl, hfl, hzl, hfv, hzv, hsub, ?_, ?_⟩
  · intro y hy
    by_contra hn
    have hv' : v' ∈ motionComponent (ρ f) v' := mem_connectedComponentIn hfv.ne
    have hl := (motionComponent_ordConnected (ρ f) v').out hy hv'
      ⟨le_of_not_gt hn, hlv.le⟩
    exact (connectedComponentIn_subset _ _ hl) hfl
  · exact NoncofinalFixedCrossing.component_invariant_of_commute (ρ f) (ρ z)
      hcomm hfv.ne hzv

/-- The second alternative in MMRT Claim 4 produces a genuine finite-trace
perturbation. Minimality and the crossing belong to the factor; the original
realization need not be minimal. No primitive-entry hypothesis remains. -/
theorem exists_finite_trace_perturbation_of_factor_crossing [Nontrivial ι]
    (O : LeftGroupOrder (FreeGroup ι × Multiplicative ℤ))
    (ρ σ : (FreeGroup ι × Multiplicative ℤ) →* (ℝ ≃o ℝ)) (x : ℝ)
    (hreal : ∀ g h, O.order.le g h ↔ ρ g x ≤ ρ h x)
    (hglobal : ∀ y : ℝ, ∃ g, ρ g y ≠ y)
    (hx : ρ (cofinalProductZ (FreeGroup ι)) x ≠ x)
    (p : ℝ → ℝ) (hm : Monotone p) (hc : Continuous p) (hs : Function.Surjective p)
    (he : ∀ g y, p (ρ g y) = σ g (p y))
    (hz : σ (cofinalProductZ (FreeGroup ι)) = 1)
    (hminimal : ∀ y : ℝ, DenseRange (fun g => σ g y))
    {f g : FreeGroup ι × Multiplicative ℤ} {u v w : ℝ}
    (hcross : NoncofinalCrossings.Crossing (σ f) (σ g) u v w)
    (b : ℝ)
    (hfar : ∀ a : FreeGroup ι, IsPrimitive a → ∀ y : ℝ, b < y → ρ (a, 1) y ≠ y)
    (F : Finset (FreeGroup ι × Multiplicative ℤ)) :
    ∃ τ : (FreeGroup ι × Multiplicative ℤ) →* (ℝ ≃o ℝ),
      O.actionCompletion τ x ≠ O ∧ (∀ g ∈ F, τ g x = ρ g x) ∧
      ∀ g ∈ F, (g ∈ (leftOrderCone (O.actionCompletion τ x)).1 ↔
        g ∈ (leftOrderCone O).1) := by
  have hn := primitive_no_fixed_of_no_fixed_above ρ hglobal b hfar
  obtain ⟨l, t, hlt, hpt, _, hql, hft, _, hleft, hlower, hqJ⟩ :=
    exists_component_of_factor_crossing ρ σ p hm hc hs he
      (cofinalProductZ (FreeGroup ι)) cofinalProductZ_central hz hcross
  obtain ⟨a, ha, hentry⟩ := exists_primitive_entry_of_factor ρ σ p hm hc hs he
    hz hminimal hn hpt
  exact exists_finite_trace_perturbation_of_primitive_entry O ρ x hreal hglobal hx hn
    (ρ f) l t hft.ne hlt hleft hlower a ha (hleft ⟨hentry.1, hentry.2.le⟩)
    ((cofinalProductZ_central f).symm.map ρ) hqJ hql F

/-- The finite-trace perturbation contradicts isolation directly, using a
finite determining set of signs rather than semigroup generation. -/
theorem not_isolated_of_factor_crossing_no_far_primitive_fixed [Nontrivial ι]
    (O : LeftGroupOrder (FreeGroup ι × Multiplicative ℤ))
    (ρ σ : (FreeGroup ι × Multiplicative ℤ) →* (ℝ ≃o ℝ)) (x : ℝ)
    (hreal : ∀ g h, O.order.le g h ↔ ρ g x ≤ ρ h x)
    (hglobal : ∀ y : ℝ, ∃ g, ρ g y ≠ y)
    (hx : ρ (cofinalProductZ (FreeGroup ι)) x ≠ x)
    (p : ℝ → ℝ) (hm : Monotone p) (hc : Continuous p) (hs : Function.Surjective p)
    (he : ∀ g y, p (ρ g y) = σ g (p y))
    (hz : σ (cofinalProductZ (FreeGroup ι)) = 1)
    (hminimal : ∀ y : ℝ, DenseRange (fun g => σ g y))
    {f g : FreeGroup ι × Multiplicative ℤ} {u v w : ℝ}
    (hcross : NoncofinalCrossings.Crossing (σ f) (σ g) u v w)
    (b : ℝ)
    (hfar : ∀ a : FreeGroup ι, IsPrimitive a → ∀ y : ℝ, b < y → ρ (a, 1) y ≠ y) :
    ¬ IsOpen ({O} : Set (LeftGroupOrder (FreeGroup ι × Multiplicative ℤ))) := by
  intro hiso
  have hfd : FinitelyDetermined (leftOrderCone O).1 :=
    (finiteDetermination_iff_leftOrder_isolated (leftOrderCone O)).mpr (by simpa using hiso)
  obtain ⟨F, hFP, hdet⟩ := hfd
  obtain ⟨τ, hneq, _, hsign⟩ := exists_finite_trace_perturbation_of_factor_crossing
    O ρ σ x hreal hglobal hx p hm hc hs he hz hminimal hcross b hfar F
  apply hneq
  have hcone : leftOrderCone (O.actionCompletion τ x) = leftOrderCone O :=
    Subtype.ext (hdet _ (leftOrderCone (O.actionCompletion τ x)).2
      (fun g hg => (hsign g hg).mpr (hFP hg)))
  simpa using congrArg coneLeftOrder hcone

/-- Under the checked factor hypotheses, isolation forces the first
alternative of MMRT Claim 4. The primitive may depend on the bound; the
statement deliberately does not assert a fixed marking works for all bounds. -/
theorem isolated_factor_crossing_primitive_fixed_above [Nontrivial ι]
    (O : LeftGroupOrder (FreeGroup ι × Multiplicative ℤ))
    (ρ σ : (FreeGroup ι × Multiplicative ℤ) →* (ℝ ≃o ℝ)) (x : ℝ)
    (hreal : ∀ g h, O.order.le g h ↔ ρ g x ≤ ρ h x)
    (hglobal : ∀ y : ℝ, ∃ g, ρ g y ≠ y)
    (hx : ρ (cofinalProductZ (FreeGroup ι)) x ≠ x)
    (p : ℝ → ℝ) (hm : Monotone p) (hc : Continuous p) (hs : Function.Surjective p)
    (he : ∀ g y, p (ρ g y) = σ g (p y))
    (hz : σ (cofinalProductZ (FreeGroup ι)) = 1)
    (hminimal : ∀ y : ℝ, DenseRange (fun g => σ g y))
    {f g : FreeGroup ι × Multiplicative ℤ} {u v w : ℝ}
    (hcross : NoncofinalCrossings.Crossing (σ f) (σ g) u v w)
    (hiso : IsOpen ({O} : Set (LeftGroupOrder (FreeGroup ι × Multiplicative ℤ))))
    (b : ℝ) :
    ∃ a : FreeGroup ι, IsPrimitive a ∧ ∃ y : ℝ, b < y ∧ ρ (a, 1) y = y := by
  by_contra! h
  exact not_isolated_of_factor_crossing_no_far_primitive_fixed O ρ σ x hreal hglobal hx
    p hm hc hs he hz hminimal hcross b h hiso

end FnZPositiveCones.NoncofinalIsolationAdapter
