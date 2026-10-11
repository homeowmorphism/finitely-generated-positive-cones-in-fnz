module

public import FnZPositiveCones.External.NoncofinalFixedCrossing
public import FnZPositiveCones.External.OrderedActionsCollapse
public import FnZPositiveCones.External.FreeGroupOrbitPerturbation
public import FnZPositiveCones.External.OddReduction

@[expose] public section

/-!
# The free action on a noncofinal central endpoint

Taking the finite lower endpoint of a central orbit gives a point fixed by
the center. Centrality makes its orbit weakly monotone in the original left
order. The orbit is still unbounded, although it need not be free. Extending
the free-factor action trivially across the center and completing its ties
with the original order recovers that order exactly.
-/

namespace FnZPositiveCones.NoncofinalEndpointAction

open NoncofinalFixedCrossing

universe u
variable {G : Type u} [Group G]

/-- Passing to the finite lower endpoint preserves every weak comparison.
Right multiplication is used only by central powers and is explicitly
converted to left multiplication before applying order invariance. -/
theorem endpoint_orbit_monotone (O : LeftGroupOrder G) (R : TightRealization O)
    (z : G) (hcentral : ∀ g : G, Commute z g)
    (hb : BddBelow (Set.range (fun n : ℤ => R.action (z ^ n) R.base)))
    {g h : G} (hgh : O.order.le g h) :
    R.action g (lowerEndpoint R z) ≤ R.action h (lowerEndpoint R z) := by
  have hcmp (n : ℤ) : R.action g (R.action (z ^ n) R.base) ≤
      R.action h (R.action (z ^ n) R.base) := by
    have hh := O.mul_le_mul_left g h (z ^ n) hgh
    rw [(hcentral g).zpow_left n |>.eq, (hcentral h).zpow_left n |>.eq] at hh
    simpa only [map_mul, RelIso.mul_apply] using (R.order_iff _ _).mp hh
  have hlow (n : ℤ) : R.action g (lowerEndpoint R z) ≤
      R.action h (R.action (z ^ n) R.base) :=
    ((R.action g).monotone (csInf_le hb ⟨n, rfl⟩)).trans (hcmp n)
  have hbound : (R.action h)⁻¹ (R.action g (lowerEndpoint R z)) ≤ lowerEndpoint R z := by
    apply le_csInf (Set.range_nonempty _)
    rintro _ ⟨n, rfl⟩
    simpa only [RelIso.inv_apply_self] using ((R.action h)⁻¹).monotone (hlow n)
  simpa only [RelIso.apply_inv_self] using (R.action h).monotone hbound

/-- If the marked center fixes a point, the full product orbit there is
exactly the free-factor orbit, retaining the integer-exponent identity. -/
theorem action_eq_free_at_fixed
    (ρ : (G × Multiplicative ℤ) →* (ℝ ≃o ℝ)) (x : ℝ)
    (hx : ρ (cofinalProductZ G) x = x) (g : G × Multiplicative ℤ) :
    ρ g x = ρ (g.1, 1) x := by
  have hg : g = (g.1, 1) * cofinalProductZ G ^ g.2.toAdd := by
    apply Prod.ext
    · simp [cofinalProductZ]
    · apply Multiplicative.toAdd.injective
      simp [cofinalProductZ]
  conv_lhs => rw [hg]
  rw [map_mul, RelIso.mul_apply, NoncofinalDynamics.fixed_zpow ρ _ hx]

/-- The actual free-factor action used at the central endpoint. -/
def freeAction (ρ : (G × Multiplicative ℤ) →* (ℝ ≃o ℝ)) : G →* (ℝ ≃o ℝ) :=
  ρ.comp (MonoidHom.inl G (Multiplicative ℤ))

/-- Extend a free-factor action by making the center act identically. -/
def productAction (ρ : G →* (ℝ ≃o ℝ)) : (G × Multiplicative ℤ) →* (ℝ ≃o ℝ) :=
  ρ.comp (MonoidHom.fst G (Multiplicative ℤ))

/-- The new product action keeps the old endpoint orbit exactly, even though
its central action is the identity everywhere. -/
theorem productFreeAction_at_fixed
    (ρ : (G × Multiplicative ℤ) →* (ℝ ≃o ℝ)) (x : ℝ)
    (hx : ρ (cofinalProductZ G) x = x) (g : G × Multiplicative ℤ) :
    productAction (freeAction ρ) g x = ρ g x :=
  (action_eq_free_at_fixed ρ x hx g).symm

/-- The free-factor orbit at the endpoint is unbounded. This uses absence
of a global fixed point, not freeness of this particular orbit. -/
theorem free_endpoint_orbit_unbounded (O : LeftGroupOrder (G × Multiplicative ℤ))
    (R : TightRealization O)
    (hb : BddBelow (Set.range (fun n : ℤ =>
      R.action (cofinalProductZ G ^ n) R.base))) :
    ∀ b : ℝ, ∃ g : G, b < freeAction R.action g (lowerEndpoint R (cofinalProductZ G)) := by
  intro b
  obtain ⟨g, hg⟩ := NoncofinalEnvelope.orbit_unbounded_above R.action R.no_global_fixed
    (lowerEndpoint R (cofinalProductZ G)) b
  refine ⟨g.1, ?_⟩
  exact (action_eq_free_at_fixed R.action _ (lowerEndpoint_fixed R _ hb) g) ▸ hg

/-- The endpoint action, with its nonfree orbit ties resolved by the
original order, recovers that order exactly. -/
theorem endpoint_actionCompletion_eq (O : LeftGroupOrder (G × Multiplicative ℤ))
    (R : TightRealization O)
    (hb : BddBelow (Set.range (fun n : ℤ =>
      R.action (cofinalProductZ G ^ n) R.base))) :
    O.actionCompletion (productAction (freeAction R.action))
      (lowerEndpoint R (cofinalProductZ G)) = O := by
  apply O.actionCompletion_eq_of_monotone
  intro g h hgh
  rw [productFreeAction_at_fixed R.action _ (lowerEndpoint_fixed R _ hb),
    productFreeAction_at_fixed R.action _ (lowerEndpoint_fixed R _ hb)]
  exact endpoint_orbit_monotone O R _ cofinalProductZ_central hb hgh

/-- Completion equality, rather than a free realizing orbit, suffices to
preserve finitely many signs under exact orbit agreement. -/
theorem completion_signs_of_orbit_agreement (O : LeftGroupOrder G)
    (ρ σ : G →* (ℝ ≃o ℝ)) (x : ℝ) (heq : O.actionCompletion ρ x = O)
    (F : Finset G) (hagree : ∀ g ∈ F, σ g x = ρ g x) :
    ∀ g ∈ F, (g ∈ (leftOrderCone (O.actionCompletion σ x)).1 ↔
      g ∈ (leftOrderCone O).1) := by
  intro g hg
  rw [LeftGroupOrder.actionCompletion_mem_cone, hagree g hg]
  have he := congrArg (fun Q => g ∈ (leftOrderCone Q).1) heq
  rw [LeftGroupOrder.actionCompletion_mem_cone] at he
  exact iff_of_eq he

/-- Opposite finite-trace perturbations of the free factor obstruct isolation
of any product order recovered by resolving the original orbit ties. -/
theorem not_isolated_of_opposite_free_perturbations {ι : Type u}
    (O : LeftGroupOrder (FreeGroup ι × Multiplicative ℤ))
    (ρ : FreeGroup ι →* (ℝ ≃o ℝ)) (x : ℝ)
    (heq : O.actionCompletion (productAction ρ) x = O)
    (hperturb : ∀ F : Finset (FreeGroup ι),
      ∃ σ τ : FreeGroup ι →* (ℝ ≃o ℝ), ∃ k : FreeGroup ι,
        (∀ g ∈ F, σ g x = ρ g x) ∧ (∀ g ∈ F, τ g x = ρ g x) ∧
        x < σ k x ∧ τ k x < x) :
    ¬ IsOpen ({O} : Set (LeftGroupOrder (FreeGroup ι × Multiplicative ℤ))) := by
  classical
  intro hiso
  have hfd : FinitelyDetermined (leftOrderCone O).1 :=
    (finiteDetermination_iff_leftOrder_isolated (leftOrderCone O)).mpr (by simpa using hiso)
  obtain ⟨S, hSP, hdet⟩ := hfd
  obtain ⟨σ, τ, k, hσ, hτ, hpos, hneg⟩ := hperturb (S.image Prod.fst)
  have forced (α : FreeGroup ι →* (ℝ ≃o ℝ))
      (hα : ∀ g ∈ S.image Prod.fst, α g x = ρ g x) :
      O.actionCompletion (productAction α) x = O := by
    have hsign := completion_signs_of_orbit_agreement O (productAction ρ)
      (productAction α) x heq S (fun g hg => hα g.1 (Finset.mem_image.mpr ⟨g, hg, rfl⟩))
    have hcone : leftOrderCone (O.actionCompletion (productAction α) x) = leftOrderCone O :=
      Subtype.ext (hdet _ (leftOrderCone (O.actionCompletion (productAction α) x)).2
        (fun g hg => (hsign g hg).mpr (hSP hg)))
    simpa using congrArg coneLeftOrder hcone
  have hpositive : O.order.lt 1 (k, 1) := by
    rw [← forced σ hσ, LeftGroupOrder.actionCompletion_lt]
    exact Or.inl (by simpa [productAction] using hpos)
  have hnegative : O.order.lt (k, 1) 1 := by
    rw [← forced τ hτ, LeftGroupOrder.actionCompletion_lt]
    exact Or.inl (by simpa [productAction] using hneg)
  let := O.order
  exact lt_asymm hpositive hnegative

/-- A noncofinal center forces nonisolation for a countable nonabelian free
group product. The perturbations act on the central fixed endpoint orbit;
their ties are completed with the original order. No moving primitive basis
or semigroup-generation assumption is used. -/
theorem not_isolated_of_not_cofinal {ι : Type u} [Nontrivial ι] [Countable ι]
    (O : LeftGroupOrder (FreeGroup ι × Multiplicative ℤ))
    (hnon : ¬ O.IsCofinal (cofinalProductZ (FreeGroup ι))) :
    ¬ IsOpen ({O} : Set (LeftGroupOrder (FreeGroup ι × Multiplicative ℤ))) := by
  obtain ⟨R⟩ := O.exists_tightRealization
  have hb := central_orbit_bddBelow O R _ cofinalProductZ_central hnon
  apply not_isolated_of_opposite_free_perturbations O (freeAction R.action)
    (lowerEndpoint R (cofinalProductZ (FreeGroup ι))) (endpoint_actionCompletion_eq O R hb)
  exact FreeGroupOrbitPerturbation.exists_finite_trace_opposite_motions _ _
    (free_endpoint_orbit_unbounded O R hb)

/-- Every isolated order on a countable nonabelian free-group product has
cofinal marked center, independently of its orientation. -/
theorem center_cofinal_of_isolated {ι : Type u} [Nontrivial ι] [Countable ι]
    (O : LeftGroupOrder (FreeGroup ι × Multiplicative ℤ))
    (hiso : IsOpen ({O} : Set (LeftGroupOrder (FreeGroup ι × Multiplicative ℤ)))) :
    O.IsCofinal (cofinalProductZ (FreeGroup ι)) := by
  by_contra hn
  exact not_isolated_of_not_cofinal O hn hiso

/-- The same result in the supplied strict positive-cone sign topology. -/
theorem cone_center_cofinal_of_isolated {ι : Type u} [Nontrivial ι] [Countable ι]
    (P : PositiveCone (FreeGroup ι × Multiplicative ℤ))
    (hiso : IsOpen ({P} : Set (PositiveCone (FreeGroup ι × Multiplicative ℤ)))) :
    (coneLeftOrder P).IsCofinal (cofinalProductZ (FreeGroup ι)) :=
  center_cofinal_of_isolated (coneLeftOrder P)
    ((finiteDetermination_iff_leftOrder_isolated P).mp
      ((finiteDetermination_iff_isolated P).mpr hiso))

/-- Exact noncofinal-branch obligation from the supplied odd-rank reduction.
The proved theorem is stronger: parity and the sign of the center are unused. -/
theorem isolatedOddRankCenterCofinal : IsolatedOddRankCenterCofinalGoal := by
  intro n hn _ P _ hiso
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  exact cone_center_cofinal_of_isolated P hiso

end FnZPositiveCones.NoncofinalEndpointAction
