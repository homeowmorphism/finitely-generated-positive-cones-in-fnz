module

public import FnZPositiveCones.External.CircularFGSeparation
public import FnZPositiveCones.External.CircularFGSeparationTopology
public import FnZPositiveCones.External.CircularDynamicsPrincipalChain
public import FnZPositiveCones.External.CircularDynamicsSeparatedDomains

@[expose] public section

/-! First-letter closure separation for the actual finitely generated cone.
Finite positive paths supply the cutset; the least positive element supplies
isolation. This bypasses the perturbation argument for general isolated orders. -/

namespace FnZPositiveCones.CircularFGSeparation

open CircularDynamics
universe u
variable {ι : Type u} [DecidableEq ι] [Nonempty ι]

/-- Finite generation itself forces distinct first-letter orbit colors to have
disjoint closures in every realization of the cofinal circular quotient. -/
theorem colorClosures_disjoint_of_semigroupFG
    (P : PositiveCone (FreeGroup ι × Multiplicative ℤ)) (hfg : SemigroupFG P.1)
    (hz : (coneLeftOrder P).order.lt 1 (cofinalProductZ (FreeGroup ι)))
    (hc : (coneLeftOrder P).IsCofinal (cofinalProductZ (FreeGroup ι)))
    (R : CircularRealization (cofinalProductCircularGroupOrder (coneLeftOrder P) hz hc))
    (s t : ι × Bool) (hst : s ≠ t) :
    Disjoint (closure (letterOrbit (realizationGenerators R) 0 s))
      (closure (letterOrbit (realizationGenerators R) 0 t)) := by
  obtain ⟨a, ha⟩ := semigroupFG_circular_successor P hfg hz hc
  obtain ⟨T, hT, hcut⟩ := exists_finite_circle_cutset P hfg hz hc R
  let F := (fun g => R.action g 0) '' T
  have hfree : Function.Injective (fun g => FreeGroup.lift (realizationGenerators R) g 0) := by
    simpa only [realizationGenerators_lift] using R.orbit_injective
  have heval (w : List (ι × Bool)) :
      evalWord (realizationGenerators R) w 0 = R.action (FreeGroup.mk w) 0 := by
    rw [← lift_mk_apply, realizationGenerators_lift]
  have hsubset (j : ι × Bool) : letterOrbit (realizationGenerators R) 0 j ⊆
      Set.range (fun g => R.action g 0) := by
    rintro _ ⟨w, _, rfl⟩
    exact ⟨FreeGroup.mk (j :: w), (heval _).symm⟩
  apply disjoint_closures_circle_of_finite_separators _ _ F (hT.image _)
    (letterOrbit_disjoint _ _ hfree hst)
  · rintro _ ⟨w, hw, rfl⟩ _ ⟨z, hz', rfl⟩
    obtain ⟨r, hr, hi⟩ := hcut (FreeGroup.mk (s :: w)) (FreeGroup.mk (t :: z))
      s t w z (by rw [FreeGroup.toWord_mk, hw.reduce_eq])
      (by rw [FreeGroup.toWord_mk, hz'.reduce_eq]) hst
    exact ⟨R.action r 0, ⟨r, hr, rfl⟩, by simpa only [heval] using hi⟩
  · intro x hx
    have hxorb : x ∈ Set.range (fun g => R.action g 0) := by
      rcases hx with hx | ⟨g, _, rfl⟩
      · refine ⟨1, ?_⟩
        simpa only [map_one, Equiv.Perm.one_apply] using hx.symm
      · exact ⟨g, rfl⟩
    obtain ⟨g, rfl⟩ := hxorb
    obtain ⟨U, hU, hg, hsing⟩ := R.exists_orbit_isolating_neighborhood ha g
    refine ⟨U, hU, hg, ?_⟩
    rintro x ⟨hxU, hx⟩
    apply hsing ▸ (show x ∈ U ∩ closure (Set.range (fun g => R.action g 0)) from ?_)
    exact ⟨hxU, subset_closure (hx.elim (fun hs => hsubset s hs) (fun ht => hsubset t ht))⟩

end FnZPositiveCones.CircularFGSeparation
