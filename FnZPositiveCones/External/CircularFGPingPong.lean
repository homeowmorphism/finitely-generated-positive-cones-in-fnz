module

public import FnZPositiveCones.External.CircularDomainComponents
public import FnZPositiveCones.External.CircularFGDomains
public import FnZPositiveCones.External.NoncofinalPrecone
public import FnZPositiveCones.Cone.OppositeFG

@[expose] public section

/-! The actual finite normalized domains supplied by a finitely generated cone. -/
namespace FnZPositiveCones
open CircularDynamics
universe u

/-- The checked domain data on a specified realized action. Finite component
counts and exact image identities are conclusions of the construction. The
cyclic endpoint adjacency needed by the final parity argument is separate. -/
structure FiniteNormalizedDomains {ι : Type u} {C : CircularGroupOrder (FreeGroup ι)}
    (R : CircularRealization C) where
  domain : ι × Bool → Set StandardCircle
  isOpen_domain : ∀ s, IsOpen (domain s)
  regular_domain : ∀ s, interior (closure (domain s)) = domain s
  nonempty_domain : ∀ s, (domain s).Nonempty
  finite_components : ∀ s, Finite (ConnectedComponents ↥(domain s))
  separated : ∀ s t, s ≠ t → Disjoint (closure (domain s)) (closure (domain t))
  base_avoids : ∀ s, (0 : StandardCircle) ∉ closure (domain s)
  image_domain : ∀ s, letterPerm (fun i => R.action (FreeGroup.of i)) s ''
    (closure (domain (PingPong.inverseLetter s)))ᶜ = domain s

namespace CircularDynamics
variable {ι : Type u} [DecidableEq ι] [Nonempty ι] [Finite ι]
variable {C : CircularGroupOrder (FreeGroup ι)} (R : CircularRealization C)

/-- All the specified data are supplied by the actual cutoff and normalization
construction, with only successor and color separation as inputs. -/
noncomputable def finiteNormalizedDomains (h : FreeGroup ι) (hh : C.IsSuccessor h)
    (hsep : ∀ s t, s ≠ t →
      Disjoint (closure (letterOrbit (realizationGenerators R) 0 s))
        (closure (letterOrbit (realizationGenerators R) 0 t))) : FiniteNormalizedDomains R where
  domain := normalizedExpandedDomain R h
  isOpen_domain := by
    rintro ⟨i, b⟩
    cases b
    · exact isOpen_interior
    · exact isOpen_normalizedPositiveDomain _ _
  regular_domain := by
    rintro ⟨i, b⟩
    cases b
    · exact openExpandedDomain_regular R h hh hsep (i, false)
    · exact normalizedPositiveDomain_regular _ _ (openExpandedDomain_regular R h hh hsep (i, false))
  nonempty_domain := normalizedExpandedDomain_nonempty R h hh hsep
  finite_components := finite_components_normalizedExpandedDomain R h hh hsep
  separated := fun _ _ hst => normalizedExpandedDomain_disjoint_closures R h hh hsep hst
  base_avoids := base_not_mem_closure_normalizedExpandedDomain R h hh hsep
  image_domain := normalizedExpandedDomain_image R h hh hsep

end CircularDynamics

/-- For the FG-specific route, both the required cofinality and separation
hypotheses are discharged. Only central orientation is specified here. -/
theorem semigroupFG_exists_finiteNormalizedDomains {ι : Type u} [Nontrivial ι] [Finite ι]
    (P : PositiveCone (FreeGroup ι × Multiplicative ℤ)) (hfg : SemigroupFG P.1)
    (hz : (coneLeftOrder P).order.lt 1 (cofinalProductZ (FreeGroup ι))) :
    ∃ (C : CircularGroupOrder (FreeGroup ι)) (R : CircularRealization C),
      Nonempty (FiniteNormalizedDomains R) ∧ ∃ h, C.IsSuccessor h := by
  classical
  let hc := NoncofinalPrecone.center_cofinal_of_semigroupFG P hfg
  let C := cofinalProductCircularGroupOrder (coneLeftOrder P) hz hc
  obtain ⟨R⟩ := C.exists_circularRealization
  obtain ⟨h, hh⟩ := semigroupFG_circular_successor P hfg hz hc
  have hsep := CircularFGSeparation.colorClosures_disjoint_of_semigroupFG P hfg hz hc R
  exact ⟨C, R, ⟨finiteNormalizedDomains R h hh hsep⟩, h, hh⟩

/-- Every hypothesized FG cone in rank at least two provides actual finite
normalized domains and a successor, without external dynamical assumptions. -/
theorem hasFGPositiveCone_exists_finiteNormalizedDomains (n : ℕ) (hn : 2 ≤ n)
    (hfg : HasFGPositiveCone (FreeGroup (Fin n) × Multiplicative ℤ)) :
    ∃ (C : CircularGroupOrder (FreeGroup (Fin n))) (R : CircularRealization C),
      Nonempty (FiniteNormalizedDomains R) ∧ ∃ h, C.IsSuccessor h := by
  let := Fin.nontrivial_iff_two_le.mpr hn
  obtain ⟨S, hS⟩ := hfg
  let P : PositiveCone (FreeGroup (Fin n) × Multiplicative ℤ) :=
    ⟨Subsemigroup.closure (S : Set _), hS⟩
  have hP : SemigroupFG P.1 := ⟨S, rfl⟩
  have hne : cofinalProductZ (FreeGroup (Fin n)) ≠ 1 := by
    intro he
    have hh := congrArg (fun p : FreeGroup (Fin n) × Multiplicative ℤ => p.2.toAdd) he
    change (1 : ℤ) = 0 at hh
    omega
  rcases P.mem_or_mem_opposite hne with hz | hz
  · apply semigroupFG_exists_finiteNormalizedDomains P hP
    simpa only [coneLeftOrder_lt, inv_one, one_mul] using hz
  · apply semigroupFG_exists_finiteNormalizedDomains P.opposite (semigroupFG_opposite hP)
    simpa only [coneLeftOrder_lt, inv_one, one_mul] using hz

end FnZPositiveCones
