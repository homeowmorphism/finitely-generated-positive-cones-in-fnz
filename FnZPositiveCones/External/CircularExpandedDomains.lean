module

public import FnZPositiveCones.External.CircularDynamicsPrincipalChain
public import FnZPositiveCones.External.CircularDynamicsExpansion
public import FnZPositiveCones.External.CircularDynamicsSeparatedDomains

@[expose] public section

/-! The actual principal-gap enlargement of the separated first-letter domains. -/

namespace FnZPositiveCones.CircularDynamics
universe u
variable {ι : Type u} [DecidableEq ι] [Nonempty ι] [Finite ι]
variable {C : CircularGroupOrder (FreeGroup ι)} (R : CircularRealization C)

omit [DecidableEq ι] [Finite ι] in
/-- All points of a color closure belong to the corresponding filled domain. -/
theorem closure_letterOrbit_subset_firstLetterDomain
    (ρ : ι → Equiv.Perm StandardCircle)
    (hsep : ∀ s t, s ≠ t → Disjoint (closure (letterOrbit ρ 0 s))
      (closure (letterOrbit ρ 0 t)))
    (hbase : ∀ s, (0 : StandardCircle) ∉ closure (letterOrbit ρ 0 s)) (s : ι × Bool) :
    closure (letterOrbit ρ 0 s) ⊆ firstLetterDomain ρ 0 s := by
  intro x hx
  have hxK : x ∈ coloredOrbitClosure ρ 0 := Set.mem_iUnion.mpr ⟨s, hx⟩
  have he := orbitClosureColor_eq_of_mem ρ 0 hsep hx
  have hm : x ∈ circularColorFilledHull (coloredOrbitClosure ρ 0)
      (orbitClosureColor ρ 0) 0 s ∩ coloredOrbitClosure ρ 0 := by
    rw [circularColorFilledHull_inter _ _ _ (base_not_mem_coloredOrbitClosure ρ 0 hbase)]
    exact ⟨hxK, he⟩
  exact hm.1

/-- Enlarge precisely the finite inverse-prefix chain, using strictly increasing
cut positions in the original successor gap. -/
noncomputable def expandedFirstLetterDomain (h : FreeGroup ι) (s : ι × Bool) :
    Set StandardCircle :=
  expandAlongGapChain (firstLetterDomain (realizationGenerators R) 0)
    (successorLetter h) (principalGapChart R h) (principalGapCut (FreeGroup.norm h)) s

/-- Source Step 3 on the actual realized action: every point outside the inverse
expanded domain is sent into the matching expanded domain. -/
theorem expandedFirstLetterDomain_fullPingPong (h : FreeGroup ι) (hh : C.IsSuccessor h)
    (hsep : ∀ s t, s ≠ t →
      Disjoint (closure (letterOrbit (realizationGenerators R) 0 s))
        (closure (letterOrbit (realizationGenerators R) 0 t))) (s : ι × Bool) :
    Set.MapsTo (letterPerm (realizationGenerators R) s)
      (expandedFirstLetterDomain R h (PingPong.inverseLetter s))ᶜ
      (expandedFirstLetterDomain R h s) := by
  have hfree : Function.Injective (fun g => FreeGroup.lift (realizationGenerators R) g 0) := by
    simpa only [realizationGenerators_lift] using R.orbit_injective
  have hc : ∀ s, Continuous (letterPerm (realizationGenerators R) s) := by
    intro s
    rw [realizationGenerators_letter]
    exact R.action_continuous _
  have hbase := base_not_mem_colorClosures_of_separated _ _ hfree hc hsep
  exact expandAlongGapChain_fullPingPong (realizationGenerators R) 0
    (firstLetterDomain (realizationGenerators R) 0) (successorLetter h)
    (principalGapChart R h) (principalGapCut (FreeGroup.norm h))
    (firstLetterDomain_trapping _ _ (fun i => R.action_preserves (FreeGroup.of i)) hc hsep)
    (fun s => closure_letterOrbit_subset_firstLetterDomain _ hsep hbase s
      (subset_closure ⟨[], FreeGroup.IsReduced.singleton, rfl⟩))
    (principalGapChart_cover R h hh hsep) (principalGapChart_step R h)
    (principalGapChart_other R h hh hsep) s

omit [Nonempty ι] [Finite ι] in
theorem principalGapChart_continuous (h : FreeGroup ι)
    (i : Fin (FreeGroup.norm h + 1)) : Continuous (principalGapChart R h i) := by
  exact (R.action_continuous _).comp ((AddCircle.continuous_mk' (1 : ℝ)).comp
    (continuous_id.mul_const _))

/-- The enlarged domains are compact, since the raw domains and every added
closed subarc are compact and the principal chain is finite. -/
theorem isCompact_expandedFirstLetterDomain (h : FreeGroup ι)
    (hsep : ∀ s t, s ≠ t →
      Disjoint (closure (letterOrbit (realizationGenerators R) 0 s))
        (closure (letterOrbit (realizationGenerators R) 0 t))) (s : ι × Bool) :
    IsCompact (expandedFirstLetterDomain R h s) := by
  have hfree : Function.Injective (fun g => FreeGroup.lift (realizationGenerators R) g 0) := by
    simpa only [realizationGenerators_lift] using R.orbit_injective
  have hc : ∀ s, Continuous (letterPerm (realizationGenerators R) s) := by
    intro s
    rw [realizationGenerators_letter]
    exact R.action_continuous _
  have hbase := base_not_mem_colorClosures_of_separated _ _ hfree hc hsep
  have hraw := isCompact_firstLetterDomain (realizationGenerators R) hsep hbase s
  let N := FreeGroup.norm h
  let chart := principalGapChart R h
  let cut := principalGapCut N
  have hright : IsCompact {x | ∃ j : Fin N, successorLetter h j = s ∧
      ∃ t ∈ Set.Icc (cut j) 1, chart j.castSucc t = x} := by
    have hi := isCompact_iUnion (fun j : Fin N => isCompact_iUnion
      (fun _ : successorLetter h j = s => (isCompact_Icc : IsCompact (Set.Icc (cut j) 1)).image
        (principalGapChart_continuous R h j.castSucc)))
    convert hi using 1
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_image, exists_prop, chart]
  have hleft : IsCompact {x | ∃ j : Fin N, PingPong.inverseLetter (successorLetter h j) = s ∧
      ∃ t ∈ Set.Icc 0 (cut j), chart j.succ t = x} := by
    have hi := isCompact_iUnion (fun j : Fin N => isCompact_iUnion
      (fun _ : PingPong.inverseLetter (successorLetter h j) = s => (isCompact_Icc : IsCompact (Set.Icc 0 (cut j))).image
        (principalGapChart_continuous R h j.succ)))
    convert hi using 1
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_image, exists_prop, chart]
  exact (hraw.union hright).union hleft

end FnZPositiveCones.CircularDynamics
