module

public import FnZPositiveCones.External.CircularExpandedRegularity
public import FnZPositiveCones.External.CircularDynamicsNormalization

@[expose] public section

/-! Genuine regular open ping-pong domains and exact action normalization. -/
namespace FnZPositiveCones.CircularDynamics
universe u
variable {ι : Type u} [DecidableEq ι] [Nonempty ι] [Finite ι]
variable {C : CircularGroupOrder (FreeGroup ι)} (R : CircularRealization C)

noncomputable def openExpandedDomain (h : FreeGroup ι) (s : ι × Bool) : Set StandardCircle :=
  interior (expandedFirstLetterDomain R h s)

theorem closure_openExpandedDomain (h : FreeGroup ι) (hh : C.IsSuccessor h)
    (hsep : ∀ s t, s ≠ t →
      Disjoint (closure (letterOrbit (realizationGenerators R) 0 s))
        (closure (letterOrbit (realizationGenerators R) 0 t))) (s : ι × Bool) :
    closure (openExpandedDomain R h s) = expandedFirstLetterDomain R h s :=
  expandedFirstLetterDomain_regularClosed R h hh hsep s

theorem openExpandedDomain_regular (h : FreeGroup ι) (hh : C.IsSuccessor h)
    (hsep : ∀ s t, s ≠ t →
      Disjoint (closure (letterOrbit (realizationGenerators R) 0 s))
        (closure (letterOrbit (realizationGenerators R) 0 t))) (s : ι × Bool) :
    interior (closure (openExpandedDomain R h s)) = openExpandedDomain R h s := by
  rw [closure_openExpandedDomain R h hh hsep]
  rfl

/-- The full complement inclusion holds for the actual open domains. Openness
of the action image upgrades containment in a closed domain to its interior. -/
theorem openExpandedDomain_fullPingPong (h : FreeGroup ι) (hh : C.IsSuccessor h)
    (hsep : ∀ s t, s ≠ t →
      Disjoint (closure (letterOrbit (realizationGenerators R) 0 s))
        (closure (letterOrbit (realizationGenerators R) 0 t))) (s : ι × Bool) :
    Set.MapsTo (letterPerm (realizationGenerators R) s)
      (closure (openExpandedDomain R h (PingPong.inverseLetter s)))ᶜ
      (openExpandedDomain R h s) := by
  rw [closure_openExpandedDomain R h hh hsep]
  have hopen : IsOpen (letterPerm (realizationGenerators R) s ''
      (expandedFirstLetterDomain R h (PingPong.inverseLetter s))ᶜ) := by
    rw [realizationGenerators_letter]
    exact (R.actionHomeomorph _).isOpenMap _
      (isCompact_expandedFirstLetterDomain R h hsep _).isClosed.isOpen_compl
  have hsub : letterPerm (realizationGenerators R) s ''
      (expandedFirstLetterDomain R h (PingPong.inverseLetter s))ᶜ ⊆
      interior (expandedFirstLetterDomain R h s) := hopen.subset_interior_iff.mpr
        (Set.image_subset_iff.mpr (expandedFirstLetterDomain_fullPingPong R h hh hsep s))
  intro x hx
  exact hsub ⟨x, hx, rfl⟩

/-- The regular open domains are nonempty, including when a raw color consisted
of isolated points. -/
theorem openExpandedDomain_nonempty (h : FreeGroup ι) (hh : C.IsSuccessor h)
    (hsep : ∀ s t, s ≠ t →
      Disjoint (closure (letterOrbit (realizationGenerators R) 0 s))
        (closure (letterOrbit (realizationGenerators R) 0 t))) (s : ι × Bool) :
    (openExpandedDomain R h s).Nonempty := by
  have hfree : Function.Injective (fun g => FreeGroup.lift (realizationGenerators R) g 0) := by
    simpa only [realizationGenerators_lift] using R.orbit_injective
  have hc : ∀ s, Continuous (letterPerm (realizationGenerators R) s) := by
    intro s
    rw [realizationGenerators_letter]
    exact R.action_continuous _
  have hbase := base_not_mem_colorClosures_of_separated _ _ hfree hc hsep
  obtain ⟨x, hx⟩ := firstLetterDomain_nonempty (realizationGenerators R) hsep hbase s
  have hxE : x ∈ expandedFirstLetterDomain R h s := subset_expandAlongGapChain _ _ _ _ _ hx
  by_contra he
  have hempty := Set.not_nonempty_iff_eq_empty.mp he
  have hr := closure_openExpandedDomain R h hh hsep s
  rw [hempty, closure_empty] at hr
  have hfalse : x ∈ (∅ : Set StandardCircle) := hr.symm ▸ hxE
  exact hfalse

/-- The final domains obtained by the source's exact generator normalization. -/
noncomputable def normalizedExpandedDomain (h : FreeGroup ι) : ι × Bool → Set StandardCircle :=
  normalizedDomains (fun i => R.actionHomeomorph (FreeGroup.of i)) (openExpandedDomain R h)

omit [DecidableEq ι] [Nonempty ι] [Finite ι] in
theorem realization_signedHomeomorph (s : ι × Bool) :
    (signedHomeomorph (fun i => R.actionHomeomorph (FreeGroup.of i)) s :
      StandardCircle → StandardCircle) = letterPerm (realizationGenerators R) s := by
  rcases s with ⟨i, b⟩
  cases b <;> rfl

/-- For both signed generators, the actual action maps the complement of the
opposite closed domain exactly onto the normalized domain. -/
theorem normalizedExpandedDomain_image (h : FreeGroup ι) (hh : C.IsSuccessor h)
    (hsep : ∀ s t, s ≠ t →
      Disjoint (closure (letterOrbit (realizationGenerators R) 0 s))
        (closure (letterOrbit (realizationGenerators R) 0 t))) (s : ι × Bool) :
    letterPerm (realizationGenerators R) s ''
      (closure (normalizedExpandedDomain R h (PingPong.inverseLetter s)))ᶜ =
      normalizedExpandedDomain R h s := by
  rw [← realization_signedHomeomorph]
  exact normalizedDomains_image (fun i => R.actionHomeomorph (FreeGroup.of i))
    (openExpandedDomain R h) (fun i => openExpandedDomain_regular R h hh hsep (i, false)) s

/-- Normalization only shrinks the actual open expanded domains; this uses the
proved full-complement condition, not merely trapping among colors. -/
theorem normalizedExpandedDomain_subset (h : FreeGroup ι) (hh : C.IsSuccessor h)
    (hsep : ∀ s t, s ≠ t →
      Disjoint (closure (letterOrbit (realizationGenerators R) 0 s))
        (closure (letterOrbit (realizationGenerators R) 0 t))) (s : ι × Bool) :
    normalizedExpandedDomain R h s ⊆ openExpandedDomain R h s := by
  apply normalizedDomains_subset (fun i => R.actionHomeomorph (FreeGroup.of i))
    (openExpandedDomain R h) ?_ s
  intro i
  exact openExpandedDomain_fullPingPong R h hh hsep (i, true)

end FnZPositiveCones.CircularDynamics
