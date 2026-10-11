module

public import FnZPositiveCones.External.CircularDynamicsColors
public import FnZPositiveCones.External.CircularDynamicsCircularHull

@[expose] public section

/-! Canonical filled first-letter domains and their checked trapping property. -/
namespace FnZPositiveCones
namespace CircularDynamics
universe u v
variable {ι : Type u} {X : Type v} [TopologicalSpace X]

/-- The union of the genuine first-letter orbit closures. -/
def coloredOrbitClosure (ρ : ι → Equiv.Perm X) (base : X) : Set X :=
  ⋃ s, closure (letterOrbit ρ base s)

variable [Nonempty ι]

/-- The unique color on separated orbit closures; the value outside their union
is immaterial and is chosen only to make this a total function. -/
noncomputable def orbitClosureColor (ρ : ι → Equiv.Perm X) (base : X) (x : X) : ι × Bool := by
  classical
  exact if h : ∃ s, x ∈ closure (letterOrbit ρ base s) then h.choose else Classical.arbitrary _

theorem mem_closure_letterOrbit_of_mem_coloredOrbitClosure
    (ρ : ι → Equiv.Perm X) (base : X) {x : X} (hx : x ∈ coloredOrbitClosure ρ base) :
    x ∈ closure (letterOrbit ρ base (orbitClosureColor ρ base x)) := by
  classical
  have he : ∃ s, x ∈ closure (letterOrbit ρ base s) := Set.mem_iUnion.mp hx
  simpa only [orbitClosureColor, dite_eq_left he] using he.choose_spec

theorem orbitClosureColor_eq_of_mem (ρ : ι → Equiv.Perm X) (base : X)
    (hsep : ∀ s t, s ≠ t → Disjoint (closure (letterOrbit ρ base s))
      (closure (letterOrbit ρ base t))) {x : X} {s : ι × Bool}
    (hx : x ∈ closure (letterOrbit ρ base s)) : orbitClosureColor ρ base x = s := by
  have hxK : x ∈ coloredOrbitClosure ρ base := Set.mem_iUnion.mpr ⟨s, hx⟩
  have hxC := mem_closure_letterOrbit_of_mem_coloredOrbitClosure ρ base hxK
  by_contra hne
  exact Set.disjoint_left.mp (hsep _ _ hne) hxC hx

omit [Nonempty ι] in
/-- The closed orbit itself is invariant under every signed generator. -/
theorem letterPerm_mapsTo_orbitClosure (ρ : ι → Equiv.Perm X) (base : X)
    (s : ι × Bool) (hc : Continuous (letterPerm ρ s)) :
    Set.MapsTo (letterPerm ρ s) (closure (Set.range (fun g => FreeGroup.lift ρ g base)))
      (closure (Set.range (fun g => FreeGroup.lift ρ g base))) := by
  apply Set.MapsTo.closure _ hc
  rintro x ⟨g, rfl⟩
  refine ⟨FreeGroup.mk [s] * g, ?_⟩
  dsimp only
  rw [map_mul]
  change FreeGroup.lift ρ (FreeGroup.mk [s]) (FreeGroup.lift ρ g base) = _
  rw [lift_mk_apply]
  rfl

variable [CircularOrder X]

/-- The canonical first-letter domain, filling precisely monochrome segments
away from the basepoint. -/
noncomputable def firstLetterDomain (ρ : ι → Equiv.Perm X) (base : X)
    (s : ι × Bool) : Set X :=
  circularColorFilledHull (coloredOrbitClosure ρ base) (orbitClosureColor ρ base) base s

/-- Source Step2: genuine separated initial-letter closures imply the trapping
rule for their actual filled domains. No arbitrary domain-action condition is
assumed, and all inverse-letter/basepoint exceptions are discharged here. -/
theorem firstLetterDomain_trapping [Finite ι] [T1Space X]
    (ρ : ι → Equiv.Perm X) (base : X)
    (hρ : ∀ i, PreservesCircular (ρ i))
    (hc : ∀ s, Continuous (letterPerm ρ s))
    (hsep : ∀ s t, s ≠ t → Disjoint (closure (letterOrbit ρ base s))
      (closure (letterOrbit ρ base t))) :
    PingPong.DomainTrapping ρ (firstLetterDomain ρ base) := by
  intro s t hts
  have hsCirc : PreservesCircular (letterPerm ρ s) := by
    rcases s with ⟨i, b⟩
    cases b
    · exact preservesCircular_inv (hρ i)
    · exact hρ i
  have hInv : (letterPerm ρ s).symm = letterPerm ρ (PingPong.inverseLetter s) := by
    rw [PingPong.letterPerm_inverseLetter]
    rfl
  have hpre : (letterPerm ρ s).symm base ∈ closure
      (letterOrbit ρ base (PingPong.inverseLetter s)) := by
    apply subset_closure
    rw [hInv]
    exact ⟨[], FreeGroup.IsReduced.singleton, rfl⟩
  apply mapsTo_circularColorFilledHull (coloredOrbitClosure ρ base)
    (orbitClosureColor ρ base) base t s (letterPerm ρ s) hsCirc
  · exact Set.mem_iUnion.mpr ⟨PingPong.inverseLetter s, hpre⟩
  · rw [orbitClosureColor_eq_of_mem ρ base hsep hpre]
    exact hts.symm
  · intro x hx hxt
    have hxC := mem_closure_letterOrbit_of_mem_coloredOrbitClosure ρ base hx
    rw [hxt] at hxC
    have hfx := closure_letterOrbit_mapsTo ρ base s t (hc s) hts hxC
    exact ⟨Set.mem_iUnion.mpr ⟨s, hfx⟩, orbitClosureColor_eq_of_mem ρ base hsep hfx⟩
  · intro z hz
    have hzC : z ∈ closure (Set.range (fun g => FreeGroup.lift ρ g base)) := by
      rw [orbitClosure_eq_base_union_colorClosures]
      exact Or.inr hz
    have hpreC := letterPerm_mapsTo_orbitClosure ρ base (PingPong.inverseLetter s)
      (hc _) hzC
    rw [← hInv, orbitClosure_eq_base_union_colorClosures] at hpreC
    exact hpreC.elim (fun h => Or.inr h) Or.inl

end CircularDynamics
end FnZPositiveCones
