module

public import FnZPositiveCones.External.PingPongGaps

@[expose] public section

/-! The orbit-to-boundary adapter needs a surjection, not a bijection.
Distinct tight-orbit gaps may meet the same finite principal interval, notably
the two gaps adjacent to the isolated basepoint. -/
namespace FnZPositiveCones.PingPong
open CircularDynamics
universe u v w
variable {ι : Type u} {Ω : Type v} {C : Type w}

/-- A surjection from principal orbit gaps to finite endpoint gaps suffices.
Local moves may already agree after the identification, so their exact contract
is membership in the generated endpoint relation. -/
theorem endpoint_gap_connected_of_one_orbit_surjective
    (ρ : ι → Equiv.Perm Ω) (D : ι × Bool → Set Ω) (htrap : DomainTrapping ρ D)
    (circle graph : Equiv.Perm C)
    (q : {x // PrincipalGap D x} → C) (hq : Function.Surjective q)
    (hlocal : ∀ (s : ι × Bool) (x y : {x // PrincipalGap D x}),
      letterPerm ρ s x.val = y.val →
        Relation.EqvGen (GapStep circle graph) (q x) (q y))
    (horbit : ∀ x y : Ω, ∃ g : FreeGroup ι, FreeGroup.lift ρ g x = y) :
    ∀ c d, Relation.EqvGen (GapStep circle graph) c d := by
  intro c d
  obtain ⟨x, rfl⟩ := hq c
  obtain ⟨y, rfl⟩ := hq d
  have hp := principal_path_of_same_orbit ρ D htrap x y (horbit _ _)
  induction hp with
  | rel x y h =>
    obtain ⟨s, hs⟩ := h
    exact hlocal s x y hs
  | refl x => exact Relation.EqvGen.refl _
  | symm x y _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans x y z _ _ hxy hyz => exact Relation.EqvGen.trans _ _ _ hxy hyz

section FiniteConfiguration
variable {I : Type u} {A B : I → Type v}
  [Fintype I] [DecidableEq I] [Nonempty I]
  [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]
  [∀ i, DecidableEq (A i)] [∀ i, DecidableEq (B i)]
  [∀ i, Nonempty (A i)] [∀ i, Nonempty (B i)]
  {Γ : Type w}

/-- The finite parity theorem with the weaker, geometrically correct gap
surjection contract. No injectivity of the gap assignment is required. -/
theorem even_of_one_gap_orbit_surjective
    (ρ : I → Equiv.Perm Γ) (D : I × Bool → Set Γ) (htrap : DomainTrapping ρ D)
    (f : ∀ i, A i ≃ B i) (g : ∀ i, B i ≃ A i)
    (next : ∀ i, Equiv.Perm (A i)) (hnext : ∀ i, (next i).IsCycleOn Set.univ)
    (hadj : ∀ i a, g i (f i a) = next i a)
    (circle : Equiv.Perm (Component A B)) (hcircle : circle.IsCycleOn Set.univ)
    (q : {x // PrincipalGap D x} → Component A B) (hq : Function.Surjective q)
    (hlocal : ∀ (s : I × Bool) (x y : {x // PrincipalGap D x}),
      letterPerm ρ s x.val = y.val →
        Relation.EqvGen (GapStep circle (polygonGraph f g)) (q x) (q y))
    (horbit : ∀ x y : Γ, ∃ w : FreeGroup I, FreeGroup.lift ρ w x = y) :
    Even (Fintype.card I) := by
  apply even_of_connected_component_configuration f g next hnext hadj circle hcircle
  exact endpoint_gap_connected_of_one_orbit_surjective ρ D htrap circle
    (polygonGraph f g) q hq hlocal horbit

end FiniteConfiguration
end FnZPositiveCones.PingPong
