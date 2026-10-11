module

public import FnZPositiveCones.External.PingPongCombinatorics
public import FnZPositiveCones.External.CircularDynamics

@[expose] public section

/-!
# Reduced-word paths among principal ping-pong gaps

A gap is principal when it is contained in none of the ping-pong domains.
Once a reduced itinerary enters a domain, every later letter keeps it in the
domain bearing that letter. Consequently an itinerary whose endpoints are
principal never leaves the principal gaps. This is the orbit-reduction step in
MMRT §3.1; it uses the domain trapping property, not an assumed connected graph.
-/

namespace FnZPositiveCones.PingPong

open CircularDynamics

universe u v w

variable {ι : Type u} {Ω : Type v}

/-- The inverse of a signed generator. -/
def inverseLetter (s : ι × Bool) : ι × Bool := (s.1, !s.2)

@[simp] theorem inverseLetter_inverse (s : ι × Bool) :
    inverseLetter (inverseLetter s) = s := by
  rcases s with ⟨i, b⟩
  cases b <;> rfl

@[simp] theorem letterPerm_inverseLetter (ρ : ι → Equiv.Perm Ω) (s : ι × Bool) :
    letterPerm ρ (inverseLetter s) = (letterPerm ρ s)⁻¹ := by
  rcases s with ⟨i, b⟩
  cases b <;> simp [inverseLetter, letterPerm]

/-- A principal gap is not contained in any individual domain. -/
def PrincipalGap (D : ι × Bool → Set Ω) (x : Ω) : Prop := ∀ s, x ∉ D s

/-- The ordinary ping-pong condition applied to gaps already contained in a domain. -/
def DomainTrapping (ρ : ι → Equiv.Perm Ω) (D : ι × Bool → Set Ω) : Prop :=
  ∀ s t, t ≠ inverseLetter s → ∀ ⦃x⦄, x ∈ D t → letterPerm ρ s x ∈ D s

/-- The gaps contained in a point domain. -/
def gapDomain {X : Type w} (D : ι × Bool → Set X) (gap : Ω → Set X)
    (s : ι × Bool) : Set Ω := {x | gap x ⊆ D s}

/-- Actual point-domain ping-pong and transport of gap sets imply the trapping
condition used in the reduced-word argument. `excluded s` can be the closure of
an open ping-pong domain, so no boundary convention is silently strengthened. -/
theorem domainTrapping_of_point_domains {X : Type w}
    (ρ : ι → Equiv.Perm X) (τ : ι → Equiv.Perm Ω)
    (D excluded : ι × Bool → Set X) (gap : Ω → Set X)
    (hseparated : ∀ s t, s ≠ t → Disjoint (D s) (excluded t))
    (hpingpong : ∀ s, Set.MapsTo (letterPerm ρ s) (excluded (inverseLetter s))ᶜ (D s))
    (htransport : ∀ s x, gap (letterPerm τ s x) = letterPerm ρ s '' gap x) :
    DomainTrapping τ (gapDomain D gap) := by
  intro s t hts x hx y hy
  rw [htransport] at hy
  obtain ⟨z, hz, rfl⟩ := hy
  apply hpingpong s
  exact fun hbad => Set.disjoint_left.mp (hseparated t (inverseLetter s) hts) (hx hz) hbad

/-- Leaving the principal gaps necessarily enters the domain of the applied letter. -/
theorem principal_step_or_domain (ρ : ι → Equiv.Perm Ω) (D : ι × Bool → Set Ω)
    (htrap : DomainTrapping ρ D) {x : Ω} (hx : PrincipalGap D x) (s : ι × Bool) :
    PrincipalGap D (letterPerm ρ s x) ∨ letterPerm ρ s x ∈ D s := by
  classical
  by_cases hs : letterPerm ρ s x ∈ D s
  · exact Or.inr hs
  · left
    intro t ht
    have hts : t ≠ inverseLetter (inverseLetter s) := by
      simpa using (show t ≠ s from fun h => hs (h ▸ ht))
    have h := htrap (inverseLetter s) t hts ht
    have hx' : x ∈ D (inverseLetter s) := by simpa using h
    exact hx _ hx'

/-- Consecutive letters of a reduced word are not inverses. -/
theorem reduced_head_ne_inverse {s t : ι × Bool} {w : List (ι × Bool)}
    (h : FreeGroup.IsReduced (s :: t :: w)) : t ≠ inverseLetter s := by
  intro he
  have hst := (FreeGroup.isReduced_cons_cons.mp h).1
  rcases s with ⟨i, b⟩
  subst t
  cases b <;> simp [inverseLetter] at hst

/-- A reduced itinerary from a principal gap either remains principal or ends
inside the domain of its final applied letter (the leftmost letter of the word). -/
theorem reduced_eval_principal_or_domain
    (ρ : ι → Equiv.Perm Ω) (D : ι × Bool → Set Ω) (htrap : DomainTrapping ρ D)
    {x : Ω} (hx : PrincipalGap D x) (s : ι × Bool) (w : List (ι × Bool))
    (hred : FreeGroup.IsReduced (s :: w)) :
    PrincipalGap D (evalWord ρ (s :: w) x) ∨ evalWord ρ (s :: w) x ∈ D s := by
  induction w generalizing s with
  | nil => exact principal_step_or_domain ρ D htrap hx s
  | cons t w ih =>
    have ht := (FreeGroup.isReduced_cons_cons.mp hred).2
    rcases ih t ht with hp | hd
    · exact principal_step_or_domain ρ D htrap hp s
    · exact Or.inr (htrap s t (reduced_head_ne_inverse hred) hd)

/-- If both ends of a reduced word are principal, removing the last applied
letter leaves a principal gap as well. -/
theorem principal_tail_of_reduced_eval
    (ρ : ι → Equiv.Perm Ω) (D : ι × Bool → Set Ω) (htrap : DomainTrapping ρ D)
    {x : Ω} (hx : PrincipalGap D x) (s : ι × Bool) (w : List (ι × Bool))
    (hred : FreeGroup.IsReduced (s :: w)) (hy : PrincipalGap D (evalWord ρ (s :: w) x)) :
    PrincipalGap D (evalWord ρ w x) := by
  cases w with
  | nil => exact hx
  | cons t w =>
    have ht := (FreeGroup.isReduced_cons_cons.mp hred).2
    rcases reduced_eval_principal_or_domain ρ D htrap hx t w ht with hp | hd
    · exact hp
    · exact False.elim (hy s (htrap s t (reduced_head_ne_inverse hred) hd))

/-- A single generator move between two principal gaps. -/
def PrincipalStep (ρ : ι → Equiv.Perm Ω) (D : ι × Bool → Set Ω)
    (x y : {x // PrincipalGap D x}) : Prop :=
  ∃ s : ι × Bool, letterPerm ρ s x.val = y.val

/-- Every reduced path between principal gaps decomposes into principal generator moves. -/
theorem principal_path_of_reduced_eval
    (ρ : ι → Equiv.Perm Ω) (D : ι × Bool → Set Ω) (htrap : DomainTrapping ρ D)
    {x : Ω} (hx : PrincipalGap D x) (w : List (ι × Bool))
    (hred : FreeGroup.IsReduced w) (hy : PrincipalGap D (evalWord ρ w x)) :
    Relation.EqvGen (PrincipalStep ρ D) ⟨x, hx⟩ ⟨evalWord ρ w x, hy⟩ := by
  induction w with
  | nil => exact Relation.EqvGen.refl _
  | cons s w ih =>
    have hp := principal_tail_of_reduced_eval ρ D htrap hx s w hred hy
    have hw : FreeGroup.IsReduced w := by
      cases w with
      | nil => exact FreeGroup.IsReduced.nil
      | cons t v => exact (FreeGroup.isReduced_cons_cons.mp hred).2
    exact Relation.EqvGen.trans _ _ _ (ih hw hp)
      (Relation.EqvGen.rel _ _ ⟨s, rfl⟩)

/-- Full group orbit equivalence between principal gaps reduces to local principal moves. -/
theorem principal_path_of_same_orbit
    (ρ : ι → Equiv.Perm Ω) (D : ι × Bool → Set Ω) (htrap : DomainTrapping ρ D)
    (x y : {x // PrincipalGap D x})
    (horbit : ∃ g : FreeGroup ι, FreeGroup.lift ρ g x.val = y.val) :
    Relation.EqvGen (PrincipalStep ρ D) x y := by
  classical
  obtain ⟨g, hg⟩ := horbit
  have he : evalWord ρ g.toWord x.val = y.val := by
    rw [← lift_mk_apply, FreeGroup.mk_toWord, hg]
  have hy : PrincipalGap D (evalWord ρ g.toWord x.val) := he ▸ y.property
  have h := principal_path_of_reduced_eval ρ D htrap x.property g.toWord
    FreeGroup.isReduced_toWord hy
  simpa only [he, Subtype.eta] using h

/-- A local endpoint formula transports principal moves to the finite gap graph. -/
theorem endpoint_gap_connected_of_one_orbit {C : Type w}
    (ρ : ι → Equiv.Perm Ω) (D : ι × Bool → Set Ω) (htrap : DomainTrapping ρ D)
    (circle graph : Equiv.Perm C) (e : {x // PrincipalGap D x} ≃ C)
    (hlocal : ∀ (s : ι × Bool) (x y : {x // PrincipalGap D x}),
      letterPerm ρ s x.val = y.val →
        circle (e x) = graph (e y) ∨ circle (e y) = graph (e x))
    (horbit : ∀ x y : Ω, ∃ g : FreeGroup ι, FreeGroup.lift ρ g x = y) :
    ∀ c d, Relation.EqvGen (GapStep circle graph) c d := by
  intro c d
  have hpath := principal_path_of_same_orbit ρ D htrap (e.symm c) (e.symm d)
    (horbit _ _)
  suffices h : Relation.EqvGen (GapStep circle graph) (e (e.symm c)) (e (e.symm d)) by
    simpa using h
  generalize e.symm c = x at hpath ⊢
  generalize e.symm d = y at hpath ⊢
  induction hpath with
  | rel x y h =>
    obtain ⟨s, hs⟩ := h
    rcases hlocal s x y hs with hxy | hyx
    · exact Relation.EqvGen.rel _ _ hxy
    · exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ hyx)
  | refl x => exact Relation.EqvGen.refl _
  | symm x y _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans x y z _ _ hxy hyz => exact Relation.EqvGen.trans _ _ _ hxy hyz

section FiniteConfiguration

variable {I : Type u} {A B : I → Type v}
  [Fintype I] [DecidableEq I] [Nonempty I]
  [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]
  [∀ i, DecidableEq (A i)] [∀ i, DecidableEq (B i)]
  [∀ i, Nonempty (A i)] [∀ i, Nonempty (B i)]
  {Ω : Type w}

/-- Finite component parity from an actual transitive action on complementary gaps.
The only orbit-to-endpoint input is the formula for one signed generator move;
all reduction from arbitrary group words and all boundary counts are proved.
The geometric domain construction and this local endpoint formula remain separate.
-/
theorem even_of_one_gap_orbit
    (ρ : I → Equiv.Perm Ω) (D : I × Bool → Set Ω) (htrap : DomainTrapping ρ D)
    (f : ∀ i, A i ≃ B i) (g : ∀ i, B i ≃ A i)
    (next : ∀ i, Equiv.Perm (A i)) (hnext : ∀ i, (next i).IsCycleOn Set.univ)
    (hadj : ∀ i a, g i (f i a) = next i a)
    (circle : Equiv.Perm (Component A B)) (hcircle : circle.IsCycleOn Set.univ)
    (e : {x // PrincipalGap D x} ≃ Component A B)
    (hlocal : ∀ (s : I × Bool) (x y : {x // PrincipalGap D x}),
      letterPerm ρ s x.val = y.val →
        circle (e x) = polygonGraph f g (e y) ∨
          circle (e y) = polygonGraph f g (e x))
    (horbit : ∀ x y : Ω, ∃ w : FreeGroup I, FreeGroup.lift ρ w x = y) :
    Even (Fintype.card I) := by
  apply even_of_connected_component_configuration f g next hnext hadj circle hcircle
  exact endpoint_gap_connected_of_one_orbit ρ D htrap circle (polygonGraph f g) e hlocal horbit

end FiniteConfiguration

end FnZPositiveCones.PingPong
