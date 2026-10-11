module

public import FnZPositiveCones.External.CircularDynamicsColors

@[expose] public section

/-! Closure separation itself excludes the free base orbit point from every color. -/
namespace FnZPositiveCones
namespace CircularDynamics
universe u v
variable {ι : Type u} {X : Type v}

/-- Applying the inverse of the first letter leaves either the empty word or a
word whose first letter is not that inverse. This records the cancellation case
omitted by the ordinary color transition lemma. -/
theorem inverse_letterOrbit_mapsTo (ρ : ι → Equiv.Perm X) (base : X) (s : ι × Bool) :
    Set.MapsTo (letterPerm ρ (PingPong.inverseLetter s)) (letterOrbit ρ base s)
      ({base} ∪ ⋃ t : {t : ι × Bool // t ≠ PingPong.inverseLetter s}, letterOrbit ρ base t.val) := by
  rintro x ⟨w, hw, rfl⟩
  have he : letterPerm ρ (PingPong.inverseLetter s) (evalWord ρ (s :: w) base) =
      evalWord ρ w base := by
    change letterPerm ρ (PingPong.inverseLetter s) (letterPerm ρ s (evalWord ρ w base)) = _
    rw [PingPong.letterPerm_inverseLetter]
    simp
  rw [he]
  cases w with
  | nil => exact Or.inl rfl
  | cons t w =>
      right
      refine Set.mem_iUnion.mpr ⟨⟨t, PingPong.reduced_head_ne_inverse hw⟩, w, ?_, rfl⟩
      exact (FreeGroup.isReduced_cons_cons.mp hw).2

/-- For a finite generating alphabet, disjoint actual color closures cannot
contain the free basepoint. This discharges a separate-looking domain premise
from the same precise closure-separation hypothesis. -/
theorem base_not_mem_colorClosures_of_separated [Finite ι] [TopologicalSpace X] [T1Space X]
    (ρ : ι → Equiv.Perm X) (base : X)
    (hx : Function.Injective (fun g => FreeGroup.lift ρ g base))
    (hc : ∀ s, Continuous (letterPerm ρ s))
    (hsep : ∀ s t, s ≠ t → Disjoint (closure (letterOrbit ρ base s))
      (closure (letterOrbit ρ base t))) (s : ι × Bool) :
    base ∉ closure (letterOrbit ρ base s) := by
  intro hb
  have ht := (inverse_letterOrbit_mapsTo ρ base s).closure (hc (PingPong.inverseLetter s)) hb
  rw [closure_union, closure_singleton, closure_iUnion_of_finite] at ht
  have hpoint : letterPerm ρ (PingPong.inverseLetter s) base ∈
      letterOrbit ρ base (PingPong.inverseLetter s) :=
    ⟨[], FreeGroup.IsReduced.singleton, rfl⟩
  rcases ht with ht | ht
  · exact base_not_mem_letterOrbit ρ base hx (PingPong.inverseLetter s) (by simpa only [Set.mem_singleton_iff.mp ht] using hpoint)
  · obtain ⟨t, ht⟩ := Set.mem_iUnion.mp ht
    exact Set.disjoint_left.mp (hsep t.val (PingPong.inverseLetter s) t.property) ht
      (subset_closure hpoint)

end CircularDynamics
end FnZPositiveCones
