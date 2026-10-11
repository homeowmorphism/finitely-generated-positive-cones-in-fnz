module

public import FnZPositiveCones.External.CircularDynamicsColors
public import Mathlib.Topology.DerivedSet
public import Mathlib.Topology.DiscreteSubset

@[expose] public section

/-! Last-letter orbit sets and their genuine invariant accumulation sets. -/
namespace FnZPositiveCones
namespace CircularDynamics
universe u v
variable {ι : Type u} {X : Type v}

/-- Actual orbit points whose reduced word ends in the specified signed letter. -/
def lastLetterOrbit (ρ : ι → Equiv.Perm X) (base : X) (t : ι × Bool) : Set X :=
  {x | ∃ w, FreeGroup.IsReduced (w ++ [t]) ∧ evalWord ρ (w ++ [t]) base = x}

/-- Left multiplication changes the last letter only when the entire word
cancels to identity. The sole exceptional image point is the basepoint. -/
theorem lastLetterOrbit_signed_mapsTo (ρ : ι → Equiv.Perm X) (base : X)
    (s t : ι × Bool) :
    Set.MapsTo (letterPerm ρ s) (lastLetterOrbit ρ base t)
      (lastLetterOrbit ρ base t ∪ {base}) := by
  classical
  rintro x ⟨w, hw, rfl⟩
  cases w with
  | nil =>
      by_cases he : t = PingPong.inverseLetter s
      · right
        change letterPerm ρ s (letterPerm ρ t base) = base
        rw [he, PingPong.letterPerm_inverseLetter]
        exact (letterPerm ρ s).apply_symm_apply base
      · left
        exact ⟨[s], reduced_cons_of_ne_inverse FreeGroup.IsReduced.singleton he, rfl⟩
  | cons a w =>
      by_cases he : a = PingPong.inverseLetter s
      · left
        refine ⟨w, hw.tail, ?_⟩
        change evalWord ρ (w ++ [t]) base =
          letterPerm ρ s (letterPerm ρ a (evalWord ρ (w ++ [t]) base))
        rw [he, PingPong.letterPerm_inverseLetter]
        exact ((letterPerm ρ s).apply_symm_apply _).symm
      · left
        exact ⟨s :: a :: w, reduced_cons_of_ne_inverse hw he, rfl⟩

/-- Every last-letter orbit set is infinite when the marked full orbit is free.
The witnesses are all positive powers of the same signed letter. -/
theorem lastLetterOrbit_infinite (ρ : ι → Equiv.Perm X) (base : X)
    (hx : Function.Injective (fun g => FreeGroup.lift ρ g base)) (t : ι × Bool) :
    (lastLetterOrbit ρ base t).Infinite := by
  classical
  let f : ℕ → X := fun n => evalWord ρ (List.replicate (n + 1) t) base
  have hf : Function.Injective f := by
    intro n m he
    have he' : FreeGroup.mk (List.replicate (n + 1) t) =
        FreeGroup.mk (List.replicate (m + 1) t) := hx (by
      simpa only [lift_mk_apply] using he)
    have hn := congrArg (fun g : FreeGroup ι => g.toWord.length) he'
    simpa only [FreeGroup.toWord_mk, FreeGroup.reduce_replicate, List.length_replicate,
      Nat.add_right_cancel_iff] using hn
  have hsub : Set.range f ⊆ lastLetterOrbit ρ base t := by
    rintro _ ⟨n, rfl⟩
    refine ⟨List.replicate n t, ?_, ?_⟩
    · apply FreeGroup.IsReduced.of_reduce_eq
      rw [← List.replicate_succ']
      exact FreeGroup.reduce_replicate _ _
    · rw [← List.replicate_succ']
  exact (Set.infinite_range_of_injective hf).mono hsub

/-- Last-letter sets consist of points in the original marked orbit. -/
theorem lastLetterOrbit_subset_orbit (ρ : ι → Equiv.Perm X) (base : X)
    (t : ι × Bool) :
    lastLetterOrbit ρ base t ⊆ Set.range (fun g => FreeGroup.lift ρ g base) := by
  rintro x ⟨w, _, rfl⟩
  exact ⟨FreeGroup.mk (w ++ [t]), lift_mk_apply _ _ _⟩

section Topology
variable [TopologicalSpace X] [T1Space X]

/-- Removing or adding the single cancellation exception does not alter the
accumulation set. -/
theorem derivedSet_singleton_eq_empty (x : X) : derivedSet ({x} : Set X) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro y hy
  exact Set.Infinite.of_accPt hy (Set.finite_singleton x)

omit [T1Space X] in
/-- Every last-letter accumulation set lies in the accumulation set of the
full marked orbit. -/
theorem lastLetterOrbit_derived_subset_orbit (ρ : ι → Equiv.Perm X) (base : X)
    (t : ι × Bool) :
    derivedSet (lastLetterOrbit ρ base t) ⊆
      derivedSet (Set.range (fun g => FreeGroup.lift ρ g base)) :=
  derivedSet_mono _ _ (lastLetterOrbit_subset_orbit ρ base t)

/-- The invariant accumulation sets are closed in the actual ambient topology. -/
theorem lastLetterOrbit_derived_isClosed (ρ : ι → Equiv.Perm X) (base : X)
    (t : ι × Bool) : IsClosed (derivedSet (lastLetterOrbit ρ base t)) :=
  isClosed_derivedSet _

/-- A signed generator preserves the genuine accumulation set of each last
letter set; this is proved from its action on words. -/
theorem lastLetterOrbit_derived_signed_mapsTo (ρ : ι → Equiv.Perm X) (base : X)
    (s t : ι × Bool) (hc : Continuous (letterPerm ρ s)) :
    Set.MapsTo (letterPerm ρ s) (derivedSet (lastLetterOrbit ρ base t))
      (derivedSet (lastLetterOrbit ρ base t)) := by
  intro x hx
  have hm := hc.image_derivedSet (letterPerm ρ s).injective ⟨x, hx, rfl⟩
  have hs : letterPerm ρ s '' lastLetterOrbit ρ base t ⊆ lastLetterOrbit ρ base t ∪ {base} :=
    Set.image_subset_iff.mpr (lastLetterOrbit_signed_mapsTo ρ base s t)
  have hd := derivedSet_mono _ _ hs hm
  simpa only [derivedSet_union, derivedSet_singleton_eq_empty, Set.union_empty] using hd

/-- Every group element preserves each last-letter accumulation set, not just
the total orbit closure. -/
theorem lastLetterOrbit_derived_invariant (ρ : ι → Equiv.Perm X) (base : X)
    (hc : ∀ s, Continuous (letterPerm ρ s)) (t : ι × Bool) (g : FreeGroup ι) :
    FreeGroup.lift ρ g '' derivedSet (lastLetterOrbit ρ base t) =
      derivedSet (lastLetterOrbit ρ base t) := by
  classical
  have hword : ∀ w, Set.MapsTo (evalWord ρ w) (derivedSet (lastLetterOrbit ρ base t))
      (derivedSet (lastLetterOrbit ρ base t)) := by
    intro w
    induction w with
    | nil => exact fun _ hx => hx
    | cons s w ih =>
      intro x hx
      exact lastLetterOrbit_derived_signed_mapsTo ρ base s t (hc s) (ih hx)
  have hmap (k : FreeGroup ι) : Set.MapsTo (FreeGroup.lift ρ k)
      (derivedSet (lastLetterOrbit ρ base t)) (derivedSet (lastLetterOrbit ρ base t)) := by
    intro x hx
    rw [← FreeGroup.mk_toWord (x := k), lift_mk_apply]
    exact hword k.toWord hx
  apply Set.Subset.antisymm
  · rintro x ⟨y, hy, rfl⟩
    exact hmap g hy
  · intro x hx
    refine ⟨FreeGroup.lift ρ g⁻¹ x, hmap g⁻¹ hx, ?_⟩
    rw [map_inv]
    exact (FreeGroup.lift ρ g).apply_symm_apply x

omit [T1Space X] in
/-- Compactness and the free orbit prove nonemptiness of every last-letter
accumulation set; no density or minimality assumption is used. -/
theorem lastLetterOrbit_derived_nonempty [CompactSpace X]
    (ρ : ι → Equiv.Perm X) (base : X)
    (hx : Function.Injective (fun g => FreeGroup.lift ρ g base)) (t : ι × Bool) :
    (derivedSet (lastLetterOrbit ρ base t)).Nonempty :=
  (lastLetterOrbit_infinite ρ base hx t).exists_accPt_principal

end Topology
end CircularDynamics
end FnZPositiveCones
