module

public import FnZPositiveCones.External.CircularDynamicsTraces
public import FnZPositiveCones.External.PingPongGaps

@[expose] public section

/-! Actual first-letter orbit colors and their transport to orbit closures. -/
namespace FnZPositiveCones
namespace CircularDynamics
universe u v
variable {ι : Type u} {X : Type v}

/-- Orbit points represented by a nonempty reduced word with prescribed first
signed letter. -/
def letterOrbit (ρ : ι → Equiv.Perm X) (base : X) (s : ι × Bool) : Set X :=
  {x | ∃ w, FreeGroup.IsReduced (s :: w) ∧ evalWord ρ (s :: w) base = x}

theorem letterOrbit_nonempty (ρ : ι → Equiv.Perm X) (base : X) (s : ι × Bool) :
    (letterOrbit ρ base s).Nonempty :=
  ⟨evalWord ρ [s] base, [], FreeGroup.IsReduced.singleton, rfl⟩

theorem reduced_cons_of_ne_inverse {s t : ι × Bool} {w : List (ι × Bool)}
    (hw : FreeGroup.IsReduced (t :: w)) (hst : t ≠ PingPong.inverseLetter s) :
    FreeGroup.IsReduced (s :: t :: w) := by
  apply FreeGroup.isReduced_cons_cons.mpr
  refine ⟨?_, hw⟩
  rcases s with ⟨i, b⟩
  rcases t with ⟨j, c⟩
  intro hij
  change i = j at hij
  subst j
  cases b <;> cases c <;> simp_all [PingPong.inverseLetter]

/-- Reduced first-letter colors have the exact ping-pong transition on orbit
points whenever the applied letter does not cancel the first letter. -/
theorem letterOrbit_mapsTo (ρ : ι → Equiv.Perm X) (base : X) (s t : ι × Bool)
    (hst : t ≠ PingPong.inverseLetter s) :
    Set.MapsTo (letterPerm ρ s) (letterOrbit ρ base t) (letterOrbit ρ base s) := by
  rintro x ⟨w, hw, rfl⟩
  exact ⟨t :: w, reduced_cons_of_ne_inverse hw hst, rfl⟩

/-- Different first letters give disjoint actual orbit sets when the orbit is
free. This makes no assertion about their closures. -/
theorem letterOrbit_disjoint (ρ : ι → Equiv.Perm X) (base : X)
    (hx : Function.Injective (fun g => FreeGroup.lift ρ g base))
    {s t : ι × Bool} (hst : s ≠ t) :
    Disjoint (letterOrbit ρ base s) (letterOrbit ρ base t) := by
  apply Set.disjoint_left.mpr
  rintro x ⟨w, hw, hwx⟩ ⟨z, hz, hzx⟩
  have he := (evalWord_eq_iff_of_reduced ρ base hx hw hz).mp (hwx.trans hzx.symm)
  exact hst (List.cons.inj he).1

theorem base_not_mem_letterOrbit (ρ : ι → Equiv.Perm X) (base : X)
    (hx : Function.Injective (fun g => FreeGroup.lift ρ g base)) (s : ι × Bool) :
    base ∉ letterOrbit ρ base s := by
  rintro ⟨w, hw, he⟩
  have hn : s :: w = [] := (evalWord_eq_iff_of_reduced ρ base hx hw FreeGroup.IsReduced.nil).mp he
  simp at hn

/-- Every orbit point is either the basepoint or belongs to a first-letter color. -/
theorem orbit_eq_base_union_letterOrbit (ρ : ι → Equiv.Perm X) (base : X) :
    Set.range (fun g => FreeGroup.lift ρ g base) = {base} ∪ ⋃ s, letterOrbit ρ base s := by
  classical
  ext x
  constructor
  · rintro ⟨g, rfl⟩
    have hg : FreeGroup.lift ρ g base = evalWord ρ g.toWord base := by
      rw [← lift_mk_apply, FreeGroup.mk_toWord]
    cases hw : g.toWord with
    | nil => left; simp [hg, hw, evalWord]
    | cons s w =>
      right
      apply Set.mem_iUnion.mpr
      refine ⟨s, w, ?_, ?_⟩
      · simpa only [hw] using (FreeGroup.isReduced_toWord (x := g))
      · simpa only [hw] using hg.symm
  · rintro (rfl | hx)
    · exact ⟨1, by simp⟩
    · obtain ⟨s, w, hw, rfl⟩ := Set.mem_iUnion.mp hx
      exact ⟨FreeGroup.mk (s :: w), lift_mk_apply _ _ _⟩

section Topology
variable [TopologicalSpace X]

/-- Continuity transports the actual closures with the same color rule. -/
theorem closure_letterOrbit_mapsTo (ρ : ι → Equiv.Perm X) (base : X) (s t : ι × Bool)
    (hc : Continuous (letterPerm ρ s)) (hst : t ≠ PingPong.inverseLetter s) :
    Set.MapsTo (letterPerm ρ s) (closure (letterOrbit ρ base t))
      (closure (letterOrbit ρ base s)) :=
  (letterOrbit_mapsTo ρ base s t hst).closure hc

/-- The orbit closure is covered by the basepoint and the finitely many actual
color closures. Disjointness of those closures remains a separate obligation. -/
theorem orbitClosure_eq_base_union_colorClosures [Finite ι] [T1Space X]
    (ρ : ι → Equiv.Perm X) (base : X) :
    closure (Set.range (fun g => FreeGroup.lift ρ g base)) =
      {base} ∪ ⋃ s, closure (letterOrbit ρ base s) := by
  rw [orbit_eq_base_union_letterOrbit, closure_union, closure_singleton,
    closure_iUnion_of_finite]

end Topology
end CircularDynamics
end FnZPositiveCones
