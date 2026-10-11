module

public import FnZPositiveCones.External.CircularDynamicsTraces
public import FnZPositiveCones.External.PingPongGaps

@[expose] public section

/-! Generator-sensitive protected trajectories and their precise endpoint collisions. -/
namespace FnZPositiveCones
namespace CircularDynamics
universe u v
variable {ι : Type u} {X : Type v}

/-- A perturbation of the signed letter `s` affects outputs of `s` edges and
inputs of inverse-`s` edges, and no other points of an itinerary. -/
def IsAffectedSuffix (s : ι × Bool) (u w : List (ι × Bool)) : Prop :=
  (u.head? = some s ∧ u.IsSuffix w) ∨ (PingPong.inverseLetter s :: u).IsSuffix w

theorem IsAffectedSuffix.isSuffix {s : ι × Bool} {u w : List (ι × Bool)}
    (h : IsAffectedSuffix s u w) : u.IsSuffix w := by
  rcases h with ⟨_, h⟩ | h
  · exact h
  · exact (List.suffix_cons _ _).trans h

theorem IsAffectedSuffix.mono {s : ι × Bool} {u v w : List (ι × Bool)}
    (h : IsAffectedSuffix s u v) (hv : v.IsSuffix w) : IsAffectedSuffix s u w := by
  rcases h with ⟨hhead, h⟩ | h
  · exact Or.inl ⟨hhead, h.trans hv⟩
  · exact Or.inr (h.trans hv)

/-- The finite, generator-sensitive protection list. -/
noncomputable def affectedTrace (ρ : ι → Equiv.Perm X) (s : ι × Bool)
    (base : X) (w : List (ι × Bool)) : List X := by
  classical
  exact (w.tails.filter (fun u => IsAffectedSuffix s u w)).map (fun u => evalWord ρ u base)

theorem mem_affectedTrace_iff (ρ : ι → Equiv.Perm X) (s : ι × Bool)
    (base y : X) (w : List (ι × Bool)) :
    y ∈ affectedTrace ρ s base w ↔
      ∃ u, IsAffectedSuffix s u w ∧ evalWord ρ u base = y := by
  classical
  simp only [affectedTrace, List.mem_map, List.mem_filter, List.mem_tails, decide_eq_true_eq]
  constructor
  · rintro ⟨u, ⟨_, hu⟩, he⟩
    exact ⟨u, hu, he⟩
  · rintro ⟨u, hu, he⟩
    exact ⟨u, ⟨hu.isSuffix, hu⟩, he⟩

/-- Only generator-sensitive trajectory points need to be fixed. -/
theorem evalWord_perturb_of_affected_fixed (ρ : ι → Equiv.Perm X) (s : ι × Bool)
    (h : Equiv.Perm X) (base : X) (w : List (ι × Bool))
    (hfix : ∀ u, IsAffectedSuffix s u w → h (evalWord ρ u base) = evalWord ρ u base) :
    evalWord (perturb ρ s h) w base = evalWord ρ w base := by
  induction w with
  | nil => rfl
  | cons t w ih =>
      have ht : evalWord (perturb ρ s h) w base = evalWord ρ w base :=
        ih (fun u hu => hfix u (hu.mono (List.suffix_cons t w)))
      change letterPerm (perturb ρ s h) t (evalWord (perturb ρ s h) w base) = _
      rw [ht]
      by_cases hts : t = s
      · subst t
        rw [letterPerm_perturb_same]
        exact hfix (s :: w) (Or.inl ⟨rfl, ⟨[], rfl⟩⟩)
      · by_cases hti : t = PingPong.inverseLetter s
        · subst t
          have hf := hfix w (Or.inr ⟨[], rfl⟩)
          have hfi : h⁻¹ (evalWord ρ w base) = evalWord ρ w base := by
            apply h.injective
            simpa using hf.symm
          change letterPerm (perturb ρ s h) (s.1, !s.2) (evalWord ρ w base) = _
          rw [letterPerm_perturb_inverse]
          change letterPerm ρ (s.1, !s.2) (h⁻¹ (evalWord ρ w base)) = _
          rw [hfi]
          rfl
        · have hgen : t.1 ≠ s.1 := by
            rcases s with ⟨i, b⟩
            rcases t with ⟨j, c⟩
            intro he
            change j = i at he
            subst j
            cases b <;> cases c <;> simp_all [PingPong.inverseLetter]
          rw [letterPerm_perturb_other ρ s t h hgen]
          rfl

/-- A finite affected-point list is sufficient protection for an entire word. -/
theorem evalWord_perturb_of_affectedTrace_fixed (ρ : ι → Equiv.Perm X) (s : ι × Bool)
    (h : Equiv.Perm X) (base : X) (w : List (ι × Bool))
    (hfix : ∀ y ∈ affectedTrace ρ s base w, h y = y) :
    evalWord (perturb ρ s h) w base = evalWord ρ w base := by
  apply evalWord_perturb_of_affected_fixed
  intro u hu
  exact hfix _ ((mem_affectedTrace_iff _ _ _ _ _).mpr ⟨u, hu, rfl⟩)


/-- Only the affected portion of the proper tail must be protected in order to
move the final selected-generator image exactly by `h`. -/
theorem evalWord_perturb_head_of_affectedTrace_fixed (ρ : ι → Equiv.Perm X)
    (s : ι × Bool) (h : Equiv.Perm X) (base : X) (w : List (ι × Bool))
    (hfix : ∀ y ∈ affectedTrace ρ s base w, h y = y) :
    evalWord (perturb ρ s h) (s :: w) base = h (evalWord ρ (s :: w) base) := by
  change letterPerm (perturb ρ s h) s (evalWord (perturb ρ s h) w base) = _
  rw [evalWord_perturb_of_affectedTrace_fixed ρ s h base w hfix,
    letterPerm_perturb_same]
  rfl

/-- For a free base orbit, affected-point collisions are exactly the indicated
signed suffix configurations. -/
theorem evalWord_mem_affectedTrace_iff (ρ : ι → Equiv.Perm X) (s : ι × Bool)
    (base : X) (hx : Function.Injective (fun g => FreeGroup.lift ρ g base))
    {u w : List (ι × Bool)} (hu : FreeGroup.IsReduced u) (hw : FreeGroup.IsReduced w) :
    evalWord ρ u base ∈ affectedTrace ρ s base w ↔ IsAffectedSuffix s u w := by
  rw [mem_affectedTrace_iff]
  constructor
  · rintro ⟨v, hv, he⟩
    have hred := hw.suffix hv.isSuffix
    have hve : v = u := (evalWord_eq_iff_of_reduced ρ base hx hred hu).mp he
    exact hve ▸ hv
  · intro hu
    exact ⟨u, hu, rfl⟩

/-- A differently colored endpoint is affected only when it is immediately
preceded by the inverse of the changed letter somewhere in the word. -/
theorem different_head_mem_affectedTrace_iff (ρ : ι → Equiv.Perm X)
    (s t : ι × Bool) (base : X)
    (hx : Function.Injective (fun g => FreeGroup.lift ρ g base))
    {u w : List (ι × Bool)} (hu : FreeGroup.IsReduced (t :: u))
    (hw : FreeGroup.IsReduced w) (hst : t ≠ s) :
    evalWord ρ (t :: u) base ∈ affectedTrace ρ s base w ↔
      (PingPong.inverseLetter s :: t :: u).IsSuffix w := by
  rw [evalWord_mem_affectedTrace_iff ρ s base hx hu hw]
  simp [IsAffectedSuffix, hst]


/-- A selected endpoint cannot occur in its own proper affected trace. -/
theorem selected_head_not_mem_proper_affectedTrace (ρ : ι → Equiv.Perm X)
    (s : ι × Bool) (base : X)
    (hx : Function.Injective (fun g => FreeGroup.lift ρ g base))
    (w : List (ι × Bool)) (hw : FreeGroup.IsReduced (s :: w)) :
    evalWord ρ (s :: w) base ∉ affectedTrace ρ s base w := by
  intro he
  have hc := (evalWord_mem_affectedTrace_iff ρ s base hx hw
    (hw.suffix (List.suffix_cons s w))).mp he
  have hn := hc.isSuffix.length_le
  simp only [List.length_cons] at hn
  omega

/-- An endpoint of another color is never itself an affected point of its own
complete reduced word. -/
theorem different_head_not_mem_own_affectedTrace (ρ : ι → Equiv.Perm X)
    (s t : ι × Bool) (base : X)
    (hx : Function.Injective (fun g => FreeGroup.lift ρ g base))
    (w : List (ι × Bool)) (hw : FreeGroup.IsReduced (t :: w)) (hst : t ≠ s) :
    evalWord ρ (t :: w) base ∉ affectedTrace ρ s base (t :: w) := by
  intro he
  have hc := (different_head_mem_affectedTrace_iff ρ s t base hx hw hw hst).mp he
  have hn := hc.length_le
  simp only [List.length_cons] at hn
  omega

/-- Choosing the longer word's head eliminates every endpoint collision except
the precise inverse-edge suffix configuration at the shorter endpoint. -/
theorem affected_traces_endpoint_collision_iff (ρ : ι → Equiv.Perm X)
    (s t : ι × Bool) (base : X)
    (hx : Function.Injective (fun g => FreeGroup.lift ρ g base))
    (w v : List (ι × Bool)) (hw : FreeGroup.IsReduced (s :: w))
    (hv : FreeGroup.IsReduced (t :: v)) (hst : t ≠ s)
    (hlen : (t :: v).length ≤ (s :: w).length) :
    (evalWord ρ (s :: w) base ∉
      affectedTrace ρ s base w ++ affectedTrace ρ s base (t :: v)) ∧
    (evalWord ρ (t :: v) base ∈
      affectedTrace ρ s base w ++ affectedTrace ρ s base (t :: v) ↔
      (PingPong.inverseLetter s :: t :: v).IsSuffix w) := by
  constructor
  · intro he
    rcases List.mem_append.mp he with he | he
    · exact selected_head_not_mem_proper_affectedTrace ρ s base hx w hw he
    · have hc := (evalWord_mem_affectedTrace_iff ρ s base hx hw hv).mp he
      have heq := hc.isSuffix.eq_of_length_le hlen
      exact hst (List.cons.inj heq).1.symm
  · rw [List.mem_append, or_iff_left
      (different_head_not_mem_own_affectedTrace ρ s t base hx v hv hst)]
    exact different_head_mem_affectedTrace_iff ρ s t base hx hv
      (hw.suffix (List.suffix_cons s w)) hst

/-- The remaining endpoint collision forces an actual conjugate prefix. This
is the residual case not removed by generator-sensitive trace protection. -/
theorem affected_collision_conjugate_prefix (s t : ι × Bool)
    (u w : List (ι × Bool)) (hst : t ≠ s)
    (hcollision : IsAffectedSuffix s (t :: u) w) :
    ∃ p, s :: w = (s :: p ++ [PingPong.inverseLetter s]) ++ t :: u := by
  have hs : (PingPong.inverseLetter s :: t :: u).IsSuffix w := by
    simpa [IsAffectedSuffix, hst] using hcollision
  obtain ⟨p, hp⟩ := hs
  refine ⟨p, ?_⟩
  rw [← hp]
  simp only [List.append_assoc, List.cons_append, List.nil_append]

end CircularDynamics
end FnZPositiveCones
