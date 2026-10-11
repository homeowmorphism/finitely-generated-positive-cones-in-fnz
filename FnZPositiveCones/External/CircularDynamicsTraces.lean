module

public import FnZPositiveCones.External.CircularDynamicsSeparation

@[expose] public section

/-! Exact endpoint-collision checks for reduced free-group trajectories. -/
namespace FnZPositiveCones
namespace CircularDynamics
universe u v
variable {ι : Type u} {X : Type v}

/-- Every point in a word trace is the endpoint of an actual suffix. -/
theorem mem_wordTrace_iff (ρ : ι → Equiv.Perm X) (x y : X) (w : List (ι × Bool)) :
    y ∈ wordTrace ρ x w ↔ ∃ v, v.IsSuffix w ∧ evalWord ρ v x = y := by
  constructor
  · intro hy
    induction w with
    | nil =>
        simp only [wordTrace, List.mem_singleton] at hy
        exact ⟨[], ⟨[], rfl⟩, hy.symm⟩
    | cons s w ih =>
        rcases List.mem_cons.mp hy with he | he
        · exact ⟨s :: w, ⟨[], rfl⟩, he.symm⟩
        · obtain ⟨v, hv, he⟩ := ih he
          refine ⟨v, hv.trans ?_, he⟩
          exact ⟨[s], rfl⟩
  · rintro ⟨v, hv, rfl⟩
    exact wordTrace_subset_of_isSuffix ρ x hv _ (evalWord_mem_wordTrace ρ x v)

/-- In a free base orbit, two reduced words have the same endpoint only when
those words themselves agree. -/
theorem evalWord_eq_iff_of_reduced (ρ : ι → Equiv.Perm X) (x : X)
    (hx : Function.Injective (fun g => FreeGroup.lift ρ g x))
    {v w : List (ι × Bool)} (hv : FreeGroup.IsReduced v) (hw : FreeGroup.IsReduced w) :
    evalWord ρ v x = evalWord ρ w x ↔ v = w := by
  classical
  constructor
  · intro he
    have hg : FreeGroup.mk v = FreeGroup.mk w := hx (by simpa only [lift_mk_apply] using he)
    have ht := congrArg FreeGroup.toWord hg
    simpa only [FreeGroup.toWord_mk, hv.reduce_eq, hw.reduce_eq] using ht
  · rintro rfl
    rfl

/-- Endpoint coincidences inside a reduced trajectory are exactly suffix relations.
This makes the endpoint exception to the empty-open-interval argument explicit. -/
theorem evalWord_mem_trace_iff_isSuffix (ρ : ι → Equiv.Perm X) (x : X)
    (hx : Function.Injective (fun g => FreeGroup.lift ρ g x))
    {v w : List (ι × Bool)} (hv : FreeGroup.IsReduced v) (hw : FreeGroup.IsReduced w) :
    evalWord ρ v x ∈ wordTrace ρ x w ↔ v.IsSuffix w := by
  rw [mem_wordTrace_iff]
  constructor
  · rintro ⟨r, hr, he⟩
    have hrred : FreeGroup.IsReduced r := hw.suffix hr
    have her : r = v := (evalWord_eq_iff_of_reduced ρ x hx hrred hv).mp he
    exact her ▸ hr
  · intro hvw
    exact ⟨v, hvw, rfl⟩

/-- The endpoint of a nonempty reduced word never lies in its own proper trace. -/
theorem evalWord_not_mem_proper_trace (ρ : ι → Equiv.Perm X) (x : X)
    (hx : Function.Injective (fun g => FreeGroup.lift ρ g x))
    (s : ι × Bool) (w : List (ι × Bool)) (hw : FreeGroup.IsReduced (s :: w)) :
    evalWord ρ (s :: w) x ∉ wordTrace ρ x w := by
  intro he
  have hws : w.IsSuffix (s :: w) := ⟨[s], rfl⟩
  have hs := (evalWord_mem_trace_iff_isSuffix ρ x hx hw (hw.suffix hws)).mp he
  have hlen := hs.length_le
  simp only [List.length_cons] at hlen
  omega

/-- When the two reduced words are suffix-incomparable, neither chosen endpoint
occurs in either proper trajectory. Together with open-interval adjacency this
justifies a supported perturbation avoiding the complete proper traces. -/
theorem proper_traces_avoid_endpoints (ρ : ι → Equiv.Perm X) (x : X)
    (hx : Function.Injective (fun g => FreeGroup.lift ρ g x))
    (s t : ι × Bool) (w v : List (ι × Bool))
    (hw : FreeGroup.IsReduced (s :: w)) (hv : FreeGroup.IsReduced (t :: v))
    (hsv : ¬(s :: w).IsSuffix (t :: v)) (htw : ¬(t :: v).IsSuffix (s :: w)) :
    (evalWord ρ (s :: w) x ∉ wordTrace ρ x w ++ wordTrace ρ x v) ∧
    (evalWord ρ (t :: v) x ∉ wordTrace ρ x w ++ wordTrace ρ x v) := by
  have hws : w.IsSuffix (s :: w) := ⟨[s], rfl⟩
  have hvs : v.IsSuffix (t :: v) := ⟨[t], rfl⟩
  constructor
  · intro he
    rcases List.mem_append.mp he with he | he
    · exact evalWord_not_mem_proper_trace ρ x hx s w hw he
    · exact hsv (((evalWord_mem_trace_iff_isSuffix ρ x hx hw (hv.suffix hvs)).mp he).trans hvs)
  · intro he
    rcases List.mem_append.mp he with he | he
    · exact htw (((evalWord_mem_trace_iff_isSuffix ρ x hx hv (hw.suffix hws)).mp he).trans hws)
    · exact evalWord_not_mem_proper_trace ρ x hx t v hv he

end CircularDynamics
end FnZPositiveCones
