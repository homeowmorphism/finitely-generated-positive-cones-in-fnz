module

public import FnZPositiveCones.External.CircularComponentConfiguration

@[expose] public section

/-! The actual orbit closure is inside the open domains except at the basepoint. -/
namespace FnZPositiveCones.FiniteNormalizedDomains
open CircularDynamics
universe u
variable {ι : Type u} {C : CircularGroupOrder (FreeGroup ι)}
    {R : CircularRealization C} (D : FiniteNormalizedDomains R)

/-- Reduced first-letter orbit points lie in the corresponding actual domain. -/
theorem evalWord_mem_domain (s : ι × Bool) (w : List (ι × Bool))
    (hw : FreeGroup.IsReduced (s :: w)) :
    evalWord (realizationGenerators R) (s :: w) 0 ∈ D.domain s := by
  induction w generalizing s with
  | nil =>
    rw [← D.image_domain s]
    exact ⟨0, D.base_avoids _, rfl⟩
  | cons t w ih =>
    have ht := ih t (FreeGroup.isReduced_cons_cons.mp hw).2
    have hts := PingPong.reduced_head_ne_inverse hw
    rw [← D.image_domain s]
    refine ⟨evalWord (realizationGenerators R) (t :: w) 0, ?_, rfl⟩
    exact fun hbad => Set.disjoint_left.mp (D.separated t (PingPong.inverseLetter s) hts)
      (subset_closure ht) hbad

theorem letterOrbit_subset_domain (s : ι × Bool) :
    letterOrbit (realizationGenerators R) 0 s ⊆ D.domain s := by
  rintro _ ⟨w, hw, rfl⟩
  exact D.evalWord_mem_domain s w hw

/-- Even the entire first-letter closure is contained in the open domain.
Cancellation of the first letter puts its inverse image among the other closed
domains or at the basepoint, where the exact image equation applies. -/
theorem closure_letterOrbit_subset_domain [Finite ι] (s : ι × Bool) :
    closure (letterOrbit (realizationGenerators R) 0 s) ⊆ D.domain s := by
  let ρ := realizationGenerators R
  let invs := PingPong.inverseLetter s
  let J := {t : ι × Bool // t ≠ invs}
  let T : Set StandardCircle := {0} ∪ ⋃ t : J, closure (D.domain t.val)
  have hclosed : IsClosed T := isClosed_singleton.union
    (isClosed_iUnion_of_finite fun _ => isClosed_closure)
  have hmap : Set.MapsTo (letterPerm ρ invs) (letterOrbit ρ 0 s) T := by
    rintro _ ⟨w, hw, rfl⟩
    have he : letterPerm ρ invs (evalWord ρ (s :: w) 0) = evalWord ρ w 0 := by
      change (letterPerm ρ (PingPong.inverseLetter s)) (letterPerm ρ s (evalWord ρ w 0)) = _
      rw [PingPong.letterPerm_inverseLetter]
      exact (letterPerm ρ s).symm_apply_apply _
    rw [he]
    cases w with
    | nil => exact Or.inl rfl
    | cons t w =>
      have ht : t ≠ invs := PingPong.reduced_head_ne_inverse hw
      exact Or.inr (Set.mem_iUnion.mpr ⟨⟨t, ht⟩, subset_closure
        (D.evalWord_mem_domain t w (FreeGroup.isReduced_cons_cons.mp hw).2)⟩)
  have hc : Continuous (letterPerm ρ invs) := by
    rw [show letterPerm ρ invs = R.action (FreeGroup.mk [invs]) from realizationGenerators_letter R invs]
    exact R.action_continuous _
  intro x hx
  have hy := hmap.closure hc hx
  rw [hclosed.closure_eq] at hy
  have hnot : letterPerm ρ invs x ∉ closure (D.domain invs) := by
    rcases hy with he | hy
    · exact he ▸ D.base_avoids invs
    · obtain ⟨t, ht⟩ := Set.mem_iUnion.mp hy
      exact fun hbad => Set.disjoint_left.mp (D.separated t.val invs t.property) ht hbad
  rw [← D.image_domain s]
  refine ⟨letterPerm ρ invs x, hnot, ?_⟩
  change letterPerm ρ s (letterPerm ρ (PingPong.inverseLetter s) x) = x
  rw [PingPong.letterPerm_inverseLetter]
  exact (letterPerm ρ s).apply_symm_apply _

/-- Every point of the tight orbit closure except the base lies in an open
domain, so the finite domain frontiers cannot be orbit-limit points. -/
theorem orbitClosure_subset_base_union_domains [Finite ι] :
    closure (Set.range (fun g : FreeGroup ι => R.action g 0)) ⊆ {0} ∪ ⋃ s, D.domain s := by
  rw [← realizationGenerators_lift R, orbitClosure_eq_base_union_colorClosures]
  exact Set.union_subset_union_right _ (Set.iUnion_mono fun s => D.closure_letterOrbit_subset_domain s)

/-- Domain frontiers avoid the entire orbit closure. -/
theorem frontier_disjoint_orbitClosure [Finite ι] (s : ι × Bool) :
    Disjoint (frontier (D.domain s)) (closure (Set.range (fun g : FreeGroup ι => R.action g 0))) := by
  apply Set.disjoint_left.mpr
  intro x hx hxK
  have hxcl := frontier_subset_closure hx
  have hxnot : x ∉ D.domain s := by
    have h : x ∉ interior (D.domain s) := hx.2
    rwa [(D.isOpen_domain s).interior_eq] at h
  rcases D.orbitClosure_subset_base_union_domains hxK with hx0 | hxD
  · exact D.base_avoids s (hx0 ▸ hxcl)
  · obtain ⟨t, ht⟩ := Set.mem_iUnion.mp hxD
    by_cases hst : s = t
    · exact hxnot (hst.symm ▸ ht)
    · exact Set.disjoint_left.mp (D.separated s t hst) hxcl (subset_closure ht)

end FnZPositiveCones.FiniteNormalizedDomains
