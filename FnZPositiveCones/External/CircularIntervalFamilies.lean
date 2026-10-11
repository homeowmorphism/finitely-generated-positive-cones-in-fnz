module

public import FnZPositiveCones.External.CircularComponentEndpoints
public import FnZPositiveCones.External.CircularFGPingPong

@[expose] public section

/-! Actual separated interval families obtained from connected components. -/
namespace FnZPositiveCones.CircularDynamics
universe u

/-- A finite interval family's endpoints in the fixed cut chart. The separation
field is strict, so a component and its right-hand gap have different endpoints. -/
structure CircleIntervalFamily (I : Type u) where
  left : I → ℝ
  right : I → ℝ
  left_pos : ∀ i, 0 < left i
  left_lt_right : ∀ i, left i < right i
  right_lt_one : ∀ i, right i < 1
  separated : ∀ i j, i ≠ j → right i < left j ∨ right j < left i

namespace CircleIntervalFamily
variable {I : Type u} (F : CircleIntervalFamily I)

def arc (i : I) : Set StandardCircle :=
  (fun t : ℝ => (t : StandardCircle)) '' Set.Ioo (F.left i) (F.right i)

theorem closure_arc (i : I) : closure (F.arc i) = closedCircleArc (F.left i) (F.right i) := by
  apply Set.Subset.antisymm
  · exact closure_minimal (Set.image_mono Set.Ioo_subset_Icc_self)
      (isCompact_closedCircleArc _ _).isClosed
  · have h := image_closure_subset_closure_image (AddCircle.continuous_mk' (1 : ℝ))
      (s := Set.Ioo (F.left i) (F.right i))
    rw [closure_Ioo (F.left_lt_right i).ne] at h
    exact h

theorem isOpen_arc (i : I) : IsOpen (F.arc i) :=
  QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo

theorem isConnected_arc (i : I) : IsConnected (F.arc i) :=
  (isConnected_Ioo (F.left_lt_right i)).image _ (AddCircle.continuous_mk' (1 : ℝ)).continuousOn

theorem left_injective : Function.Injective F.left := by
  intro i j hij
  by_contra hne
  rcases F.separated i j hne with h | h
  · exact (not_lt_of_ge (F.left_lt_right i).le) (h.trans_eq hij.symm)
  · exact (not_lt_of_ge (F.left_lt_right j).le) (h.trans_eq hij)

theorem right_injective : Function.Injective F.right := by
  intro i j hij
  by_contra hne
  rcases F.separated i j hne with h | h
  · exact (not_lt_of_ge (F.left_lt_right j).le) (hij.symm ▸ h)
  · exact (not_lt_of_ge (F.left_lt_right i).le) (hij ▸ h)

theorem right_lt_left_of_left_lt {i j : I} (hij : F.left i < F.left j) :
    F.right i < F.left j := by
  rcases F.separated i j (fun he => hij.ne (congrArg F.left he)) with h | h
  · exact h
  · exact False.elim ((lt_irrefl _) ((F.left_lt_right j).trans (h.trans hij)))

/-- Sort the actual components by their left endpoints. -/
noncomputable def enumeration [Fintype I] : Fin (Fintype.card I) ≃ I := by
  let : LinearOrder I := LinearOrder.lift' F.left F.left_injective
  exact (monoEquivOfFin I rfl).toEquiv

theorem enumeration_strictMono [Fintype I] : StrictMono (F.left ∘ F.enumeration) := by
  let : LinearOrder I := LinearOrder.lift' F.left F.left_injective
  exact (monoEquivOfFin I rfl).strictMono

/-- Cyclic successor is the transported rotation of the sorted endpoints. -/
noncomputable def next [Fintype I] : Equiv.Perm I :=
  F.enumeration.permCongrHom (finRotate (Fintype.card I))

theorem next_enumeration [Fintype I] (i : Fin (Fintype.card I)) :
    F.next (F.enumeration i) = F.enumeration (finRotate _ i) := by
  simp [next, Equiv.permCongrHom, Equiv.permCongr_apply]

/-- Rotation is transitive on the whole finite index set, including cardinality
one. This is the exact `IsCycleOn` convention used by the parity theorem. -/
theorem finRotate_isCycleOn (n : ℕ) : (finRotate n).IsCycleOn Set.univ := by
  rcases n with _ | _ | n
  · exact ⟨(finRotate 0).bijOn (by simp), fun x _ => Fin.elim0 x⟩
  · change (finRotate 1).IsCycleOn Set.univ
    rw [finRotate_one]
    exact Equiv.Perm.isCycleOn_one.mpr (fun _ _ _ _ => Subsingleton.elim _ _)
  · have h := (isCycle_finRotate (n := n)).isCycleOn
    have he : {x : Fin (n + 2) | finRotate (n + 2) x ≠ x} = Set.univ := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      exact Equiv.Perm.mem_support.mp (by rw [support_finRotate]; exact Finset.mem_univ x)
    simpa only [he] using h

theorem next_isCycleOn [Fintype I] : F.next.IsCycleOn Set.univ := by
  refine ⟨F.next.bijOn (by simp), ?_⟩
  intro i _ j _
  obtain ⟨k, hk⟩ := (finRotate_isCycleOn (Fintype.card I)).2
    (Set.mem_univ (F.enumeration.symm i)) (Set.mem_univ (F.enumeration.symm j))
  refine ⟨k, ?_⟩
  change ((F.enumeration.permCongrHom (finRotate (Fintype.card I))) ^ k) i = j
  rw [← map_zpow]
  simp only [Equiv.permCongrHom_coe, Equiv.permCongr_apply, hk, Equiv.apply_symm_apply]

end CircleIntervalFamily

theorem endpoints_separated_of_disjoint_closed_arcs {a b u v : ℝ}
    (hab : a ≤ b) (huv : u ≤ v)
    (hdisj : Disjoint (closedCircleArc a b) (closedCircleArc u v)) : b < u ∨ v < a := by
  by_contra hn
  push Not at hn
  apply Set.disjoint_left.mp hdisj
  · exact ⟨max a u, ⟨le_max_left _ _, max_le hab hn.1⟩, rfl⟩
  · exact ⟨max a u, ⟨le_max_right _ _, max_le hn.2 huv⟩, rfl⟩

/-- Extract endpoint data for every actual component of one regular open
domain. The index type is exactly its connected-component quotient. -/
theorem exists_component_intervalFamily {S : Set StandardCircle} (ho : IsOpen S)
    (hreg : interior (closure S) = S) (hzero : 0 ∉ closure S) :
    ∃ F : CircleIntervalFamily (ConnectedComponents ↥S),
      ∀ c, F.arc c = domainComponent S c := by
  classical
  choose a b ha hab hb he hcl using domainComponent_endpoints ho hzero
  let F : CircleIntervalFamily (ConnectedComponents ↥S) :=
    ⟨a, b, ha, hab, hb, fun c d hcd => domainComponent_endpoints_separated hreg hcd
      (ha c) (hab c) (hb c) (ha d) (hab d) (hb d) (he c) (hcl c) (he d) (hcl d)⟩
  exact ⟨F, fun c => (he c).symm⟩

/-- All signed domains are decomposed into their actual components, with one
global family of strictly separated endpoints. Separation within a single
color follows from regular openness; separation between colors follows from
the proved closed-domain separation. -/
theorem finiteNormalizedDomains_exists_intervalFamily {ι : Type u}
    {C : CircularGroupOrder (FreeGroup ι)} {R : CircularRealization C}
    (D : FiniteNormalizedDomains R) :
    ∃ F : CircleIntervalFamily (Σ s : ι × Bool, ConnectedComponents ↥(D.domain s)),
      ∀ s c, F.arc ⟨s, c⟩ = domainComponent (D.domain s) c := by
  classical
  choose F hF using fun s => exists_component_intervalFamily
    (D.isOpen_domain s) (D.regular_domain s) (D.base_avoids s)
  let G : CircleIntervalFamily (Σ s : ι × Bool, ConnectedComponents ↥(D.domain s)) := {
    left := fun i => (F i.1).left i.2
    right := fun i => (F i.1).right i.2
    left_pos := fun i => (F i.1).left_pos i.2
    left_lt_right := fun i => (F i.1).left_lt_right i.2
    right_lt_one := fun i => (F i.1).right_lt_one i.2
    separated := by
      rintro ⟨s, c⟩ ⟨t, d⟩ hne
      dsimp only
      by_cases hst : s = t
      · subst t
        exact (F s).separated c d (fun he => hne (congrArg (Sigma.mk s) he))
      · apply endpoints_separated_of_disjoint_closed_arcs
          ((F s).left_lt_right c).le ((F t).left_lt_right d).le
        rw [← (F s).closure_arc c, ← (F t).closure_arc d, hF s c, hF t d]
        exact (D.separated s t hst).mono
          (closure_mono (domainComponent_subset _ _)) (closure_mono (domainComponent_subset _ _)) }
  exact ⟨G, hF⟩

end FnZPositiveCones.CircularDynamics
