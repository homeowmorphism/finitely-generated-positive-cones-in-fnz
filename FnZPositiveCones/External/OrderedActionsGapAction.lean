module

public import FnZPositiveCones.External.OrderedActionsCircleGaps

@[expose] public section

namespace FnZPositiveCones.CircularRealization
universe u
variable {G : Type u} [Group G] {C : CircularGroupOrder G} (R : CircularRealization C)

/-- Actual connected components of the complement of the circular orbit closure. -/
def ComplementaryGap := {J : Set (AddCircle (1 : ℝ)) //
  ∃ x : AddCircle (1 : ℝ), x ∉ closure (Set.range (fun g => R.action g 0)) ∧
    connectedComponentIn (closure (Set.range (fun g => R.action g 0)))ᶜ x = J}

/-- The component following each marked orbit point. -/
noncomputable def gapLabel {a : G} (ha : C.IsSuccessor a) (g : G) : R.ComplementaryGap :=
  ⟨R.circleGap a g, by
    obtain ⟨x, hx⟩ := R.circleGap_nonempty ha g
    exact ⟨x, fun hh => Set.disjoint_left.mp (R.circleGap_disjoint_orbitClosure ha g) hx hh,
      R.circleGap_eq_component ha g hx⟩⟩

theorem gapLabel_injective {a : G} (ha : C.IsSuccessor a) :
    Function.Injective (R.gapLabel ha) := by
  intro g h he
  have he' : R.circleGap a g = R.circleGap a h := congrArg Subtype.val he
  by_contra hne
  obtain ⟨x, hx⟩ := R.circleGap_nonempty ha g
  exact Set.disjoint_left.mp (R.circleGap_disjoint ha hne) hx (he' ▸ hx)

theorem gapLabel_surjective {a : G} (ha : C.IsSuccessor a) :
    Function.Surjective (R.gapLabel ha) := by
  rintro ⟨J, x, hx, he⟩
  obtain ⟨g, hg⟩ := R.exists_mem_circleGap ha hx
  refine ⟨g, Subtype.ext ?_⟩
  exact (R.circleGap_eq_component ha g hg).symm.trans he

/-- The group labels all actual gaps bijectively, without a transitivity assumption. -/
noncomputable def gapEquiv {a : G} (ha : C.IsSuccessor a) : G ≃ R.ComplementaryGap :=
  Equiv.ofBijective (R.gapLabel ha) ⟨R.gapLabel_injective ha, R.gapLabel_surjective ha⟩

noncomputable def gapAction {a : G} (ha : C.IsSuccessor a) :
    G →* Equiv.Perm R.ComplementaryGap :=
  (R.gapEquiv ha).permCongrHom.toMonoidHom.comp (MulAction.toPermHom G G)

theorem gapAction_label {a : G} (ha : C.IsSuccessor a) (g h : G) :
    R.gapAction ha g (R.gapLabel ha h) = R.gapLabel ha (g * h) := by
  change R.gapEquiv ha (g * (R.gapEquiv ha).symm (R.gapEquiv ha h)) = _
  rw [Equiv.symm_apply_apply]
  rfl

/-- The permutation action is the action on the actual underlying circle components. -/
theorem gapAction_transport {a : G} (ha : C.IsSuccessor a) (g : G) (J : R.ComplementaryGap) :
    (R.gapAction ha g J).val = R.action g '' J.val := by
  obtain ⟨h, rfl⟩ := R.gapLabel_surjective ha J
  rw [R.gapAction_label ha]
  exact R.circleGap_transport a g h

theorem gapAction_transitive {a : G} (ha : C.IsSuccessor a) (J K : R.ComplementaryGap) :
    ∃ g : G, R.gapAction ha g J = K := by
  obtain ⟨h, rfl⟩ := R.gapLabel_surjective ha J
  obtain ⟨k, rfl⟩ := R.gapLabel_surjective ha K
  refine ⟨k * h⁻¹, ?_⟩
  rw [R.gapAction_label ha, inv_mul_cancel_right]

end FnZPositiveCones.CircularRealization
