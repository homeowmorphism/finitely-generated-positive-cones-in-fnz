module

public import FnZPositiveCones.External.OrderedActionsCircleGaps
public import FnZPositiveCones.External.CircularDynamicsObstruction

@[expose] public section

/-! Finite orbit cutsets separate closed first-letter colors. The cutset
condition below is purely order-theoretic; no perturbation theorem is assumed. -/

namespace FnZPositiveCones.CircularDynamics

/-- A closed set meeting every interval between two sets contains every common
point of their closures. -/
theorem closure_inter_subset_closed_separators (A B F : Set ℝ)
    (hF : IsClosed F)
    (hsep : ∀ a ∈ A, ∀ b ∈ B, ∃ c ∈ F, c ∈ Set.uIcc a b) :
    closure A ∩ closure B ⊆ F := by
  rintro x ⟨hxA, hxB⟩
  by_contra hxF
  obtain ⟨l, r, hxlr, hlr⟩ := mem_nhds_iff_exists_Ioo_subset.mp
    (hF.isOpen_compl.mem_nhds hxF)
  obtain ⟨a, ha, haA⟩ := mem_closure_iff.mp hxA (Set.Ioo l r) isOpen_Ioo hxlr
  obtain ⟨b, hb, hbB⟩ := mem_closure_iff.mp hxB (Set.Ioo l r) isOpen_Ioo hxlr
  obtain ⟨c, hcF, hc⟩ := hsep a haA b hbB
  have hclr : c ∈ Set.Ioo l r := by
    rcases le_total a b with hab | hba
    · rw [Set.uIcc_of_le hab] at hc
      exact ⟨ha.1.trans_le hc.1, hc.2.trans_lt hb.2⟩
    · rw [Set.uIcc_of_ge hba] at hc
      exact ⟨hb.1.trans_le hc.1, hc.2.trans_lt ha.2⟩
  exact hlr hclr hcF

/-- An isolated point of the union of two disjoint sets cannot be a common
closure point. -/
theorem not_mem_both_closures_of_isolated {X : Type*} [TopologicalSpace X]
    (A B : Set X) (hAB : Disjoint A B) (x : X)
    (hi : ∃ U, IsOpen U ∧ x ∈ U ∧ U ∩ (A ∪ B) ⊆ {x}) :
    ¬ (x ∈ closure A ∧ x ∈ closure B) := by
  rintro ⟨hxA, hxB⟩
  obtain ⟨U, hU, hxU, hsing⟩ := hi
  obtain ⟨a, haU, haA⟩ := mem_closure_iff.mp hxA U hU hxU
  obtain ⟨b, hbU, hbB⟩ := mem_closure_iff.mp hxB U hU hxU
  have ha : a = x := hsing ⟨haU, Or.inl haA⟩
  have hb : b = x := hsing ⟨hbU, Or.inr hbB⟩
  exact Set.disjoint_left.mp hAB (ha ▸ haA) (hb ▸ hbB)

theorem circleCoordinate_injective : Function.Injective circleCoordinate := by
  intro x y h
  exact (AddCircle.equivIco (1 : ℝ) 0).injective (Subtype.ext h)

theorem circleCoordinate_continuousAt {x : AddCircle (1 : ℝ)} (hx : x ≠ 0) :
    ContinuousAt circleCoordinate x := by
  exact continuousAt_subtype_val.comp
    (AddCircle.continuousAt_equivIco (1 : ℝ) 0 (by simpa using hx))

/-- Finite orbit cutsets and isolation of their points imply actual separation
of the circle closures. Both the cutset condition and isolation are explicit. -/
theorem disjoint_closures_circle_of_finite_separators
    (A B F : Set (AddCircle (1 : ℝ))) (hF : F.Finite) (hAB : Disjoint A B)
    (hsep : ∀ a ∈ A, ∀ b ∈ B, ∃ c ∈ F,
      circleCoordinate c ∈ Set.uIcc (circleCoordinate a) (circleCoordinate b))
    (hisolated : ∀ x ∈ insert 0 F,
      ∃ U, IsOpen U ∧ x ∈ U ∧ U ∩ (A ∪ B) ⊆ {x}) :
    Disjoint (closure A) (closure B) := by
  apply Set.disjoint_left.mpr
  intro x hxA hxB
  have hxF : x ∈ insert 0 F := by
    by_cases hx0 : x = 0
    · exact Or.inl hx0
    · have hc := circleCoordinate_continuousAt hx0
      have hA : circleCoordinate x ∈ closure (circleCoordinate '' A) :=
        mem_closure_image hc hxA
      have hB : circleCoordinate x ∈ closure (circleCoordinate '' B) :=
        mem_closure_image hc hxB
      have hsep' : ∀ a ∈ circleCoordinate '' A, ∀ b ∈ circleCoordinate '' B,
          ∃ c ∈ circleCoordinate '' F, c ∈ Set.uIcc a b := by
        rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
        obtain ⟨c, hcF, hc⟩ := hsep a ha b hb
        exact ⟨circleCoordinate c, ⟨c, hcF, rfl⟩, hc⟩
      obtain ⟨f, hf, he⟩ := closure_inter_subset_closed_separators _ _ _
        (hF.image circleCoordinate).isClosed hsep' ⟨hA, hB⟩
      exact Set.mem_insert_of_mem 0 (circleCoordinate_injective he ▸ hf)
  exact not_mem_both_closures_of_isolated A B hAB x (hisolated x hxF) ⟨hxA, hxB⟩

end FnZPositiveCones.CircularDynamics

namespace FnZPositiveCones.CircularRealization

variable {G : Type*} [Group G] {C : CircularGroupOrder G} (R : CircularRealization C)

/-- A successor makes every orbit point isolated, by transporting the checked
isolating neighborhood of the basepoint through the actual action. -/
theorem exists_orbit_isolating_neighborhood {a : G} (ha : C.IsSuccessor a) (g : G) :
    ∃ U, IsOpen U ∧ R.action g 0 ∈ U ∧
      U ∩ closure (Set.range (fun h => R.action h 0)) = {R.action g 0} := by
  obtain ⟨U, hU, hzero, hsing⟩ := R.exists_base_isolating_neighborhood ha
  refine ⟨R.action g '' U, (R.actionHomeomorph g).isOpenMap _ hU,
    ⟨0, hzero, rfl⟩, ?_⟩
  apply Set.Subset.antisymm
  · rintro x ⟨⟨y, hy, rfl⟩, hx⟩
    have hyC := R.circle_orbitClosure_mapsTo g⁻¹ hx
    have he : R.action g⁻¹ (R.action g y) = y := by
      rw [map_inv]
      exact (R.action g).symm_apply_apply y
    rw [he] at hyC
    have hy0 : y = 0 := Set.mem_singleton_iff.mp (hsing ▸ ⟨hy, hyC⟩)
    simp only [hy0, Set.mem_singleton_iff]
  · rintro _ rfl
    exact ⟨⟨0, hzero, rfl⟩, subset_closure ⟨g, rfl⟩⟩

end FnZPositiveCones.CircularRealization
