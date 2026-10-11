module

public import FnZPositiveCones.External.CircularEndpointMaps
public import FnZPositiveCones.External.OrderedActionsGapAction

@[expose] public section

/-! A real coordinate on the tight orbit gaps, invariant under the group action. -/
namespace FnZPositiveCones.CircularRealization
open CircularDynamics
universe u
variable {G : Type u} [Group G] {C : CircularGroupOrder G} (R : CircularRealization C)

/-- Transport a point in a successor gap back to the identity gap. The value
outside all gaps is immaterial and chosen to be zero. -/
noncomputable def gapCoordinate (a : G) (x : StandardCircle) : ℝ := by
  classical
  exact if hx : ∃ g, x ∈ R.circleGap a g then circleCoordinate (R.action hx.choose⁻¹ x) else 0

theorem gapCoordinate_eq {a : G} (ha : C.IsSuccessor a) {g : G} {x : StandardCircle}
    (hx : x ∈ R.circleGap a g) :
    R.gapCoordinate a x = circleCoordinate (R.action g⁻¹ x) := by
  have h : ∃ g, x ∈ R.circleGap a g := ⟨g, hx⟩
  rw [gapCoordinate, dite_eq_left h]
  have he : h.choose = g := by
    by_contra hne
    exact Set.disjoint_left.mp (R.circleGap_disjoint ha hne) h.choose_spec hx
  rw [he]

/-- The coordinate is invariant under every group element on the complement
of the orbit closure. This uses uniqueness of actual successor-gap labels. -/
theorem gapCoordinate_action {a : G} (ha : C.IsSuccessor a) (k : G)
    {x : StandardCircle} (hx : x ∉ closure (Set.range (fun g => R.action g 0))) :
    R.gapCoordinate a (R.action k x) = R.gapCoordinate a x := by
  obtain ⟨g, hg⟩ := R.exists_mem_circleGap ha hx
  have hk : R.action k x ∈ R.circleGap a (k * g) := by
    rw [R.circleGap_transport]
    exact ⟨x, hg, rfl⟩
  rw [R.gapCoordinate_eq ha hk, R.gapCoordinate_eq ha hg,
    mul_inv_rev, map_mul, Equiv.Perm.mul_apply, map_inv]
  simp only [map_inv, Equiv.Perm.inv_def, Equiv.symm_apply_apply]

/-- A preconnected set disjoint from the orbit closure lies in one actual
successor gap. -/
theorem preconnected_subset_circleGap {a : G} (ha : C.IsSuccessor a)
    {S : Set StandardCircle} (hS : IsPreconnected S)
    (hdisj : Disjoint S (closure (Set.range (fun g => R.action g 0))))
    {x : StandardCircle} (hx : x ∈ S) : ∃ g, S ⊆ R.circleGap a g := by
  have hxK : x ∉ closure (Set.range (fun g => R.action g 0)) :=
    fun hh => Set.disjoint_left.mp hdisj hx hh
  obtain ⟨g, hg⟩ := R.exists_mem_circleGap ha hxK
  refine ⟨g, ?_⟩
  rw [← R.circleGap_eq_component ha g hg]
  exact hS.subset_connectedComponentIn hx (fun _ hy hh => Set.disjoint_left.mp hdisj hy hh)

/-- Along any oriented closed segment contained in one orbit gap, the
invariant coordinate strictly increases between its distinct endpoints. -/
theorem gapCoordinate_lt_of_segment_subset {a : G} (ha : C.IsSuccessor a)
    {g : G} {x y : StandardCircle} (hxy : x ≠ y)
    (hsub : circularClosedSegment x y ⊆ R.circleGap a g) :
    R.gapCoordinate a x < R.gapCoordinate a y := by
  have hx := hsub (mem_circularClosedSegment_left x y)
  have hy := hsub (mem_circularClosedSegment_right x y)
  rw [R.gapCoordinate_eq ha hx, R.gapCoordinate_eq ha hy]
  let u := R.action g⁻¹ x
  let v := R.action g⁻¹ y
  have hback : ∀ z, R.action g (R.action g⁻¹ z) = z := by
    intro z
    rw [map_inv]
    exact (R.action g).apply_symm_apply z
  have hzero : 0 ∉ circularClosedSegment u v := by
    intro hz
    have hmem := (circularClosedSegment_perm (R.action g) (R.action_preserves g) u v 0).mpr hz
    dsimp only [u, v] at hmem
    rw [hback, hback] at hmem
    have hgap := hsub hmem
    exact Set.disjoint_left.mp (R.circleGap_disjoint_orbitClosure ha g) hgap (subset_closure ⟨g, rfl⟩)
  have hv : v ≠ 0 := fun he => hzero (he ▸ mem_circularClosedSegment_right u v)
  have hle := circularClosedSegment_coordinate_le hv hzero
  apply lt_of_le_of_ne hle
  intro he
  have huv : u = v := by
    simpa only [coe_circleCoordinate] using congrArg (fun t : ℝ => (t : StandardCircle)) he
  exact hxy ((R.action g⁻¹).injective huv)

end FnZPositiveCones.CircularRealization
