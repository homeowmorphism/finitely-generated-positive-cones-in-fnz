module

public import FnZPositiveCones.External.CircularDomainComponents
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Topology.Connected.LocallyConnected

@[expose] public section

/-! Endpoints of actual open connected circle components, using a cut outside
their closures. No interval representation is assumed. -/
namespace FnZPositiveCones.CircularDynamics

/-- Away from the cut, the normalized coordinate takes an open circle set to
an open real set. -/
theorem isOpen_circleCoordinate_image {S : Set StandardCircle}
    (hS : IsOpen S) (hzero : 0 ∉ S) : IsOpen (circleCoordinate '' S) := by
  have he : circleCoordinate '' S = Set.Ioo (0 : ℝ) 1 ∩
      (fun t : ℝ => (t : StandardCircle)) ⁻¹' S := by
    ext t
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hm := circleCoordinate_mem x
      refine ⟨⟨lt_of_le_of_ne hm.1 ?_, hm.2⟩, ?_⟩
      · intro he
        have hx0 : x = 0 := by
          rw [← coe_circleCoordinate x, ← he]
          rfl
        exact hzero (hx0 ▸ hx)
      · change (circleCoordinate x : StandardCircle) ∈ S
        simpa only [coe_circleCoordinate] using hx
    · rintro ⟨ht, hx⟩
      exact ⟨(t : StandardCircle), hx, circleCoordinate_coe ⟨ht.1.le, ht.2⟩⟩
  rw [he]
  exact isOpen_Ioo.inter (hS.preimage (AddCircle.continuous_mk' (1 : ℝ)))

/-- A nonempty bounded connected open real set is an actual open interval. -/
theorem open_connected_real_eq_Ioo {S : Set ℝ} (ho : IsOpen S)
    (hc : IsConnected S) (hb : IsCompact (closure S)) :
    ∃ a b : ℝ, a < b ∧ S = Set.Ioo a b ∧ closure S = Set.Icc a b := by
  have he := eq_Icc_of_connected_compact hc.closure hb
  have hr : interior (closure S) = S := by
    rw [hc.isPreconnected.convex.interior_closure_eq_interior_of_nonempty_interior
      (ho.interior_eq.symm ▸ hc.nonempty), ho.interior_eq]
  have hi : S = Set.Ioo (sInf (closure S)) (sSup (closure S)) := by
    calc
      S = interior (closure S) := hr.symm
      _ = interior (Set.Icc (sInf (closure S)) (sSup (closure S))) := congrArg interior he
      _ = _ := interior_Icc
  refine ⟨_, _, ?_, hi, he⟩
  obtain ⟨x, hx⟩ := hc.nonempty
  rw [hi] at hx
  exact hx.1.trans hx.2

/-- Every nonempty open connected circle set whose closure avoids the cut has
strictly ordered endpoints in the fundamental interval. Both the open set and
its closure are the actual quotient images of those intervals. -/
theorem open_connected_circle_endpoints {S : Set StandardCircle} (ho : IsOpen S)
    (hc : IsConnected S) (hzero : 0 ∉ closure S) :
    ∃ a b : ℝ, 0 < a ∧ a < b ∧ b < 1 ∧
      S = (fun t : ℝ => (t : StandardCircle)) '' Set.Ioo a b ∧
      closure S = closedCircleArc a b := by
  let J := circleCoordinate '' S
  let K := circleCoordinate '' closure S
  have hcont : ContinuousOn circleCoordinate (closure S) := fun x hx =>
    (continuousAt_circleCoordinate (fun he => hzero (he ▸ hx))).continuousWithinAt
  have hK : IsCompact K := isClosed_closure.isCompact.image_of_continuousOn hcont
  have hJK : closure J ⊆ K := closure_minimal (Set.image_mono subset_closure) hK.isClosed
  have hJcompact : IsCompact (closure J) := hK.of_isClosed_subset isClosed_closure hJK
  obtain ⟨a, b, hab, hJ, hJcl⟩ := open_connected_real_eq_Ioo
    (isOpen_circleCoordinate_image ho (fun hx => hzero (subset_closure hx)))
    (hc.image _ (hcont.mono subset_closure)) hJcompact
  have hbounds (t : ℝ) (ht : t ∈ closure J) : 0 < t ∧ t < 1 := by
    obtain ⟨x, hx, rfl⟩ := hJK ht
    have hm := circleCoordinate_mem x
    refine ⟨lt_of_le_of_ne hm.1 ?_, hm.2⟩
    intro he
    have hx0 : x = 0 := by
      rw [← coe_circleCoordinate x, ← he]
      rfl
    exact hzero (hx0 ▸ hx)
  have ha : 0 < a := (hbounds a (hJcl.symm ▸ (show a ∈ Set.Icc a b from ⟨le_rfl, hab.le⟩))).1
  have hb : b < 1 := (hbounds b (hJcl.symm ▸ (show b ∈ Set.Icc a b from ⟨hab.le, le_rfl⟩))).2
  have hS : S = (fun t : ℝ => (t : StandardCircle)) '' Set.Ioo a b := by
    calc
      S = (fun t : ℝ => (t : StandardCircle)) '' J := by
        dsimp only [J]
        rw [Set.image_image]
        simp only [coe_circleCoordinate, Set.image_id']
      _ = _ := congrArg (fun T : Set ℝ => (fun t : ℝ => (t : StandardCircle)) '' T) hJ
  refine ⟨a, b, ha, hab, hb, hS, ?_⟩
  apply Set.Subset.antisymm
  · apply closure_minimal
    · rw [hS]
      exact Set.image_mono Set.Ioo_subset_Icc_self
    · exact (isCompact_closedCircleArc a b).isClosed
  · have hi : closedCircleArc a b ⊆ closure ((fun t : ℝ => (t : StandardCircle)) '' Set.Ioo a b) := by
      have hh := image_closure_subset_closure_image (AddCircle.continuous_mk' (1 : ℝ))
        (s := Set.Ioo a b)
      rw [closure_Ioo hab.ne] at hh
      exact hh
    simpa only [← hS] using hi

/-- The circle is locally connected because it is a quotient of the real line. -/
instance locallyConnectedStandardCircle : LocallyConnectedSpace StandardCircle :=
  (QuotientAddGroup.isQuotientMap_mk (AddSubgroup.zmultiples (1 : ℝ))).isCoinducing.locallyConnectedSpace

/-- An actual connected component of a domain, viewed in the ambient circle. -/
def domainComponent (S : Set StandardCircle) (c : ConnectedComponents ↥S) :
    Set StandardCircle := Subtype.val '' {x : S | ConnectedComponents.mk x = c}

theorem domainComponent_mk (S : Set StandardCircle) (x : S) :
    domainComponent S (ConnectedComponents.mk x) = connectedComponentIn S x.val := by
  rw [connectedComponentIn_eq_image x.property]
  apply congrArg (Set.image Subtype.val)
  ext y
  exact ConnectedComponents.coe_eq_coe'

theorem domainComponent_subset (S : Set StandardCircle) (c : ConnectedComponents ↥S) :
    domainComponent S c ⊆ S := by
  rintro _ ⟨x, _, rfl⟩
  exact x.property

theorem isConnected_domainComponent (S : Set StandardCircle) (c : ConnectedComponents ↥S) :
    IsConnected (domainComponent S c) := by
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
  rw [domainComponent_mk]
  exact isConnected_connectedComponentIn_iff.mpr x.property

theorem isOpen_domainComponent {S : Set StandardCircle} (hS : IsOpen S)
    (c : ConnectedComponents ↥S) : IsOpen (domainComponent S c) := by
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
  rw [domainComponent_mk]
  exact hS.connectedComponentIn

theorem domainComponent_disjoint (S : Set StandardCircle)
    {c d : ConnectedComponents ↥S} (hcd : c ≠ d) :
    Disjoint (domainComponent S c) (domainComponent S d) := by
  apply Set.disjoint_left.mpr
  rintro z ⟨x, hx, hxz⟩ ⟨y, hy, hyz⟩
  have he : x = y := Subtype.ext (hxz.trans hyz.symm)
  exact hcd (hx.symm.trans ((congrArg ConnectedComponents.mk he).trans hy))

theorem iUnion_domainComponent (S : Set StandardCircle) :
    (⋃ c : ConnectedComponents ↥S, domainComponent S c) = S := by
  apply Set.Subset.antisymm
  · exact Set.iUnion_subset fun c => domainComponent_subset S c
  · intro x hx
    let y : S := ⟨x, hx⟩
    exact Set.mem_iUnion.mpr ⟨ConnectedComponents.mk y, y, rfl, rfl⟩

/-- The endpoints are obtained for the actual quotient type of connected
components. In particular, every component is nondegenerate. -/
theorem domainComponent_endpoints {S : Set StandardCircle} (hS : IsOpen S)
    (hzero : 0 ∉ closure S) (c : ConnectedComponents ↥S) :
    ∃ a b : ℝ, 0 < a ∧ a < b ∧ b < 1 ∧
      domainComponent S c = (fun t : ℝ => (t : StandardCircle)) '' Set.Ioo a b ∧
      closure (domainComponent S c) = closedCircleArc a b :=
  open_connected_circle_endpoints (isOpen_domainComponent hS c)
    (isConnected_domainComponent S c)
    (fun hz => hzero (closure_mono (domainComponent_subset S c) hz))

/-- Components are relatively closed in their domain. -/
theorem closure_domainComponent_inter (S : Set StandardCircle)
    (c : ConnectedComponents ↥S) : closure (domainComponent S c) ∩ S = domainComponent S c := by
  apply Set.Subset.antisymm
  · rintro z ⟨hz, hzS⟩
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
    rw [domainComponent_mk, connectedComponentIn_eq_image x.property] at hz ⊢
    have hh : (⟨z, hzS⟩ : S) ∈ closure (connectedComponent x) := closure_subtype.mpr hz
    rw [isClosed_connectedComponent.closure_eq] at hh
    exact ⟨⟨z, hzS⟩, hh, rfl⟩
  · exact fun z hz => ⟨subset_closure hz, domainComponent_subset S c hz⟩

/-- Membership in an arc whose endpoints lie strictly inside the coordinate
chart can be tested in real coordinates. -/
theorem coe_mem_open_arc_iff {a b t : ℝ} (ha : 0 < a) (hb : b < 1)
    (ht : t ∈ Set.Ico (0 : ℝ) 1) :
    (t : StandardCircle) ∈ (fun x : ℝ => (x : StandardCircle)) '' Set.Ioo a b ↔
      t ∈ Set.Ioo a b := by
  constructor
  · rintro ⟨x, hx, he⟩
    have hxI : x ∈ Set.Ico (0 : ℝ) 1 := ⟨(ha.trans hx.1).le, hx.2.trans hb⟩
    have hxt : x = t := by
      simpa only [circleCoordinate_coe hxI, circleCoordinate_coe ht] using congrArg circleCoordinate he
    exact hxt ▸ hx
  · exact fun hx => ⟨t, hx, rfl⟩

theorem coe_mem_closed_arc_iff {a b t : ℝ} (ha : 0 < a) (hb : b < 1)
    (ht : t ∈ Set.Ico (0 : ℝ) 1) :
    (t : StandardCircle) ∈ closedCircleArc a b ↔ t ∈ Set.Icc a b := by
  constructor
  · rintro ⟨x, hx, he⟩
    have hxI : x ∈ Set.Ico (0 : ℝ) 1 := ⟨ha.le.trans hx.1, hx.2.trans_lt hb⟩
    have hxt : x = t := by
      simpa only [circleCoordinate_coe hxI, circleCoordinate_coe ht] using congrArg circleCoordinate he
    exact hxt ▸ hx
  · exact fun hx => ⟨t, hx, rfl⟩

/-- Both endpoints of a component lie outside its original open domain. -/
theorem domainComponent_endpoints_not_mem {S : Set StandardCircle}
    (c : ConnectedComponents ↥S) {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1)
    (he : domainComponent S c = (fun t : ℝ => (t : StandardCircle)) '' Set.Ioo a b)
    (hcl : closure (domainComponent S c) = closedCircleArc a b) :
    (a : StandardCircle) ∉ S ∧ (b : StandardCircle) ∉ S := by
  have hnot (t : ℝ) (ht : t ∈ Set.Icc a b) (hend : t = a ∨ t = b) :
      (t : StandardCircle) ∉ S := by
    intro htS
    have htc : (t : StandardCircle) ∈ closure (domainComponent S c) := by
      rw [hcl]
      exact ⟨t, ht, rfl⟩
    have hmem : (t : StandardCircle) ∈ domainComponent S c := by
      rw [← closure_domainComponent_inter S c]
      exact ⟨htc, htS⟩
    rw [he] at hmem
    have hti := (coe_mem_open_arc_iff ha hb ⟨ha.le.trans ht.1, ht.2.trans_lt hb⟩).mp hmem
    rcases hend with rfl | rfl
    · exact (lt_irrefl _) hti.1
    · exact (lt_irrefl _) hti.2
  exact ⟨hnot a ⟨le_rfl, hab.le⟩ (Or.inl rfl), hnot b ⟨hab.le, le_rfl⟩ (Or.inr rfl)⟩

/-- Two closed arcs contained in the closure of a regular open set cannot
meet end to end at a point outside that set. -/
theorem regular_open_arcs_not_touch {S : Set StandardCircle}
    (hreg : interior (closure S) = S) {a b d : ℝ} (hab : a < b) (hbd : b < d)
    (hleft : closedCircleArc a b ⊆ closure S)
    (hright : closedCircleArc b d ⊆ closure S) (hnot : (b : StandardCircle) ∉ S) : False := by
  let U := (fun t : ℝ => (t : StandardCircle)) '' Set.Ioo a d
  have ho : IsOpen U := QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo
  have hU : U ⊆ closure S := by
    rintro _ ⟨t, ht, rfl⟩
    by_cases htb : t ≤ b
    · exact hleft ⟨t, ⟨ht.1.le, htb⟩, rfl⟩
    · exact hright ⟨t, ⟨(lt_of_not_ge htb).le, ht.2.le⟩, rfl⟩
  have hi := (ho.subset_interior_iff.mpr hU) (show (b : StandardCircle) ∈ U from ⟨b, ⟨hab, hbd⟩, rfl⟩)
  exact hnot (hreg ▸ hi)

/-- Distinct components of a regular open circle domain have strictly separated
coordinate intervals. Regularity excludes a shared endpoint. -/
theorem domainComponent_endpoints_separated {S : Set StandardCircle}
    (hreg : interior (closure S) = S) {c d : ConnectedComponents ↥S} (hcd : c ≠ d)
    {a b u v : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1)
    (hu : 0 < u) (huv : u < v) (hv : v < 1)
    (hec : domainComponent S c = (fun t : ℝ => (t : StandardCircle)) '' Set.Ioo a b)
    (hecl : closure (domainComponent S c) = closedCircleArc a b)
    (hed : domainComponent S d = (fun t : ℝ => (t : StandardCircle)) '' Set.Ioo u v)
    (hedl : closure (domainComponent S d) = closedCircleArc u v) : b < u ∨ v < a := by
  have hdisj : Disjoint (Set.Ioo a b) (Set.Ioo u v) := by
    apply Set.disjoint_left.mpr
    intro t ht ht'
    apply Set.disjoint_left.mp (domainComponent_disjoint S hcd)
    · rw [hec]
      exact ⟨t, ht, rfl⟩
    · rw [hed]
      exact ⟨t, ht', rfl⟩
  have hbc : (b : StandardCircle) ∉ S := (domainComponent_endpoints_not_mem c ha hab hb hec hecl).2
  have hvd : (v : StandardCircle) ∉ S := (domainComponent_endpoints_not_mem d hu huv hv hed hedl).2
  have hsubc : closedCircleArc a b ⊆ closure S := hecl ▸ closure_mono (domainComponent_subset S c)
  have hsubd : closedCircleArc u v ⊆ closure S := hedl ▸ closure_mono (domainComponent_subset S d)
  have hord : b ≤ u ∨ v ≤ a := by
    by_contra hn
    push Not at hn
    have hm : max a u < min b v := lt_min (max_lt hab hn.1) (max_lt hn.2 huv)
    obtain ⟨t, htl, htr⟩ := exists_between hm
    exact Set.disjoint_left.mp hdisj
      ⟨(le_max_left a u).trans_lt htl, htr.trans_le (min_le_left b v)⟩
      ⟨(le_max_right a u).trans_lt htl, htr.trans_le (min_le_right b v)⟩
  rcases hord with h | h
  · rcases h.lt_or_eq with h | h
    · exact Or.inl h
    · subst u
      exact (regular_open_arcs_not_touch hreg hab huv hsubc hsubd hbc).elim
  · rcases h.lt_or_eq with h | h
    · exact Or.inr h
    · subst a
      exact (regular_open_arcs_not_touch hreg huv hab hsubd hsubc hvd).elim

/-- In a regular open circle domain avoiding the cut, different actual
components have disjoint closures. Finiteness is not needed for this step. -/
theorem domainComponent_disjoint_closures {S : Set StandardCircle} (ho : IsOpen S)
    (hreg : interior (closure S) = S) (hzero : 0 ∉ closure S)
    {c d : ConnectedComponents ↥S} (hcd : c ≠ d) :
    Disjoint (closure (domainComponent S c)) (closure (domainComponent S d)) := by
  obtain ⟨a, b, ha, hab, hb, hec, hecl⟩ := domainComponent_endpoints ho hzero c
  obtain ⟨u, v, hu, huv, hv, hed, hedl⟩ := domainComponent_endpoints ho hzero d
  have hord := domainComponent_endpoints_separated hreg hcd ha hab hb hu huv hv hec hecl hed hedl
  rw [hecl, hedl]
  apply Set.disjoint_left.mpr
  rintro x ⟨t, ht, rfl⟩ hx
  have htv := (coe_mem_closed_arc_iff hu hv ⟨ha.le.trans ht.1, ht.2.trans_lt hb⟩).mp hx
  rcases hord with h | h
  · exact (not_lt_of_ge (htv.1.trans ht.2)) h
  · exact (not_lt_of_ge (ht.1.trans htv.2)) h

end FnZPositiveCones.CircularDynamics
