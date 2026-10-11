module

public import FnZPositiveCones.External.CircularIntervalGaps

@[expose] public section

/-! Endpoint maps are derived from the actual orientation-preserving action. -/
namespace FnZPositiveCones.CircularDynamics

/-- An open circle interval of length less than one has precisely its two
endpoints as frontier, even when it crosses the chosen coordinate cut. -/
theorem frontier_open_circle_arc {a b : ℝ} (hab : a < b) (hlen : b < a + 1) :
    frontier ((fun t : ℝ => (t : StandardCircle)) '' Set.Ioo a b) =
      {(a : StandardCircle), (b : StandardCircle)} := by
  let q : ℝ → StandardCircle := fun t => (t : StandardCircle)
  have ho : IsOpen (q '' Set.Ioo a b) := QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo
  have hcl : closure (q '' Set.Ioo a b) = q '' Set.Icc a b := by
    apply Set.Subset.antisymm
    · exact closure_minimal (Set.image_mono Set.Ioo_subset_Icc_self)
        (isCompact_closedCircleArc a b).isClosed
    · have h := image_closure_subset_closure_image (AddCircle.continuous_mk' (1 : ℝ)) (s := Set.Ioo a b)
      rw [closure_Ioo hab.ne] at h
      exact h
  have hinj : Set.InjOn q (Set.Icc a b) := by
    intro x hx y hy he
    apply (AddCircle.coe_eq_coe_iff_of_mem_Ico (a := a)
      (show x ∈ Set.Ico a (a + 1) from ⟨hx.1, hx.2.trans_lt hlen⟩)
      (show y ∈ Set.Ico a (a + 1) from ⟨hy.1, hy.2.trans_lt hlen⟩)).mp he
  change frontier (q '' Set.Ioo a b) = _
  rw [frontier, hcl, ho.interior_eq]
  ext x
  constructor
  · rintro ⟨⟨t, ht, rfl⟩, hn⟩
    have htend : t = a ∨ t = b := by
      by_contra hh
      push Not at hh
      exact hn ⟨t, ⟨lt_of_le_of_ne ht.1 (Ne.symm hh.1), lt_of_le_of_ne ht.2 hh.2⟩, rfl⟩
    rcases htend with rfl | rfl <;> simp [q]
  · intro hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    have hend (t : ℝ) (ht : t ∈ Set.Icc a b) (he : t = a ∨ t = b) :
        q t ∈ q '' Set.Icc a b \ q '' Set.Ioo a b := by
      refine ⟨⟨t, ht, rfl⟩, ?_⟩
      rintro ⟨u, hu, hue⟩
      have hut : u = t := hinj (Set.Ioo_subset_Icc_self hu) ht hue
      subst u
      rcases he with rfl | rfl
      · exact lt_irrefl _ hu.1
      · exact lt_irrefl _ hu.2
    rcases hx with rfl | rfl
    · exact hend a ⟨le_rfl, hab.le⟩ (Or.inl rfl)
    · exact hend b ⟨hab.le, le_rfl⟩ (Or.inr rfl)

/-- An actual orientation-preserving homeomorphism mapping one open interval
onto another sends left endpoint to left endpoint and right endpoint to right
endpoint. Orientation is checked, rather than inferred from the set image. -/
theorem image_interval_endpoints (f : StandardCircle ≃ₜ StandardCircle)
    (hf : PreservesCircular f.toEquiv) {U V : Set StandardCircle}
    {a b c d : StandardCircle} (hU : U.Nonempty)
    (hUarc : U = {x | sbtw a x b}) (hVarc : V = {x | sbtw c x d})
    (hUfront : frontier U = {a, b}) (hVfront : frontier V = {c, d})
    (himage : f '' U = V) : f a = c ∧ f b = d := by
  have hpair : {f a, f b} = ({c, d} : Set StandardCircle) := by
    rw [← Set.image_pair, ← hUfront, f.image_frontier, himage, hVfront]
  rcases Set.pair_eq_pair_iff.mp hpair with h | h
  · exact h
  · obtain ⟨x, hx⟩ := hU
    have hfx : f x ∈ V := himage ▸ (show f x ∈ f '' U from ⟨x, hx, rfl⟩)
    rw [hUarc] at hx
    rw [hVarc] at hfx
    have hs : sbtw (f a) (f x) (f b) := by
      change sbtw a x b at hx
      rw [sbtw_iff_btw_not_btw] at hx ⊢
      exact ⟨(hf a x b).mpr hx.1, fun hh => hx.2 ((hf b x a).mp hh)⟩
    rw [h.1, h.2] at hs
    exact False.elim (hfx.not_sbtw hs)

namespace CircleIntervalFamily
universe u v
variable {I : Type u} {J : Type v} (F : CircleIntervalFamily I) (H : CircleIntervalFamily J)

theorem frontier_arc (i : I) :
    frontier (F.arc i) = {(F.left i : StandardCircle), (F.right i : StandardCircle)} := by
  apply frontier_open_circle_arc (F.left_lt_right i)
  have ha := F.left_pos i
  have hb := F.right_lt_one i
  linarith

theorem frontier_gap [Fintype I] (i : I) :
    frontier (F.gap i) = {(F.right i : StandardCircle), (F.left (F.next i) : StandardCircle)} := by
  rw [F.gap_eq_image, frontier_open_circle_arc (F.gap_interval_nonempty i)]
  · split_ifs with hi
    · simp only [add_zero]
    · rw [AddCircle.coe_add_period]
  · split_ifs with hi
    · have ha := (F.left_pos i).trans (F.left_lt_right i)
      have hb := (F.left_lt_right (F.next i)).trans (F.right_lt_one (F.next i))
      linarith
    · have h := (le_of_not_gt hi).trans_lt (F.left_lt_right i)
      linarith

/-- The component map from complement intervals has its specified endpoint
orientation as a theorem about the given homeomorphism. -/
theorem gap_image_arc_endpoints [Fintype I] [Fintype J]
    (f : StandardCircle ≃ₜ StandardCircle) (hf : PreservesCircular f.toEquiv)
    (i : I) (j : J) (himage : f '' F.gap i = H.arc j) :
    f (F.right i : StandardCircle) = (H.left j : StandardCircle) ∧
    f (F.left (F.next i) : StandardCircle) = (H.right j : StandardCircle) :=
  image_interval_endpoints f hf (F.isConnected_gap i).nonempty
    (F.gap_eq_sbtw i) (H.arc_eq_sbtw j) (F.frontier_gap i) (H.frontier_arc j) himage

theorem arc_disjoint {i j : I} (hij : i ≠ j) : Disjoint (F.arc i) (F.arc j) := by
  apply Set.disjoint_left.mpr
  rintro x ⟨t, ht, rfl⟩ hx
  have hx' := (coe_mem_open_arc_iff (F.left_pos j) (F.right_lt_one j)
    ⟨((F.left_pos i).trans ht.1).le, ht.2.trans (F.right_lt_one i)⟩).mp hx
  rcases F.separated i j hij with h | h
  · exact (lt_irrefl t) (ht.2.trans (h.trans hx'.1))
  · exact (lt_irrefl t) (hx'.2.trans (h.trans ht.1))

variable [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]

/-- The actual image equation determines a component bijection from the
right-hand complement gaps to the target domain components. -/
noncomputable def complementImageEquiv (f : StandardCircle ≃ₜ StandardCircle)
    (himage : f '' (closure (⋃ i, F.arc i))ᶜ = ⋃ j, H.arc j) : I ≃ J :=
  PingPong.openFamilyImageEquiv f F.gap H.arc F.isOpen_gap F.isConnected_gap
    (fun _ _ hij => F.gap_disjoint hij) H.isOpen_arc H.isConnected_arc
    (fun _ _ hij => H.arc_disjoint hij) (by rw [F.iUnion_gap]; exact himage)

theorem complementImageEquiv_image (f : StandardCircle ≃ₜ StandardCircle)
    (himage : f '' (closure (⋃ i, F.arc i))ᶜ = ⋃ j, H.arc j) (i : I) :
    f '' F.gap i = H.arc (F.complementImageEquiv H f himage i) :=
  PingPong.openFamilyImageEquiv_image f F.gap H.arc F.isOpen_gap F.isConnected_gap
    (fun _ _ hij => F.gap_disjoint hij) H.isOpen_arc H.isConnected_arc
    (fun _ _ hij => H.arc_disjoint hij) (by rw [F.iUnion_gap]; exact himage) i

/-- MMRT's local adjacency equation is derived from the two actual interval
images and their endpoint orientation. The two component bijections are
constructed from the homeomorphism and its inverse. -/
theorem complementImageEquiv_adjacency (f : StandardCircle ≃ₜ StandardCircle)
    (hf : PreservesCircular f.toEquiv)
    (hforward : f '' (closure (⋃ i, F.arc i))ᶜ = ⋃ j, H.arc j)
    (hback : f.symm '' (closure (⋃ j, H.arc j))ᶜ = ⋃ i, F.arc i) (i : I) :
    H.complementImageEquiv F f.symm hback (F.complementImageEquiv H f hforward i) = F.next i := by
  let j := F.complementImageEquiv H f hforward i
  let k := H.complementImageEquiv F f.symm hback j
  have hj := F.gap_image_arc_endpoints H f hf i j (F.complementImageEquiv_image H f hforward i)
  have hfs : PreservesCircular f.symm.toEquiv := preservesCircular_inv hf
  have hk := H.gap_image_arc_endpoints F f.symm hfs j k (H.complementImageEquiv_image F f.symm hback j)
  have he : (F.left (F.next i) : StandardCircle) = (F.left k : StandardCircle) := by
    calc
      (F.left (F.next i) : StandardCircle) = f.symm (f (F.left (F.next i) : StandardCircle)) :=
        (f.symm_apply_apply _).symm
      _ = f.symm (H.right j : StandardCircle) := congrArg f.symm hj.2
      _ = (F.left k : StandardCircle) := hk.1
  apply F.left_injective
  have hc := congrArg circleCoordinate he
  rw [circleCoordinate_coe ⟨(F.left_pos _).le, (F.left_lt_right _).trans (F.right_lt_one _)⟩,
    circleCoordinate_coe ⟨(F.left_pos _).le, (F.left_lt_right _).trans (F.right_lt_one _)⟩] at hc
  exact hc.symm

end CircleIntervalFamily
end FnZPositiveCones.CircularDynamics
