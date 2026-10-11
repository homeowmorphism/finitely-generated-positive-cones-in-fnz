module

public import FnZPositiveCones.External.NoncofinalDenseAction
public import FnZPositiveCones.External.OrderedActionsFill
public import Mathlib.Topology.Order.T5

@[expose] public section

namespace FnZPositiveCones.NoncofinalMinimalAction
universe u v
variable {G : Type u} [Group G] {X : Type v} [LinearOrder X]

/-- Order components commute with an order automorphism preserving the set. -/
theorem mapsTo_orderComponent (f : X ≃o X) (S : Set X)
    (hS : ∀ y, y ∈ S → f y ∈ S) {x y : X}
    (hxy : y ∈ Set.ordConnectedComponent S x) :
    f y ∈ Set.ordConnectedComponent S (f x) := by
  intro z hz
  have hh : f.symm z ∈ Set.uIcc x y := by
    rw [Set.mem_uIcc] at hz ⊢
    rcases hz with hz | hz
    · exact Or.inl ⟨f.le_iff_le.mp (by simpa using hz.1),
        f.le_iff_le.mp (by simpa using hz.2)⟩
    · exact Or.inr ⟨f.le_iff_le.mp (by simpa using hz.1),
        f.le_iff_le.mp (by simpa using hz.2)⟩
  simpa only [OrderIso.apply_symm_apply] using hS _ (hxy hh)

/-- Motions preserving the component of a basepoint in an invariant set. -/
def componentSubgroup (ρ : G →* (X ≃o X)) (S : Set X) (x : X) (hx : x ∈ S)
    (hS : ∀ g y, y ∈ S → ρ g y ∈ S) : Subgroup G where
  carrier := {g | ρ g x ∈ Set.ordConnectedComponent S x}
  one_mem' := by simpa using (Set.self_mem_ordConnectedComponent.mpr hx)
  mul_mem' := by
    intro g h hg hh
    change ρ (g * h) x ∈ Set.ordConnectedComponent S x
    simpa only [map_mul, RelIso.mul_apply] using
      Set.mem_ordConnectedComponent_trans hg (mapsTo_orderComponent (ρ g) S (hS g) hh)
  inv_mem' := by
    intro g hg
    change ρ g⁻¹ x ∈ Set.ordConnectedComponent S x
    have hh := mapsTo_orderComponent (ρ g⁻¹) S (hS g⁻¹) hg
    simp only [map_inv, RelIso.inv_apply_self] at hh
    simpa only [map_inv] using Set.mem_ordConnectedComponent_comm.mp hh

theorem componentSubgroup_convex (O : LeftGroupOrder G) (ρ : G →* (X ≃o X))
    (S : Set X) (x : X) (hx : x ∈ S) (hS : ∀ g y, y ∈ S → ρ g y ∈ S)
    (hmono : ∀ a b, O.order.le a b → ρ a x ≤ ρ b x) :
    letI := O.order; Set.OrdConnected (componentSubgroup ρ S x hx hS : Set G) := by
  let := O.order
  constructor
  intro a ha b hb g hg
  exact (inferInstance : Set.OrdConnected (Set.ordConnectedComponent S x)).out ha hb
    ⟨hmono _ _ hg.1, hmono _ _ hg.2⟩

/-- A dense base orbit and a maximal convex stabilizer make every real orbit dense. -/
theorem minimal_of_dense_base_maximal_stabilizer (O : LeftGroupOrder G)
    (ρ : G →* (ℝ ≃o ℝ)) (x : ℝ) (C : Subgroup G)
    (hstab : ∀ g, g ∈ C ↔ ρ g x = x)
    (hmono : ∀ a b, O.order.le a b → ρ a x ≤ ρ b x)
    (hmax : ∀ S : Subgroup G, (letI := O.order; Set.OrdConnected (S : Set G)) →
      C < S → S = ⊤)
    (hdense : DenseRange (fun g => ρ g x)) :
    ∀ y : ℝ, DenseRange (fun g => ρ g y) := by
  intro y
  let F := closure (Set.range (fun g => ρ g y))
  have hF : ∀ g t, t ∈ F → ρ g t ∈ F := by
    intro g t ht
    have hs : (ρ g) '' Set.range (fun h => ρ h y) ⊆ Set.range (fun h => ρ h y) := by
      rintro _ ⟨z, ⟨h, rfl⟩, rfl⟩
      exact ⟨g * h, by simp only [map_mul, RelIso.mul_apply]⟩
    exact closure_mono hs (mem_closure_image (ρ g).continuous.continuousAt ht)
  by_contra hn
  have hx : x ∉ F := by
    intro hx
    have hall : Set.range (fun g => ρ g x) ⊆ F := by
      rintro _ ⟨g, rfl⟩
      exact hF g x hx
    have : closure (Set.range (fun g => ρ g x)) ⊆ F :=
      closure_minimal hall isClosed_closure
    exact hn (by intro t; exact this (hdense t))
  have hcompl : ∀ g t, t ∈ Fᶜ → ρ g t ∈ Fᶜ := by
    intro g t ht he
    apply ht
    simpa only [map_inv, RelIso.inv_apply_self] using hF g⁻¹ (ρ g t) he
  let D := componentSubgroup ρ Fᶜ x hx hcompl
  have hCD : C ≤ D := by
    intro g hg
    change ρ g x ∈ Set.ordConnectedComponent Fᶜ x
    rw [(hstab g).mp hg]
    exact Set.self_mem_ordConnectedComponent.mpr hx
  obtain ⟨l, r, hxr, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp
    (Set.ordConnectedComponent_mem_nhds.mpr (isClosed_closure.isOpen_compl.mem_nhds hx))
  obtain ⟨g, hg⟩ := hdense.exists_mem_open isOpen_Ioo (Set.nonempty_Ioo.mpr hxr.2)
  have hgD : g ∈ D := hsub ⟨hxr.1.trans hg.1, hg.2⟩
  have hgC : g ∉ C := by
    intro he
    exact hg.1.ne ((hstab g).mp he).symm
  have hDtop : D = ⊤ := hmax D (componentSubgroup_convex O ρ Fᶜ x hx hcompl hmono)
    (lt_of_le_of_ne hCD (fun he => hgC (he ▸ hgD)))
  have hwhole : ∀ t, t ∈ Set.ordConnectedComponent Fᶜ x := by
    intro t
    obtain ⟨a, ha⟩ := hdense.exists_mem_open isOpen_Iio (Set.nonempty_Iio (a := t))
    obtain ⟨b, hb⟩ := hdense.exists_mem_open isOpen_Ioi (Set.nonempty_Ioi (a := t))
    have haD : a ∈ D := hDtop ▸ Subgroup.mem_top a
    have hbD : b ∈ D := hDtop ▸ Subgroup.mem_top b
    exact (inferInstance : Set.OrdConnected (Set.ordConnectedComponent Fᶜ x)).out haD hbD
      ⟨ha.le, hb.le⟩
  have hyF : y ∈ F := subset_closure ⟨1, by simp⟩
  exact Set.ordConnectedComponent_subset (hwhole y) hyF

/-- The real model of a dense countable order has dense image. -/
theorem realModel_denseRange [Countable X] [NoMinOrder X] [NoMaxOrder X]
    [Nonempty X] [DenselyOrdered X] : DenseRange (OrderedActions.realModel (A := X)) := by
  intro x
  by_contra hx
  obtain ⟨a, b, hab, _⟩ := OrderedActions.realModel_gap hx
  exact not_covBy_of_denselyOrdered hab


theorem transitive_at (ρ : G →* (X ≃o X)) (x : X)
    (htrans : Function.Surjective (fun g => ρ g x)) (a b : X) :
    ∃ g, ρ g a = b := by
  obtain ⟨u, hu⟩ := htrans a
  obtain ⟨v, hv⟩ := htrans b
  refine ⟨v * u⁻¹, ?_⟩
  dsimp only at hu hv
  rw [← hu, map_mul, RelIso.mul_apply, map_inv, RelIso.inv_apply_self, hv]

theorem transitive_noMax [Nontrivial X] (ρ : G →* (X ≃o X)) (x : X)
    (htrans : Function.Surjective (fun g => ρ g x)) : NoMaxOrder X := by
  constructor
  intro a
  obtain ⟨b, hb⟩ := exists_ne a
  rcases lt_or_gt_of_ne hb with hb | hb
  · obtain ⟨g, hg⟩ := transitive_at ρ x htrans a b
    refine ⟨ρ g⁻¹ a, ?_⟩
    simpa only [← hg, map_inv, RelIso.inv_apply_self] using (ρ g⁻¹).strictMono hb
  · exact ⟨b, hb⟩

theorem transitive_noMin [Nontrivial X] (ρ : G →* (X ≃o X)) (x : X)
    (htrans : Function.Surjective (fun g => ρ g x)) : NoMinOrder X := by
  constructor
  intro a
  obtain ⟨b, hb⟩ := exists_ne a
  rcases lt_or_gt_of_ne hb with hb | hb
  · exact ⟨b, hb⟩
  · obtain ⟨g, hg⟩ := transitive_at ρ x htrans a b
    refine ⟨ρ g⁻¹ a, ?_⟩
    simpa only [← hg, map_inv, RelIso.inv_apply_self] using (ρ g⁻¹).strictMono hb

/-- The coset order of a nonnormal maximal convex subgroup has an actual
minimal real realization, retaining its point stabilizer and a crossing. -/
theorem exists_minimal_real_action [Countable G] (O : LeftGroupOrder G) (C : Subgroup G)
    (hC : letI := O.order; Set.OrdConnected (C : Set G)) (hne : C ≠ ⊤)
    (hmax : ∀ S : Subgroup G, (letI := O.order; Set.OrdConnected (S : Set G)) →
      C < S → S = ⊤) (hnormal : ¬ C.Normal) :
    ∃ ρ : G →* (ℝ ≃o ℝ), ∃ x : ℝ,
      (∀ g, g ∈ C ↔ ρ g x = x) ∧
      (∀ a b, O.order.le a b → ρ a x ≤ ρ b x) ∧
      (∀ y, DenseRange (fun g => ρ g y)) ∧
      (∃ f g u v w, NoncofinalCrossings.Crossing (ρ f) (ρ g) u v w) := by
  let := NoncofinalConvexJump.cosetLinearOrder O C hC
  let : Nontrivial (G ⧸ C) := QuotientGroup.nontrivial_iff.mpr hne
  let : Countable (G ⧸ C) := Function.Surjective.countable (QuotientGroup.mk_surjective (s := C))
  let α := NoncofinalConvexJump.cosetAction O C hC
  let q : G ⧸ C := QuotientGroup.mk 1
  have ht : Function.Surjective (fun g => α g q) := by
    intro r
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective r
    exact ⟨g, NoncofinalConvexJump.cosetAction_base O C hC g⟩
  let := transitive_noMin α q ht
  let := transitive_noMax α q ht
  let := NoncofinalDenseAction.coset_denselyOrdered O C hC hne hmax hnormal
  let e := OrderedActions.realModel (A := G ⧸ C)
  let ρ := OrderedActions.realModelHom.comp α
  have he (g : G) (r : G ⧸ C) : ρ g (e r) = e (α g r) :=
    OrderedActions.realModelHom_apply (α g) r
  have hstab : ∀ g, g ∈ C ↔ ρ g (e q) = e q := by
    intro g
    rw [he, e.injective.eq_iff]
    exact (NoncofinalConvexJump.coset_base_fixed_iff O C hC g).symm
  have hmono : ∀ a b, O.order.le a b → ρ a (e q) ≤ ρ b (e q) := by
    intro a b hab
    rw [he, he, e.le_iff_le]
    simp only [α, q, NoncofinalConvexJump.cosetAction_base]
    exact (NoncofinalConvexJump.coset_mk_le_mk O C hC a b).mpr (Or.inl hab)
  have hd : DenseRange (fun g => ρ g (e q)) := by
    have hr : Set.range (fun g => ρ g (e q)) = Set.range e := by
      ext z
      constructor
      · rintro ⟨g, rfl⟩
        exact ⟨α g q, (he g q).symm⟩
      · rintro ⟨r, rfl⟩
        obtain ⟨g, rfl⟩ := ht r
        exact ⟨g, he g q⟩
    rw [DenseRange, hr]
    exact realModel_denseRange
  refine ⟨ρ, e q, hstab, hmono,
    minimal_of_dense_base_maximal_stabilizer O ρ (e q) C hstab hmono hmax hd, ?_⟩
  obtain ⟨f, g, u, v, w, hc⟩ :=
    NoncofinalConvexJump.exists_crossing_of_maximal_convex_not_normal O C hC hne hmax hnormal
  refine ⟨f, g, e u, e v, e w, ?_⟩
  constructor
  · exact e.strictMono hc.left_lt_middle
  · exact e.strictMono hc.middle_lt_right
  · intro n
    simpa only [← map_pow, he] using e.strictMono (hc.left_bounded n)
  · intro n
    simpa only [← map_pow, he] using e.strictMono (hc.right_bounded n)
  · obtain ⟨N, M, hN, hM⟩ := hc.crosses
    exact ⟨N, M, by simpa only [← map_pow, he] using e.strictMono hN,
      by simpa only [← map_pow, he] using e.strictMono hM⟩

end FnZPositiveCones.NoncofinalMinimalAction
