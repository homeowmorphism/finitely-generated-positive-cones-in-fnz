module

public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Instances.Real.Lemmas

@[expose] public section

/-! The checked topological normalization in MMRT Lemma 2.2. -/
namespace FnZPositiveCones
namespace CircularDynamics
universe u
variable {X : Type u} [TopologicalSpace X]

/-- Shrink one positive domain to the image of the complement of the closed
negative domain, exactly as in the source normalization. -/
def normalizedPositiveDomain (f : X ≃ₜ X) (B : Set X) : Set X := f '' (closure B)ᶜ

theorem isOpen_normalizedPositiveDomain (f : X ≃ₜ X) (B : Set X) :
    IsOpen (normalizedPositiveDomain f B) := f.isOpenMap _ isClosed_closure.isOpen_compl

theorem normalizedPositiveDomain_subset (f : X ≃ₜ X) (A B : Set X)
    (hpingpong : Set.MapsTo f (closure B)ᶜ A) : normalizedPositiveDomain f B ⊆ A :=
  Set.image_subset_iff.mpr hpingpong

/-- Regularity of the negative open domain gives the exact inverse equality.
No bijection of connected components or endpoint map is assumed. -/
theorem normalizedPositiveDomain_inverse (f : X ≃ₜ X) (B : Set X)
    (hregular : interior (closure B) = B) :
    f.symm '' (closure (normalizedPositiveDomain f B))ᶜ = B := by
  rw [normalizedPositiveDomain, ← f.image_closure, closure_compl, hregular,
    ← f.image_compl, compl_compl]
  simp only [Set.image_image, f.symm_apply_apply]
  change id '' B = B
  exact Set.image_id B

/-- The shrunken positive domain is regular open as well. -/
theorem normalizedPositiveDomain_regular (f : X ≃ₜ X) (B : Set X)
    (hregular : interior (closure B) = B) :
    interior (closure (normalizedPositiveDomain f B)) = normalizedPositiveDomain f B := by
  rw [normalizedPositiveDomain, ← f.image_closure, ← f.image_interior,
    closure_compl, hregular, interior_compl]

/-- The two required exact complement/domain identities hold simultaneously. -/
theorem normalized_domain_pair (f : X ≃ₜ X) (A B : Set X)
    (hpingpong : Set.MapsTo f (closure B)ᶜ A)
    (hregular : interior (closure B) = B) :
    ∃ A' : Set X, A' ⊆ A ∧ IsOpen A' ∧ interior (closure A') = A' ∧
      f '' (closure B)ᶜ = A' ∧ f.symm '' (closure A')ᶜ = B :=
  ⟨normalizedPositiveDomain f B, normalizedPositiveDomain_subset f A B hpingpong,
    isOpen_normalizedPositiveDomain f B, normalizedPositiveDomain_regular f B hregular,
    rfl, normalizedPositiveDomain_inverse f B hregular⟩

/-- Disjoint closures let regularity pass through a finite union. Thus the
normalization's regularity premise follows from actual finite separated arcs. -/
theorem regular_open_finset_iUnion {I : Type*} (F : Finset I) (D : I → Set X)
    (hregular : ∀ i ∈ F, interior (closure (D i)) = D i)
    (hdisjoint : ∀ i ∈ F, ∀ j ∈ F, i ≠ j → Disjoint (closure (D i)) (closure (D j))) :
    interior (closure (⋃ i ∈ F, D i)) = ⋃ i ∈ F, D i := by
  classical
  induction F using Finset.induction_on with
  | empty => simp
  | @insert i F hi ih =>
      have hregi := hregular i (Finset.mem_insert_self i F)
      have hregF : ∀ j ∈ F, interior (closure (D j)) = D j :=
        fun j hj => hregular j (Finset.mem_insert_of_mem hj)
      have hdisF : ∀ j ∈ F, ∀ k ∈ F, j ≠ k → Disjoint (closure (D j)) (closure (D k)) :=
        fun j hj k hk hjk => hdisjoint j (Finset.mem_insert_of_mem hj) k
          (Finset.mem_insert_of_mem hk) hjk
      have hd : Disjoint (closure (D i)) (closure (⋃ j ∈ F, D j)) := by
        rw [Finset.closure_biUnion]
        apply Set.disjoint_iUnion_right.mpr
        intro j
        apply Set.disjoint_iUnion_right.mpr
        intro hj
        exact hdisjoint i (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj)
          (fun he => hi (he ▸ hj))
      simp only [Finset.mem_insert, Set.iUnion_iUnion_eq_or_left, closure_union]
      rw [interior_union_of_disjoint_closure (by simpa only [closure_closure] using hd),
        hregi, ih hregF hdisF]

/-- Each real open interval is regular, including degenerate and empty cases. -/
theorem regular_open_real_Ioo (a b : ℝ) :
    interior (closure (Set.Ioo a b)) = Set.Ioo a b := by
  by_cases hab : a < b
  · rw [closure_Ioo hab.ne, interior_Icc]
  · rw [Set.Ioo_eq_empty hab]
    simp


/-- The normalization provides an actual homeomorphism of the relevant open
subspaces. Consequently component correspondences come from the action itself. -/
def normalizedPositiveDomainHomeomorph (f : X ≃ₜ X) (B : Set X) :
    ↥((closure B)ᶜ) ≃ₜ normalizedPositiveDomain f B := f.image _

/-- The action-induced bijection of connected components, with no cardinality
or endpoint correspondence assumed. -/
noncomputable def normalizedPositiveDomainComponents (f : X ≃ₜ X) (B : Set X) :
    ConnectedComponents ↥((closure B)ᶜ) ≃
      ConnectedComponents ↥(normalizedPositiveDomain f B) := by
  let e := normalizedPositiveDomainHomeomorph f B
  exact (e.isQuotientMap.isCoinducing.connectedComponentsHomeomorph (by
    intro y
    have he : e ⁻¹' {y} = {e.symm y} := by
      ext x
      exact e.toEquiv.eq_symm_apply.symm
    rw [he]
    exact isConnected_singleton)).toEquiv

/-- Apply the source's asymmetric shrinking to every positive generator,
leaving its negative partner fixed. -/
def normalizedDomains {I : Type*} (f : I → X ≃ₜ X) (D : I × Bool → Set X)
    (s : I × Bool) : Set X :=
  if s.2 then normalizedPositiveDomain (f s.1) (D (s.1, false)) else D (s.1, false)

/-- The signed action used by the normalization, with inverse convention
matching the free-group action. -/
def signedHomeomorph {I : Type*} (f : I → X ≃ₜ X) (s : I × Bool) : X ≃ₜ X :=
  if s.2 then f s.1 else (f s.1).symm

/-- Exact complement-to-domain equality for both signs after normalization. -/
theorem normalizedDomains_image {I : Type*} (f : I → X ≃ₜ X)
    (D : I × Bool → Set X)
    (hregular : ∀ i, interior (closure (D (i, false))) = D (i, false))
    (s : I × Bool) :
    signedHomeomorph f s '' (closure (normalizedDomains f D (s.1, !s.2)))ᶜ =
      normalizedDomains f D s := by
  rcases s with ⟨i, b⟩
  cases b
  · simpa only [signedHomeomorph, normalizedDomains, Bool.not_false, Bool.false_eq_true,
      ↓reduceIte] using normalizedPositiveDomain_inverse (f i) (D (i, false)) (hregular i)
  · rfl

/-- Normalization shrinks each domain when the genuine full complement
ping-pong inclusion has been proved. Trapping among colored domains alone does
not suffice for this hypothesis. -/
theorem normalizedDomains_subset {I : Type*} (f : I → X ≃ₜ X)
    (D : I × Bool → Set X)
    (hpingpong : ∀ i, Set.MapsTo (f i) (closure (D (i, false)))ᶜ (D (i, true)))
    (s : I × Bool) : normalizedDomains f D s ⊆ D s := by
  rcases s with ⟨i, b⟩
  cases b
  · exact Set.Subset.rfl
  · exact normalizedPositiveDomain_subset (f i) _ _ (hpingpong i)

/-- Pairwise disjoint closures are preserved by the actual shrinking. -/
theorem normalizedDomains_disjoint_closures {I : Type*} (f : I → X ≃ₜ X)
    (D : I × Bool → Set X)
    (hpingpong : ∀ i, Set.MapsTo (f i) (closure (D (i, false)))ᶜ (D (i, true)))
    (hdisjoint : ∀ s t, s ≠ t → Disjoint (closure (D s)) (closure (D t)))
    {s t : I × Bool} (hst : s ≠ t) :
    Disjoint (closure (normalizedDomains f D s)) (closure (normalizedDomains f D t)) :=
  (hdisjoint s t hst).mono (closure_mono (normalizedDomains_subset f D hpingpong s))
    (closure_mono (normalizedDomains_subset f D hpingpong t))

end CircularDynamics
end FnZPositiveCones
