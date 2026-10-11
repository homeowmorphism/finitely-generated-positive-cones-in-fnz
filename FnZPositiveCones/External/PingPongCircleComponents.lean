module

public import FnZPositiveCones.External.PingPongCombinatorics
public import FnZPositiveCones.External.CircularDynamicsNormalization
public import FnZPositiveCones.External.CircularDynamicsCircleDomains
public import Mathlib.Data.Fintype.Sort
public import Mathlib.GroupTheory.Perm.Fin

@[expose] public section

/-!
# Components and successor order of finite circle domains

Component correspondences below are derived from the action's actual image
identity and from connectedness. No component map or cyclic adjacency is
assumed as an input. Circle arcs use a cut outside the closed domains.
-/

namespace FnZPositiveCones.PingPong

universe u v w

section OpenFamilies
variable {X : Type u} [TopologicalSpace X] {I : Type v} {J : Type w}

/-- A connected set cannot cross between members of a disjoint open family. -/
theorem preconnected_subset_open_member (D : I → Set X)
    (hopen : ∀ i, IsOpen (D i)) (hdisj : Pairwise (fun i j => Disjoint (D i) (D j)))
    {S : Set X} (hS : IsPreconnected S) (hcover : S ⊆ ⋃ i, D i)
    {i : I} (hmeet : (S ∩ D i).Nonempty) : S ⊆ D i := by
  classical
  apply hS.subset_left_of_subset_union (hopen i)
    (isOpen_iUnion fun j => isOpen_iUnion fun _ : j ≠ i => hopen j) ?_ ?_ hmeet
  · exact Set.disjoint_iUnion_right.mpr fun j =>
      Set.disjoint_iUnion_right.mpr fun hji => hdisj (Ne.symm hji)
  · intro x hx
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hcover hx)
    by_cases hji : j = i
    · exact Or.inl (hji ▸ hj)
    · exact Or.inr (Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨hji, hj⟩⟩)

/-- Each member of a disjoint connected open family is an actual connected
component of its union. -/
theorem connectedComponentIn_open_family (D : I → Set X)
    (hopen : ∀ i, IsOpen (D i)) (hconn : ∀ i, IsPreconnected (D i))
    (hdisj : Pairwise (fun i j => Disjoint (D i) (D j)))
    {i : I} {x : X} (hx : x ∈ D i) :
    connectedComponentIn (⋃ j, D j) x = D i := by
  have hxU : x ∈ ⋃ j, D j := Set.mem_iUnion.mpr ⟨i, hx⟩
  apply Set.Subset.antisymm
  · exact preconnected_subset_open_member D hopen hdisj isPreconnected_connectedComponentIn
      (connectedComponentIn_subset _ _) ⟨x, mem_connectedComponentIn hxU, hx⟩
  · exact (hconn i).subset_connectedComponentIn hx (Set.subset_iUnion D i)

/-- An actual homeomorphism of two unions takes each connected open member
onto exactly one connected open member, including surjectivity onto that member. -/
theorem exists_unique_image_member (f : X ≃ₜ X) (D : I → Set X) (E : J → Set X)
    (hDopen : ∀ i, IsOpen (D i)) (hDconn : ∀ i, IsConnected (D i))
    (hDdisj : Pairwise (fun i j => Disjoint (D i) (D j)))
    (hEopen : ∀ j, IsOpen (E j)) (hEconn : ∀ j, IsConnected (E j))
    (hEdisj : Pairwise (fun i j => Disjoint (E i) (E j)))
    (himage : f '' (⋃ i, D i) = ⋃ j, E j) (i : I) :
    ∃! j : J, f '' D i = E j := by
  obtain ⟨x, hx⟩ := (hDconn i).nonempty
  have hfx : f x ∈ ⋃ j, E j := by
    rw [← himage]
    exact ⟨x, Set.mem_iUnion.mpr ⟨i, hx⟩, rfl⟩
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hfx
  have he : f '' D i = E j := by
    rw [← connectedComponentIn_open_family D hDopen (fun i => (hDconn i).isPreconnected)
      hDdisj hx, f.image_connectedComponentIn (Set.mem_iUnion.mpr ⟨i, hx⟩), himage]
    exact connectedComponentIn_open_family E hEopen (fun j => (hEconn j).isPreconnected)
      hEdisj hj
  refine ⟨j, he, ?_⟩
  intro k hk
  by_contra hkj
  exact Set.disjoint_left.mp (hEdisj hkj)
    (hk ▸ (show f x ∈ f '' D i from ⟨x, hx, rfl⟩)) hj

/-- The component permutation is extracted from actual domain images. -/
noncomputable def openFamilyImageEquiv (f : X ≃ₜ X) (D : I → Set X) (E : J → Set X)
    (hDopen : ∀ i, IsOpen (D i)) (hDconn : ∀ i, IsConnected (D i))
    (hDdisj : Pairwise (fun i j => Disjoint (D i) (D j)))
    (hEopen : ∀ j, IsOpen (E j)) (hEconn : ∀ j, IsConnected (E j))
    (hEdisj : Pairwise (fun i j => Disjoint (E i) (E j)))
    (himage : f '' (⋃ i, D i) = ⋃ j, E j) : I ≃ J := by
  classical
  let F : I → J := fun i => (exists_unique_image_member f D E hDopen hDconn hDdisj
    hEopen hEconn hEdisj himage i).choose
  have hF (i : I) : f '' D i = E (F i) :=
    (exists_unique_image_member f D E hDopen hDconn hDdisj
      hEopen hEconn hEdisj himage i).choose_spec.1
  apply Equiv.ofBijective F
  constructor
  · intro i j hij
    have he : D i = D j := Set.image_injective.mpr f.injective ((hF i).trans ((congrArg E hij).trans (hF j).symm))
    by_contra hne
    obtain ⟨x, hx⟩ := (hDconn i).nonempty
    exact Set.disjoint_left.mp (hDdisj hne) hx (he ▸ hx)
  · intro j
    have hinv : f.symm '' (⋃ j, E j) = ⋃ i, D i := by
      rw [← himage, Set.image_image]
      simp only [f.symm_apply_apply, Set.image_id']
    obtain ⟨i, hi, _⟩ := exists_unique_image_member f.symm E D hEopen hEconn hEdisj
      hDopen hDconn hDdisj hinv j
    refine ⟨i, ?_⟩
    symm
    apply (exists_unique_image_member f D E hDopen hDconn hDdisj
      hEopen hEconn hEdisj himage i).choose_spec.2
    rw [← hi, Set.image_image]
    simp only [f.apply_symm_apply, Set.image_id']

/-- Exact image correspondence for the extracted finite-index adapter. -/
theorem openFamilyImageEquiv_image (f : X ≃ₜ X) (D : I → Set X) (E : J → Set X)
    (hDopen : ∀ i, IsOpen (D i)) (hDconn : ∀ i, IsConnected (D i))
    (hDdisj : Pairwise (fun i j => Disjoint (D i) (D j)))
    (hEopen : ∀ j, IsOpen (E j)) (hEconn : ∀ j, IsConnected (E j))
    (hEdisj : Pairwise (fun i j => Disjoint (E i) (E j)))
    (himage : f '' (⋃ i, D i) = ⋃ j, E j) (i : I) :
    f '' D i = E (openFamilyImageEquiv f D E hDopen hDconn hDdisj hEopen hEconn hEdisj himage i) :=
  (exists_unique_image_member f D E hDopen hDconn hDdisj
    hEopen hEconn hEdisj himage i).choose_spec.1

end OpenFamilies

end FnZPositiveCones.PingPong
