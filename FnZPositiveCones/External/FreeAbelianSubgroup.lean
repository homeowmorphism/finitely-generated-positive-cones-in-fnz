module

public import Mathlib.GroupTheory.FreeGroup.NielsenSchreier
public import Mathlib.GroupTheory.FreeGroup.Reduce
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

@[expose] public section

/-! Abelian subgroups of free groups are cyclic, including the trivial subgroup. -/

namespace FnZPositiveCones

universe u

/-- Distinct marked letters in a free group do not commute. -/
theorem freeGroup_of_commute_iff {ι : Type u} (a b : ι) :
    Commute (FreeGroup.of a) (FreeGroup.of b) ↔ a = b := by
  classical
  constructor
  · intro h
    have hw : [(a, true), (b, true)] = [(b, true), (a, true)] := by
      simpa [FreeGroup.toWord_mul, FreeGroup.reduce] using congrArg FreeGroup.toWord h.eq
    exact congrArg Prod.fst (List.cons.inj hw).1
  · rintro rfl
    exact Commute.refl _

/-- A free group with at most one basis element is cyclic. -/
theorem freeGroup_isCyclic_of_subsingleton {ι : Type u} [Subsingleton ι] :
    IsCyclic (FreeGroup ι) := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl he =>
    let : IsEmpty ι := he
    infer_instance
  | inr hn =>
    let : Unique ι := ⟨⟨Classical.choice hn⟩, fun _ => Subsingleton.elim _ _⟩
    infer_instance

/-- Pairwise commutation forces the actual basis index to have at most one element. -/
theorem freeGroup_isCyclic_of_commute {ι : Type u}
    (hcomm : ∀ a b : FreeGroup ι, Commute a b) : IsCyclic (FreeGroup ι) := by
  let : Subsingleton ι := ⟨fun a b => (freeGroup_of_commute_iff a b).mp (hcomm _ _)⟩
  exact freeGroup_isCyclic_of_subsingleton

/-- An abelian group equipped with a checked free basis is cyclic. -/
theorem isFreeGroup_isCyclic_of_commute {G : Type u} [Group G] [IsFreeGroup G]
    (hcomm : ∀ a b : G, Commute a b) : IsCyclic G := by
  let e := IsFreeGroup.toFreeGroup G
  have hfree : ∀ a b : FreeGroup (IsFreeGroup.Generators G), Commute a b := by
    intro a b
    have h := (hcomm (e.symm a) (e.symm b)).map e.toMonoidHom
    change Commute (e (e.symm a)) (e (e.symm b)) at h
    simpa only [e.apply_symm_apply] using h
  exact e.isCyclic.mpr (freeGroup_isCyclic_of_commute hfree)

/-- Every abelian subgroup of a free group is cyclic. Nielsen–Schreier supplies
the actual free basis; no finite generation or rank assumption is needed. -/
theorem freeSubgroup_isCyclic_of_commute {ι : Type u} (K : Subgroup (FreeGroup ι))
    (hcomm : ∀ a b : K, Commute a b) : IsCyclic K :=
  isFreeGroup_isCyclic_of_commute hcomm

end FnZPositiveCones
