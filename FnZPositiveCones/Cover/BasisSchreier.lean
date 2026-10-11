module

public import FnZPositiveCones.Cover.Modular
public import FnZPositiveCones.Schreier.Positive

@[expose] public section

/-! Explicit Schreier generators for the modular cover, for every positive degree. -/
namespace FnZPositiveCones

open scoped Pointwise

def freeXUMap : FreeGroup (Fin 2) →* FreeGroup (Fin 2) :=
  FreeGroup.lift ![freeX, coverU]

def freeXUInverse : FreeGroup (Fin 2) →* FreeGroup (Fin 2) :=
  FreeGroup.lift ![freeX, freeY * freeX⁻¹]

theorem freeXUInverse_comp : freeXUInverse.comp freeXUMap = MonoidHom.id _ := by
  apply FreeGroup.ext_hom
  intro i
  fin_cases i <;> simp [freeXUMap, freeXUInverse, coverU, freeX, freeY]

theorem freeXUMap_comp : freeXUMap.comp freeXUInverse = MonoidHom.id _ := by
  apply FreeGroup.ext_hom
  intro i
  fin_cases i <;> simp [freeXUMap, freeXUInverse, coverU, freeX, freeY]

/-- The change from `x,y` to `x,u=y*x` has a checked inverse. -/
def freeXUEquiv : FreeGroup (Fin 2) ≃* FreeGroup (Fin 2) where
  toFun := freeXUMap
  invFun := freeXUInverse
  left_inv g := DFunLike.congr_fun freeXUInverse_comp g
  right_inv g := DFunLike.congr_fun freeXUMap_comp g
  map_mul' := map_mul freeXUMap

theorem freeXU_generators : Subgroup.closure ({freeX, coverU} : Set (FreeGroup (Fin 2))) = ⊤ := by
  apply top_unique
  rw [← FreeGroup.closure_range_of]
  apply (Subgroup.closure_le _).2
  rintro g ⟨i, rfl⟩
  have hx : freeX ∈ Subgroup.closure ({freeX, coverU} : Set (FreeGroup (Fin 2))) :=
    Subgroup.subset_closure (by simp)
  have hu : coverU ∈ Subgroup.closure ({freeX, coverU} : Set (FreeGroup (Fin 2))) :=
    Subgroup.subset_closure (by simp)
  fin_cases i
  · exact hx
  · simpa [coverU, freeY] using (Subgroup.closure ({freeX, coverU} : Set (FreeGroup (Fin 2)))).mul_mem
      hu ((Subgroup.closure ({freeX, coverU} : Set (FreeGroup (Fin 2)))).inv_mem hx)

variable (d : ℕ) [NeZero d]

def coverPowerRep (j : Fin d) : FreeGroup (Fin 2) := coverU ^ j.val

def coverPowerTransversal : Set (FreeGroup (Fin 2)) := Set.range (coverPowerRep d)

theorem coverPowerTransversal_complement :
    Subgroup.IsComplement (coverSubgroup d : Set (FreeGroup (Fin 2))) (coverPowerTransversal d) := by
  rw [Subgroup.isComplement_iff_existsUnique_mul_inv_mem]
  intro g
  let j : Fin d := (modularFinEquiv d).symm (modularRightAction d 0 g)
  have hj : modularRightAction d 0 (coverPowerRep d j) = modularRightAction d 0 g := by
    simp [coverPowerRep, j, modularFinEquiv]
  refine ⟨⟨coverPowerRep d j, ⟨j, rfl⟩⟩, ?_, ?_⟩
  · exact (modularRightAction_eq_iff_mul_inv_mem d _ _).1 hj.symm
  · rintro ⟨t, ⟨k, rfl⟩⟩ ht
    apply Subtype.ext
    have hk := (modularRightAction_eq_iff_mul_inv_mem d _ _).2 ht
    have he : (modularFinEquiv d) k = (modularFinEquiv d) j := by
      simpa [coverPowerRep, modularFinEquiv] using hk.symm.trans hj.symm
    exact congrArg (coverPowerRep d) ((modularFinEquiv d).injective he)

theorem coverPowerTransversal_one : (1 : FreeGroup (Fin 2)) ∈ coverPowerTransversal d := by
  exact ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩, by simp [coverPowerRep]⟩

def coverNegativeIndex (j : Fin d) : Fin d := (modularFinEquiv d).symm (-(j.val : ZMod d))

@[simp] theorem coverNegativeIndex_cast (j : Fin d) :
    ((coverNegativeIndex d j).val : ZMod d) = -(j.val : ZMod d) := by
  exact (modularFinEquiv d).apply_symm_apply _

def coverBasisA (j : Fin d) : coverSubgroup d :=
  ⟨coverU ^ j.val * freeX * (coverU ^ (coverNegativeIndex d j).val)⁻¹, by
    apply (modularRightAction_eq_iff_mul_inv_mem d _ _).1
    simp [modularRightAction_mul]⟩

def coverBasisC : coverSubgroup d := ⟨coverU ^ d, by simp⟩

@[simp] theorem coverBasisA_coe (j : Fin d) :
    (coverBasisA d j : FreeGroup (Fin 2)) =
      coverU ^ j.val * freeX * (coverU ^ (coverNegativeIndex d j).val)⁻¹ := rfl

@[simp] theorem coverBasisC_coe : (coverBasisC d : FreeGroup (Fin 2)) = coverU ^ d := rfl

theorem coverRep_x (j : Fin d) :
    rightRep (coverPowerTransversal_complement d) (coverPowerRep d j * freeX) =
      coverPowerRep d (coverNegativeIndex d j) := by
  apply rightRep_eq_of_mem (coverPowerTransversal_complement d) (Set.mem_range_self _)
  apply (modularRightAction_eq_iff_mul_inv_mem d _ _).1
  simp [coverPowerRep, modularRightAction_mul]

theorem coverRep_u (j : Fin d) :
    rightRep (coverPowerTransversal_complement d) (coverPowerRep d j * coverU) =
      coverPowerRep d ⟨(j.val + 1) % d, Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne d))⟩ := by
  apply rightRep_eq_of_mem (coverPowerTransversal_complement d) (Set.mem_range_self _)
  apply (modularRightAction_eq_iff_mul_inv_mem d _ _).1
  simp [coverPowerRep, modularRightAction_mul]

theorem coverSchreier_x (j : Fin d) :
    schreierDelta (coverPowerTransversal_complement d) (coverPowerRep d j) freeX =
      coverBasisA d j := by
  apply Subtype.ext
  change coverPowerRep d j * freeX *
    (rightRep (coverPowerTransversal_complement d) (coverPowerRep d j * freeX))⁻¹ = _
  rw [coverRep_x]
  rfl

theorem coverSchreier_u (j : Fin d) :
    schreierDelta (coverPowerTransversal_complement d) (coverPowerRep d j) coverU =
      if j.val + 1 = d then coverBasisC d else 1 := by
  apply Subtype.ext
  change coverPowerRep d j * coverU *
    (rightRep (coverPowerTransversal_complement d) (coverPowerRep d j * coverU))⁻¹ = _
  rw [coverRep_u]
  simp only [coverPowerRep, ← pow_succ]
  split_ifs with hj
  · simp [hj]
  · have hj' : j.val + 1 < d := by omega
    simp [Nat.mod_eq_of_lt hj']

def coverBasisGenerators : Set (coverSubgroup d) := Set.range (coverBasisA d) ∪ {coverBasisC d}

theorem coverBasis_generates : Subgroup.closure (coverBasisGenerators d) = ⊤ := by
  have h := Subgroup.closure_mul_image_eq_top (coverPowerTransversal_complement d)
    (coverPowerTransversal_one d) freeXU_generators
  apply top_unique
  rw [← h]
  apply (Subgroup.closure_le _).2
  rintro k ⟨g, ⟨t, ht, v, hv, rfl⟩, rfl⟩
  rcases ht with ⟨j, rfl⟩
  have ha : coverBasisA d j ∈ Subgroup.closure (coverBasisGenerators d) :=
    Subgroup.subset_closure (Or.inl ⟨j, rfl⟩)
  have hc : coverBasisC d ∈ Subgroup.closure (coverBasisGenerators d) :=
    Subgroup.subset_closure (Or.inr rfl)
  change schreierDelta (coverPowerTransversal_complement d) (coverPowerRep d j) v ∈ _
  rcases hv with rfl | hv
  · simpa [coverSchreier_x] using ha
  · have hv' : v = coverU := hv
    subst v
    rw [coverSchreier_u]
    split_ifs <;> simp_all

end FnZPositiveCones
