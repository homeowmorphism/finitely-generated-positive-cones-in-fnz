module

public import FnZPositiveCones.Cover.BasisWeighted

@[expose] public section

/-! A checked basis equivalence proves the exact free rank of every modular cover. -/
namespace FnZPositiveCones

variable (d : ℕ) [NeZero d]

def coverBasisLetter : CoverBasisIndex d → coverSubgroup d
  | Sum.inl j => coverBasisA d j
  | Sum.inr _ => coverBasisC d

def coverBasisLift : CoverBasisFreeGroup d →* coverSubgroup d :=
  FreeGroup.lift (coverBasisLetter d)

theorem coverBasisWeight_lift :
    (coverBasisWeight d).comp (coverBasisLift d) = MonoidHom.id _ := by
  apply FreeGroup.ext_hom
  intro i
  cases i with
  | inl j => simp [coverBasisLift, coverBasisLetter]
  | inr u => cases u; simp [coverBasisLift, coverBasisLetter]

theorem coverBasisLift_injective : Function.Injective (coverBasisLift d) := by
  apply Function.LeftInverse.injective (g := coverBasisWeight d)
  intro w
  exact DFunLike.congr_fun (coverBasisWeight_lift d) w

theorem coverBasisLift_surjective : Function.Surjective (coverBasisLift d) := by
  rw [← MonoidHom.range_eq_top]
  apply top_unique
  rw [← coverBasis_generates d]
  apply (Subgroup.closure_le _).2
  rintro k (⟨j, rfl⟩ | hk)
  · exact ⟨FreeGroup.of (Sum.inl j), FreeGroup.lift_apply_of⟩
  · have hk' : k = coverBasisC d := hk
    subst k
    exact ⟨FreeGroup.of (Sum.inr ()), FreeGroup.lift_apply_of⟩

/-- The free basis is given by the explicit `a_j` loops and the single wrap loop. -/
noncomputable def coverExplicitBasis : FreeGroupBasis (CoverBasisIndex d) (coverSubgroup d) :=
  FreeGroupBasis.ofRepr
    (MulEquiv.ofBijective (coverBasisLift d)
      ⟨coverBasisLift_injective d, coverBasisLift_surjective d⟩).symm

@[simp] theorem coverExplicitBasis_a (j : Fin d) :
    coverExplicitBasis d (Sum.inl j) = coverBasisA d j := by
  change coverBasisLift d (FreeGroup.of (Sum.inl j)) = coverBasisA d j
  exact FreeGroup.lift_apply_of

@[simp] theorem coverExplicitBasis_c :
    coverExplicitBasis d (Sum.inr ()) = coverBasisC d := by
  change coverBasisLift d (FreeGroup.of (Sum.inr ())) = coverBasisC d
  exact FreeGroup.lift_apply_of

noncomputable def coverBasisIndexEquiv : CoverBasisIndex d ≃ Fin (d + 1) :=
  Fintype.equivOfCardEq (by simp [CoverBasisIndex])

/-- Exact free rank `d+1`, not an upper bound or an unspecified freeness instance. -/
noncomputable def coverRankEquiv : coverSubgroup d ≃* FreeGroup (Fin (d + 1)) :=
  ((coverExplicitBasis d).reindex (coverBasisIndexEquiv d)).repr

end FnZPositiveCones
