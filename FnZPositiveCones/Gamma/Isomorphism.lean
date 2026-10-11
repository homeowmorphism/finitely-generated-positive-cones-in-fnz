module

public import FnZPositiveCones.Gamma.MarkedProduct
public import FnZPositiveCones.Gamma.Weighted
public import FnZPositiveCones.Cover.Modular

@[expose] public section

/-! The marked product isomorphism and its verified weight inverse. -/
namespace FnZPositiveCones

theorem gammaWeightHom_comp_markedProduct :
    gammaWeightHom.comp markedProduct_to_H = MonoidHom.id (FnZ 2) := by
  let f := gammaWeightHom.comp markedProduct_to_H
  have hx : f.comp (MonoidHom.inl (FreeGroup (Fin 2)) (Multiplicative ℤ)) =
      MonoidHom.inl (FreeGroup (Fin 2)) (Multiplicative ℤ) := by
    apply FreeGroup.ext_hom
    intro i
    fin_cases i
    · change gammaWeightHom (markedProduct_to_H productX) = productX
      rw [markedProduct_to_H_X, gammaWeightHom_X]
    · change gammaWeightHom (markedProduct_to_H productY) = productY
      rw [markedProduct_to_H_Y, gammaWeightHom_Y]
  have hz : f.comp (MonoidHom.inr (FreeGroup (Fin 2)) (Multiplicative ℤ)) =
      MonoidHom.inr (FreeGroup (Fin 2)) (Multiplicative ℤ) := by
    apply MonoidHom.ext_mint
    change gammaWeightHom (markedProduct_to_H productZ) = productZ
    rw [markedProduct_to_H_Z, gammaWeightHom_Z]
  apply MonoidHom.ext
  rintro ⟨w, z⟩
  change f (w, z) = (w, z)
  have hp : (w, z) = (w, 1) * (1, z) := by simp
  rw [hp, map_mul]
  have hxw := DFunLike.congr_fun hx w
  have hzz := DFunLike.congr_fun hz z
  change f (w, 1) = (w, 1) at hxw
  change f (1, z) = (1, z) at hzz
  rw [hxw, hzz]

theorem markedProduct_to_H_injective : Function.Injective markedProduct_to_H := by
  intro p q h
  have he := congrArg gammaWeightHom h
  simpa only [← MonoidHom.comp_apply, gammaWeightHom_comp_markedProduct,
    MonoidHom.id_apply] using he

/-- Both directions of the marked isomorphism are constructed and checked. -/
noncomputable def H_marked_product_equiv : gammaH ≃* FnZ 2 :=
  (MulEquiv.ofBijective markedProduct_to_H
    ⟨markedProduct_to_H_injective, markedProduct_to_H_surjective⟩).symm

theorem H_marked_product_equiv_eq_weight (h : gammaH) :
    H_marked_product_equiv h = gammaWeightHom h := by
  obtain ⟨p, rfl⟩ := markedProduct_to_H_surjective h
  have hi : H_marked_product_equiv (markedProduct_to_H p) = p :=
    (MulEquiv.ofBijective markedProduct_to_H
      ⟨markedProduct_to_H_injective, markedProduct_to_H_surjective⟩).symm_apply_apply p
  rw [hi]
  exact (DFunLike.congr_fun gammaWeightHom_comp_markedProduct p).symm

@[simp] theorem H_marked_product_equiv_X : H_marked_product_equiv gammaX = productX := by
  rw [H_marked_product_equiv_eq_weight, gammaWeightHom_X]

@[simp] theorem H_marked_product_equiv_Y : H_marked_product_equiv gammaY0 = productY := by
  rw [H_marked_product_equiv_eq_weight, gammaWeightHom_Y]

@[simp] theorem H_marked_product_equiv_Z : H_marked_product_equiv gammaZ = productZ := by
  rw [H_marked_product_equiv_eq_weight, gammaWeightHom_Z]

/-- The marking required for the second power transversal. -/
theorem psi_C : H_marked_product_equiv gammaC =
    productY⁻¹ * productX⁻¹ * productY * productX * productZ⁻¹ := by
  rw [H_marked_product_equiv_eq_weight, gammaWeightHom_C]
  rfl

noncomputable def markedProjection : gammaH →* FreeGroup (Fin 2) :=
  (MonoidHom.fst _ _).comp H_marked_product_equiv.toMonoidHom

@[simp] theorem markedProjection_C : markedProjection gammaC = coverG := by
  change (H_marked_product_equiv gammaC).1 = coverG
  rw [psi_C]
  simp [productX, productY, productZ, coverG, freeX, freeY]

theorem markedProjection_surjective : Function.Surjective markedProjection := by
  intro w
  refine ⟨H_marked_product_equiv.symm (w, 1), ?_⟩
  change (H_marked_product_equiv (H_marked_product_equiv.symm (w, 1))).1 = w
  rw [H_marked_product_equiv.apply_symm_apply]

end FnZPositiveCones
