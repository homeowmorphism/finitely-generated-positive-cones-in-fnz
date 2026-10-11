module

public import FnZPositiveCones.Construction.Subgroup

@[expose] public section

/-! Restriction of a marked product equivalence to the pulled-back cover subgroup. -/

namespace FnZPositiveCones

/-- Projection along any verified marked product isomorphism. -/
def productFreeProjection (e : gammaH ≃* FnZ 2) : gammaH →* FreeGroup (Fin 2) :=
  (MonoidHom.fst (FreeGroup (Fin 2)) (Multiplicative ℤ)).comp e.toMonoidHom

/-- Restrict the product equivalence, retaining the first-coordinate membership proof.
Both inverses are checked on the actual subgroup of `gammaH`. -/
def secondSubgroupProductEquiv (e : gammaH ≃* FnZ 2) (d : ℕ) [NeZero d] :
    secondSubgroup (productFreeProjection e) d ≃* coverSubgroup d × Multiplicative ℤ where
  toFun k := (⟨(e k.val).1, k.property⟩, (e k.val).2)
  invFun p := ⟨e.symm (p.1.val, p.2), by
    change (e (e.symm (p.1.val, p.2))).1 ∈ coverSubgroup d
    rw [e.apply_symm_apply]
    exact p.1.property⟩
  left_inv k := by
    apply Subtype.ext
    exact e.symm_apply_apply k.val
  right_inv p := by
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst (e.apply_symm_apply (p.1.val, p.2))
    · exact congrArg (fun z : FnZ 2 => z.2) (e.apply_symm_apply (p.1.val, p.2))
  map_mul' k l := by
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst (e.map_mul k.val l.val)
    · exact congrArg (fun z : FnZ 2 => z.2) (e.map_mul k.val l.val)

/-- An explicit free basis of the cover gives the precise rank in the final direct product. -/
def secondSubgroupFnZEquiv (e : gammaH ≃* FnZ 2) (d : ℕ) [NeZero d]
    (basis : coverSubgroup d ≃* FreeGroup (Fin (d + 1))) :
    secondSubgroup (productFreeProjection e) d ≃* FnZ (d + 1) :=
  (secondSubgroupProductEquiv e d).trans (basis.prodCongr (MulEquiv.refl (Multiplicative ℤ)))

end FnZPositiveCones
