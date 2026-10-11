module

public import FnZPositiveCones.Gamma.Basic
public import FnZPositiveCones.Schreier.Positive

@[expose] public section

/-! The six inverse powers of `b` give the right transversal and Schreier table. -/
namespace FnZPositiveCones

open scoped Pointwise

def gammaTransversalRep (s : Fin 6) : Gamma2 := bGamma ^ (-(s.val : ℤ))

def gammaTransversal : Set Gamma2 := Set.range gammaTransversalRep

@[simp] theorem gamma_phi_transversal (s : Fin 6) :
    gamma_phi (gammaTransversalRep s) = Multiplicative.ofAdd (-(s.val : ZMod 6)) := by
  apply Multiplicative.toAdd.injective
  simp [gammaTransversalRep]

theorem gamma_phi_transversal_injective :
    Function.Injective (gamma_phi ∘ gammaTransversalRep) := by
  intro s t h
  have he : (s.val : ZMod 6) = (t.val : ZMod 6) := by
    have he := congrArg Multiplicative.toAdd h
    simpa using he
  have hv := congrArg ZMod.val he
  simp only [ZMod.val_natCast_of_lt s.isLt, ZMod.val_natCast_of_lt t.isLt] at hv
  exact Fin.ext hv

theorem gammaH_mul_inv_mem_iff (g h : Gamma2) :
    g * h⁻¹ ∈ gammaH ↔ gamma_phi g = gamma_phi h := by
  simp [map_mul, map_inv, mul_inv_eq_one]

theorem gammaTransversal_isComplement :
    Subgroup.IsComplement (gammaH : Set Gamma2) gammaTransversal := by
  rw [Subgroup.isComplement_iff_existsUnique_mul_inv_mem]
  intro g
  let s : Fin 6 := ⟨(- (gamma_phi g).toAdd).val, ZMod.val_lt _⟩
  have hs : gamma_phi (gammaTransversalRep s) = gamma_phi g := by
    apply Multiplicative.toAdd.injective
    simp [s]
  refine ⟨⟨gammaTransversalRep s, ⟨s, rfl⟩⟩, ?_, ?_⟩
  · exact (gammaH_mul_inv_mem_iff _ _).2 hs.symm
  · rintro ⟨t, ⟨j, rfl⟩⟩ ht
    apply Subtype.ext
    have hj := gamma_phi_transversal_injective
      ((gammaH_mul_inv_mem_iff _ _).1 ht |>.symm.trans hs.symm)
    exact congrArg gammaTransversalRep hj

theorem gammaTransversal_one_mem : (1 : Gamma2) ∈ gammaTransversal := by
  exact ⟨0, by simp [gammaTransversalRep]⟩

theorem gammaTransversal_finite : gammaTransversal.Finite := Set.finite_range _

/-- The six positive Schreier generators in their actual subgroup type. -/
def gammaA (s : Fin 6) : gammaH :=
  ⟨bGamma ^ (-(s.val : ℤ)) * aGamma * bGamma ^ ((s.val + 2) % 6), by
    rw [gammaH_mem]
    simp only [map_mul, map_zpow, map_pow, gamma_phi_a, gamma_phi_b]
    fin_cases s <;> decide⟩

def gammaC : gammaH := ⟨bGamma ^ 6, by
  rw [gammaH_mem]
  simp only [map_pow, gamma_phi_b]
  decide⟩

@[simp] theorem gammaA_coe (s : Fin 6) :
    (gammaA s : Gamma2) = bGamma ^ (-(s.val : ℤ)) * aGamma * bGamma ^ ((s.val + 2) % 6) :=
  rfl

@[simp] theorem gammaC_coe : (gammaC : Gamma2) = bGamma ^ 6 := rfl

theorem gammaRep_a (s : Fin 6) :
    rightRep gammaTransversal_isComplement (gammaTransversalRep s * aGamma) =
      gammaTransversalRep ⟨(s.val + 2) % 6, Nat.mod_lt _ (by decide)⟩ := by
  apply rightRep_eq_of_mem gammaTransversal_isComplement
    (Set.mem_range_self ⟨(s.val + 2) % 6, Nat.mod_lt _ (by decide)⟩)
  rw [gammaH_mul_inv_mem_iff]
  simp only [map_mul, gamma_phi_transversal, gamma_phi_a]
  fin_cases s <;> decide

theorem gammaRep_b (s : Fin 6) :
    rightRep gammaTransversal_isComplement (gammaTransversalRep s * bGamma) =
      gammaTransversalRep ⟨(s.val + 5) % 6, Nat.mod_lt _ (by decide)⟩ := by
  apply rightRep_eq_of_mem gammaTransversal_isComplement
    (Set.mem_range_self ⟨(s.val + 5) % 6, Nat.mod_lt _ (by decide)⟩)
  rw [gammaH_mul_inv_mem_iff]
  simp only [map_mul, gamma_phi_transversal, gamma_phi_b]
  fin_cases s <;> decide

theorem gammaSchreier_a (s : Fin 6) :
    schreierDelta gammaTransversal_isComplement (gammaTransversalRep s) aGamma = gammaA s := by
  apply Subtype.ext
  change gammaTransversalRep s * aGamma *
    (rightRep gammaTransversal_isComplement (gammaTransversalRep s * aGamma))⁻¹ = _
  rw [gammaRep_a]
  simp only [gammaTransversalRep, gammaA_coe, zpow_neg, inv_inv, zpow_natCast]

theorem gammaSchreier_b (s : Fin 6) :
    schreierDelta gammaTransversal_isComplement (gammaTransversalRep s) bGamma =
      if s = 0 then gammaC else 1 := by
  apply Subtype.ext
  change gammaTransversalRep s * bGamma *
    (rightRep gammaTransversal_isComplement (gammaTransversalRep s * bGamma))⁻¹ = _
  rw [gammaRep_b]
  fin_cases s <;> simp [gammaTransversalRep, gammaC] <;> group

/-- This indexed set is used both for subgroup generation and positive generation. -/
def gammaGenerators : Set gammaH := Set.range gammaA ∪ {gammaC}

theorem gammaH_generators : Subgroup.closure gammaGenerators = ⊤ := by
  have h := Subgroup.closure_mul_image_eq_top gammaTransversal_isComplement
    gammaTransversal_one_mem gamma_generators_closure
  apply top_unique
  rw [← h]
  apply (Subgroup.closure_le _).2
  rintro k ⟨g, ⟨t, ht, v, hv, rfl⟩, rfl⟩
  rcases ht with ⟨s, rfl⟩
  have ha : gammaA s ∈ Subgroup.closure gammaGenerators :=
    Subgroup.subset_closure (Or.inl ⟨s, rfl⟩)
  have hc : gammaC ∈ Subgroup.closure gammaGenerators :=
    Subgroup.subset_closure (Or.inr rfl)
  change schreierDelta gammaTransversal_isComplement (gammaTransversalRep s) v ∈ _
  rcases hv with rfl | hv
  · simpa [gammaSchreier_a] using ha
  · have hv' : v = bGamma := hv
    subst v
    rw [gammaSchreier_b]
    split_ifs <;> simp_all

end FnZPositiveCones
