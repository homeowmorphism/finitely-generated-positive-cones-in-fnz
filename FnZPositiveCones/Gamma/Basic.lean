module

public import FnZPositiveCones.Interfaces

@[expose] public section

/-! Elementary algebra in the exact presentation ⟨a,b | ba²b=a⟩. -/
namespace FnZPositiveCones

 theorem gamma_relation : bGamma * aGamma ^ 2 * bGamma = aGamma := by
  apply mul_inv_eq_one.mp
  simpa [gammaRelator, aGamma, bGamma, PresentedGroup.of] using
    PresentedGroup.one_of_mem (rels := gammaRelations) (x := gammaRelator) (by
      simp [gammaRelations])

theorem gamma_generators_closure :
    Subgroup.closure ({aGamma, bGamma} : Set Gamma2) = ⊤ := by
  have hr : ({aGamma, bGamma} : Set Gamma2) = Set.range PresentedGroup.of := by
    ext g
    constructor
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      rintro (rfl | rfl)
      · exact ⟨GammaLetter.a, rfl⟩
      · exact ⟨GammaLetter.b, rfl⟩
    · rintro ⟨x, rfl⟩
      cases x <;> simp [aGamma, bGamma]
  rw [hr, PresentedGroup.closure_range_of]

theorem gamma_inverse_mul_a : bGamma⁻¹ * aGamma = aGamma ^ 2 * bGamma := by
  calc
    _ = bGamma⁻¹ * (bGamma * aGamma ^ 2 * bGamma) := by rw [gamma_relation]
    _ = _ := by group

theorem gamma_a_mul_inverse : aGamma * bGamma⁻¹ = bGamma * aGamma ^ 2 := by
  calc
    _ = (bGamma * aGamma ^ 2 * bGamma) * bGamma⁻¹ := by rw [gamma_relation]
    _ = _ := by group

theorem gamma_inverse_moves :
    bGamma⁻¹ * aGamma = aGamma ^ 2 * bGamma ∧
      aGamma * bGamma⁻¹ = bGamma * aGamma ^ 2 :=
  ⟨gamma_inverse_mul_a, gamma_a_mul_inverse⟩

theorem gamma_neg_pow_mul_a (s : ℕ) :
    bGamma ^ (-(s : ℤ)) * aGamma = aGamma * (aGamma * bGamma) ^ s := by
  simp only [zpow_neg, zpow_natCast, ← inv_pow]
  induction s with
  | zero => simp
  | succ s ih =>
    calc
      bGamma⁻¹ ^ (s + 1) * aGamma = bGamma⁻¹ * (bGamma⁻¹ ^ s * aGamma) := by
        rw [pow_succ']; group
      _ = bGamma⁻¹ * (aGamma * (aGamma * bGamma) ^ s) := by rw [ih]
      _ = aGamma * (aGamma * bGamma) ^ (s + 1) := by
        rw [← mul_assoc, gamma_inverse_mul_a, pow_succ' (aGamma * bGamma) s]
        simp only [pow_two, mul_assoc]

theorem gamma_a_mul_neg_pow (t : ℕ) :
    aGamma * bGamma ^ (-(t : ℤ)) = (bGamma * aGamma) ^ t * aGamma := by
  simp only [zpow_neg, zpow_natCast, ← inv_pow]
  induction t with
  | zero => simp
  | succ t ih =>
    calc
      aGamma * bGamma⁻¹ ^ (t + 1) = (aGamma * bGamma⁻¹ ^ t) * bGamma⁻¹ := by
        rw [pow_succ]; group
      _ = (bGamma * aGamma) ^ t * (aGamma * bGamma⁻¹) := by rw [ih]; group
      _ = (bGamma * aGamma) ^ (t + 1) * aGamma := by
        rw [gamma_a_mul_inverse, pow_succ (bGamma * aGamma) t]
        simp only [pow_two, mul_assoc]

theorem gamma_double_neg_sandwich (s t : ℕ) :
    bGamma ^ (-((s + 1 : ℕ) : ℤ)) * aGamma * bGamma ^ (-((t + 1 : ℕ) : ℤ)) =
      aGamma * (aGamma * bGamma) ^ s * (bGamma * aGamma) ^ t * aGamma := by
  calc
    _ = bGamma ^ (-(s : ℤ)) * (bGamma⁻¹ * aGamma * bGamma⁻¹) *
        bGamma ^ (-(t : ℤ)) := by push_cast; group
    _ = bGamma ^ (-(s : ℤ)) * (aGamma * aGamma) * bGamma ^ (-(t : ℤ)) := by
      rw [gamma_inverse_mul_a]
      simp only [pow_two, mul_assoc, mul_inv_cancel_left]
    _ = (bGamma ^ (-(s : ℤ)) * aGamma) * (aGamma * bGamma ^ (-(t : ℤ))) := by
      group
    _ = _ := by rw [gamma_neg_pow_mul_a, gamma_a_mul_neg_pow]; group

theorem aGamma_mem_basePositiveClosure : aGamma ∈ basePositiveClosure :=
  Subsemigroup.subset_closure (by simp)

theorem bGamma_mem_basePositiveClosure : bGamma ∈ basePositiveClosure :=
  Subsemigroup.subset_closure (by simp)

/-- An anchor preserves nonemptiness even when the power is zero. -/
theorem semigroup_mul_pow_mem {G : Type*} [Group G] (P : Subsemigroup G)
    {u v : G} (hu : u ∈ P) (hv : v ∈ P) (n : ℕ) : u * v ^ n ∈ P := by
  induction n with
  | zero => simpa using hu
  | succ n ih => simpa [pow_succ, ← mul_assoc] using P.mul_mem ih hv

theorem semigroup_pow_mul_mem {G : Type*} [Group G] (P : Subsemigroup G)
    {u v : G} (hu : u ∈ P) (hv : v ∈ P) (n : ℕ) : u ^ n * v ∈ P := by
  induction n with
  | zero => simpa using hv
  | succ n ih => simpa [pow_succ', mul_assoc] using P.mul_mem hu ih

theorem gamma_sandwich_mem (p q : ℤ) :
    bGamma ^ p * aGamma * bGamma ^ q ∈ basePositiveClosure := by
  have ha := aGamma_mem_basePositiveClosure
  have hb := bGamma_mem_basePositiveClosure
  have hab := basePositiveClosure.mul_mem ha hb
  have hba := basePositiveClosure.mul_mem hb ha
  cases p with
  | ofNat p =>
    cases q with
    | ofNat q =>
      simpa using semigroup_mul_pow_mem _ (semigroup_pow_mul_mem _ hb ha p) hb q
    | negSucc q =>
      have hq := gamma_a_mul_neg_pow (q + 1)
      change bGamma ^ (p : ℤ) * aGamma * bGamma ^ (-((q + 1 : ℕ) : ℤ)) ∈ _
      rw [mul_assoc, hq]
      simpa using semigroup_pow_mul_mem _ hb (semigroup_pow_mul_mem _ hba ha (q + 1)) p
  | negSucc p =>
    cases q with
    | ofNat q =>
      change bGamma ^ (-((p + 1 : ℕ) : ℤ)) * aGamma * bGamma ^ (q : ℤ) ∈ _
      rw [gamma_neg_pow_mul_a]
      simpa using semigroup_mul_pow_mem _ (semigroup_mul_pow_mem _ ha hab (p + 1)) hb q
    | negSucc q =>
      change bGamma ^ (-((p + 1 : ℕ) : ℤ)) * aGamma *
          bGamma ^ (-((q + 1 : ℕ) : ℤ)) ∈ _
      rw [gamma_double_neg_sandwich]
      exact basePositiveClosure.mul_mem
        (semigroup_mul_pow_mem _ (semigroup_mul_pow_mem _ ha hab p) hba q) ha

theorem gamma_positive_power_mem (k : ℕ) (hk : 1 ≤ k) :
    bGamma ^ k ∈ basePositiveClosure := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  simpa [pow_succ'] using
    semigroup_mul_pow_mem basePositiveClosure bGamma_mem_basePositiveClosure
      bGamma_mem_basePositiveClosure j

/-- The residue assignment used for the index-six subgroup. -/
def gammaResidue : GammaLetter → Multiplicative (ZMod 6)
  | .a => Multiplicative.ofAdd 4
  | .b => Multiplicative.ofAdd 1

theorem gammaResidue_relations (r : FreeGroup GammaLetter) (hr : r ∈ gammaRelations) :
    FreeGroup.lift gammaResidue r = 1 := by
  have hr' : r = gammaRelator := by simpa [gammaRelations] using hr
  subst r
  simp only [gammaRelator, map_mul, map_pow, map_inv, FreeGroup.lift_apply_of]
  decide

def gamma_phi : Gamma2 →* Multiplicative (ZMod 6) :=
  PresentedGroup.toGroup gammaResidue_relations

@[simp] theorem gamma_phi_a : gamma_phi aGamma = Multiplicative.ofAdd 4 :=
  PresentedGroup.toGroup.of _

@[simp] theorem gamma_phi_b : gamma_phi bGamma = Multiplicative.ofAdd 1 :=
  PresentedGroup.toGroup.of _

theorem gamma_phi_surjective : Function.Surjective gamma_phi := by
  intro r
  refine ⟨bGamma ^ r.toAdd.val, ?_⟩
  rw [map_pow, gamma_phi_b]
  apply Multiplicative.toAdd.injective
  simp [toAdd_pow, nsmul_eq_mul]

/-- The subgroup remains an actual subgroup of the presented group. -/
def gammaH : Subgroup Gamma2 := gamma_phi.ker

theorem gammaH_index : gammaH.index = 6 := by
  rw [gammaH, Subgroup.index_ker, MonoidHom.range_eq_top.mpr gamma_phi_surjective]
  simp [Nat.card_eq_fintype_card]

@[simp] theorem gammaH_mem (g : Gamma2) : g ∈ gammaH ↔ gamma_phi g = 1 := Iff.rfl

/-- The three marked subgroup elements of blueprint §9.1. -/
def gammaX : gammaH := ⟨aGamma * bGamma ^ 2, by
  rw [gammaH_mem]
  simp only [map_mul, map_pow, gamma_phi_a, gamma_phi_b]
  decide⟩

def gammaY0 : gammaH := ⟨aGamma ^ 2 * bGamma ^ 2 * aGamma ^ 2, by
  rw [gammaH_mem]
  simp only [map_mul, map_pow, gamma_phi_a, gamma_phi_b]
  decide⟩

def gammaZ : gammaH := ⟨aGamma ^ 3, by
  rw [gammaH_mem]
  simp only [map_pow, gamma_phi_a]
  decide⟩

@[simp] theorem gammaX_coe : (gammaX : Gamma2) = aGamma * bGamma ^ 2 := rfl
@[simp] theorem gammaY0_coe : (gammaY0 : Gamma2) = aGamma ^ 2 * bGamma ^ 2 * aGamma ^ 2 := rfl
@[simp] theorem gammaZ_coe : (gammaZ : Gamma2) = aGamma ^ 3 := rfl

theorem gamma_a_cube_commute_a : Commute (aGamma ^ 3) aGamma :=
  (Commute.refl aGamma).pow_left 3

theorem gamma_a_cube_commute_b : Commute (aGamma ^ 3) bGamma := by
  show aGamma ^ 3 * bGamma = bGamma * aGamma ^ 3
  symm
  calc
    bGamma * aGamma ^ 3 = (bGamma * aGamma ^ 2) * aGamma := by group
    _ = (aGamma * bGamma⁻¹) * aGamma := by rw [gamma_a_mul_inverse]
    _ = aGamma * (aGamma ^ 2 * bGamma) := by rw [mul_assoc, gamma_inverse_mul_a]
    _ = aGamma ^ 3 * bGamma := by group

/-- Centrality is proved from generation, without assuming Γ is commutative. -/
theorem gamma_a_cube_commute (g : Gamma2) : Commute (aGamma ^ 3) g := by
  have hg : g ∈ Subgroup.centralizer ({aGamma ^ 3} : Set Gamma2) := by
    apply PresentedGroup.generated_by gammaRelations
    intro letter
    cases letter
    · exact Subgroup.mem_centralizer_singleton_iff.mpr gamma_a_cube_commute_a.symm.eq
    · exact Subgroup.mem_centralizer_singleton_iff.mpr gamma_a_cube_commute_b.symm.eq
  exact (Subgroup.mem_centralizer_singleton_iff.mp hg).symm

theorem gammaZ_commute (g : gammaH) : Commute gammaZ g := by
  apply Subtype.ext
  exact gamma_a_cube_commute g

end FnZPositiveCones
