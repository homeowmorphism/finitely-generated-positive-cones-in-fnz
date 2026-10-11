module

public import FnZPositiveCones.External.CircularDynamicsTraces
public import FnZPositiveCones.External.CircularDynamicsLocal
public import FnZPositiveCones.External.OrderedActionsCompletion
public import FnZPositiveCones.Cone.Opposite
public import FnZPositiveCones.External.NoncofinalDynamics

@[expose] public section

namespace FnZPositiveCones
namespace FreeGroupOrbitPerturbation
open CircularDynamics
universe u v
variable {ι : Type u} {X : Type v}

/-- The outputs at which a postcomposition of one positive generator is tested.
For an inverse letter this is the initial, rather than the final, vertex. -/
noncomputable def edgeOutputs (ρ : ι → Equiv.Perm X) (i : ι) (x : X) : List (ι × Bool) → List X := by
  classical
  exact fun w => match w with
  | [] => []
  | s :: w =>
    (if s.1 = i then [if s.2 then evalWord ρ (s :: w) x else evalWord ρ w x] else []) ++
      edgeOutputs ρ i x w

/-- Every tested output and its generator preimage are vertices of the trace. -/
theorem edgeOutputs_mem_trace (ρ : ι → Equiv.Perm X) (i : ι) (x : X)
    (w : List (ι × Bool)) {y : X} (hy : y ∈ edgeOutputs ρ i x w) :
    y ∈ wordTrace ρ x w ∧ (ρ i)⁻¹ y ∈ wordTrace ρ x w := by
  classical
  induction w with
  | nil => simp [edgeOutputs] at hy
  | cons s w ih =>
    simp only [edgeOutputs, List.mem_append] at hy
    rcases hy with hy | hy
    · by_cases hi : s.1 = i
      · rcases s with ⟨j, b⟩
        dsimp at hi
        subst j
        cases b <;> simp only [Bool.false_eq_true, ite_false, ite_true,
          List.mem_singleton] at hy <;> subst y
        · constructor
          · exact List.mem_cons_of_mem _ (evalWord_mem_wordTrace ρ x w)
          · exact List.mem_cons_self
        · constructor
          · exact List.mem_cons_self
          · change (ρ i).symm ((ρ i) (evalWord ρ w x)) ∈ _
            rw [(ρ i).symm_apply_apply]
            exact List.mem_cons_of_mem _ (evalWord_mem_wordTrace ρ x w)
      · simp [hi] at hy
    · obtain ⟨ha, hb⟩ := ih hy
      exact ⟨List.mem_cons_of_mem _ ha, List.mem_cons_of_mem _ hb⟩

/-- Fixing exactly those outputs preserves the whole word, including inverses. -/
theorem evalWord_perturb_of_edgeOutputs_fixed (ρ : ι → Equiv.Perm X) (i : ι)
    (e : Equiv.Perm X) (x : X) (w : List (ι × Bool))
    (he : ∀ y ∈ edgeOutputs ρ i x w, e y = y) :
    evalWord (perturb ρ (i, true) e) w x = evalWord ρ w x := by
  classical
  induction w with
  | nil => rfl
  | cons s w ih =>
    have htail : ∀ y ∈ edgeOutputs ρ i x w, e y = y := by
      intro y hy
      apply he
      simp only [edgeOutputs, List.mem_append]
      exact Or.inr hy
    change letterPerm (perturb ρ (i, true) e) s
      (evalWord (perturb ρ (i, true) e) w x) = _
    rw [ih htail]
    by_cases hi : s.1 = i
    · rcases s with ⟨j, b⟩
      dsimp at hi
      subst j
      have hx : e (if b then evalWord ρ ((i, b) :: w) x else evalWord ρ w x) =
          (if b then evalWord ρ ((i, b) :: w) x else evalWord ρ w x) := by
        apply he
        simp [edgeOutputs]
      cases b
      · have hx' : e⁻¹ (evalWord ρ w x) = evalWord ρ w x := by
          apply e.injective
          simpa using hx.symm
        simp [letterPerm, perturb, mul_inv_rev, Equiv.Perm.mul_apply, hx', evalWord]
      · simpa [letterPerm, perturb, Equiv.Perm.mul_apply, evalWord] using hx
    · rw [letterPerm_perturb_other _ _ _ _ hi]
      rfl

/-- Forget only the order-preservation field, compatibly with composition. -/
def orderPermHom : (ℝ ≃o ℝ) →* Equiv.Perm ℝ where
  toFun := fun f => f.toEquiv
  map_one' := rfl
  map_mul' := fun _ _ => rfl

@[simp] theorem lift_generatorPerm (ρ : FreeGroup ι →* (ℝ ≃o ℝ)) :
    FreeGroup.lift (fun i => (ρ (FreeGroup.of i)).toEquiv) = orderPermHom.comp ρ := by
  apply FreeGroup.ext_hom
  intro i
  simp only [FreeGroup.lift_apply_of]
  rfl

/-- Preserve finitely many output constraints while making a new point fixed. -/
theorem exists_prescribed_extension (f : ℝ ≃o ℝ) (T : Finset ℝ) (x target : ℝ)
    (hx : ∀ y ∈ T, y < target) (hfx : ∀ y ∈ T, f.symm y < x) :
    ∃ e : ℝ ≃o ℝ, e (f x) = target ∧ ∀ y ∈ T, e y = y := by
  classical
  have hb : ∃ b : ℝ, (∀ y ∈ T, y < b) ∧ b < min target (f x) := by
    let U := T ∪ {min target (f x) - 1}
    have hu : U.Nonempty := ⟨min target (f x) - 1, Finset.mem_union_right _ (by simp)⟩
    have hmax : U.max' hu < min target (f x) := by
      apply (Finset.max'_lt_iff _ _).mpr
      intro y hy
      rcases Finset.mem_union.mp hy with hy | hy
      · exact lt_min (hx y hy) (by simpa only [f.apply_symm_apply] using f.strictMono (hfx y hy))
      · simp only [Finset.mem_singleton] at hy
        rw [hy]
        linarith
    obtain ⟨b, hmb, hbm⟩ := exists_between hmax
    exact ⟨b, fun y hy => (Finset.le_max' U y (Finset.mem_union_left _ hy)).trans_lt hmb, hbm⟩
  obtain ⟨b, hTb, hbx⟩ := hb
  obtain ⟨e, he, hfix⟩ := exists_supported_real_orderIso b (f x) target (max target (f x) + 1)
    (hbx.trans_le (min_le_right _ _)) (by have := le_max_right target (f x); linarith)
    (hbx.trans_le (min_le_left _ _)) (by have := le_max_left target (f x); linarith)
  exact ⟨e, he, fun y hy => hfix y (fun h => (hTb y hy).not_ge h.1.le)⟩


/-- The equal-target specialization fixes the chosen new point. -/
theorem exists_fixing_extension (f : ℝ ≃o ℝ) (T : Finset ℝ) (x : ℝ)
    (hx : ∀ y ∈ T, y < x) (hfx : ∀ y ∈ T, f.symm y < x) :
    ∃ e : ℝ ≃o ℝ, e (f x) = x ∧ ∀ y ∈ T, e y = y :=
  exists_prescribed_extension f T x x hx hfx

/-- A shortest word reaching above a bound has its entire proper trajectory
below that bound. The word need not be assumed reduced. -/
theorem exists_word_first_above (ρ : FreeGroup ι →* (ℝ ≃o ℝ)) (x B : ℝ)
    (hxB : x ≤ B) (hu : ∀ b : ℝ, ∃ g, b < ρ g x) :
    ∃ s w, B < evalWord (fun i => (ρ (FreeGroup.of i)).toEquiv) (s :: w) x ∧
      ∀ y ∈ wordTrace (fun i => (ρ (FreeGroup.of i)).toEquiv) x w, y ≤ B := by
  classical
  let φ := fun i => (ρ (FreeGroup.of i)).toEquiv
  have heval (w : List (ι × Bool)) : evalWord φ w x = ρ (FreeGroup.mk w) x := by
    rw [← lift_mk_apply, lift_generatorPerm]
    rfl
  have hex : ∃ n : ℕ, ∃ w : List (ι × Bool), w.length = n ∧ B < evalWord φ w x := by
    obtain ⟨g, hg⟩ := hu B
    exact ⟨g.toWord.length, g.toWord, rfl, by simpa only [heval, FreeGroup.mk_toWord] using hg⟩
  obtain ⟨w, hlen, hB⟩ := Nat.find_spec hex
  cases w with
  | nil => exact False.elim (hB.not_ge hxB)
  | cons s w =>
    refine ⟨s, w, hB, ?_⟩
    intro y hy
    obtain ⟨v, hv, rfl⟩ := (mem_wordTrace_iff φ x y w).mp hy
    by_contra h
    have hmin := Nat.find_min' hex ⟨v, rfl, lt_of_not_ge h⟩
    have hvlen := hv.length_le
    simp only [List.length_cons] at hlen
    omega

/-- A free-group action with an unbounded orbit admits a perturbation preserving
any finite orbit test and giving that basepoint a nontrivial stabilizer. -/
theorem exists_finite_trace_motion_family [Nontrivial ι]
    (ρ : FreeGroup ι →* (ℝ ≃o ℝ)) (x : ℝ)
    (hu : ∀ b : ℝ, ∃ g, b < ρ g x) (F : Finset (FreeGroup ι)) :
    ∃ B z : ℝ, ∃ k : FreeGroup ι, B < z ∧ k ≠ 1 ∧
      ∀ y : ℝ, B < y → ∃ σ : FreeGroup ι →* (ℝ ≃o ℝ),
        (∀ g ∈ F, σ g x = ρ g x) ∧
        (σ k x < x ↔ y < z) ∧ (x < σ k x ↔ z < y) := by
  classical
  let φ := fun i => (ρ (FreeGroup.of i)).toEquiv
  let U : Finset ℝ := F.biUnion (fun g => (wordTrace φ x g.toWord).toFinset) ∪ {x}
  obtain ⟨B, hB⟩ := U.finite_toSet.bddAbove
  have hxB : x ≤ B := hB (Finset.mem_union_right _ (by simp))
  have hFtrace : ∀ g ∈ F, ∀ y ∈ wordTrace φ x g.toWord, y ≤ B := by
    intro g hg y hy
    exact hB (Finset.mem_union_left _ (Finset.mem_biUnion.mpr
      ⟨g, hg, List.mem_toFinset.mpr hy⟩))
  obtain ⟨s, w, hs, hw⟩ := exists_word_first_above ρ x B hxB hu
  let z := evalWord φ (s :: w) x
  obtain ⟨i, hi⟩ := exists_ne s.1
  let T : Finset ℝ := F.biUnion (fun g => (edgeOutputs φ i x g.toWord).toFinset) ∪
    (edgeOutputs φ i x w).toFinset
  have hTb (y : ℝ) (hy : y ∈ T) : y ≤ B ∧ (φ i)⁻¹ y ≤ B := by
    rcases Finset.mem_union.mp hy with hy | hy
    · obtain ⟨g, hg, hy⟩ := Finset.mem_biUnion.mp hy
      have ht := edgeOutputs_mem_trace φ i x g.toWord (List.mem_toFinset.mp hy)
      exact ⟨hFtrace g hg y ht.1, hFtrace g hg _ ht.2⟩
    · have ht := edgeOutputs_mem_trace φ i x w (List.mem_toFinset.mp hy)
      exact ⟨hw y ht.1, hw _ ht.2⟩
  let g := FreeGroup.mk (s :: w)
  let k := g⁻¹ * FreeGroup.of i * g
  have hk : k ≠ 1 := by
    intro hk
    have he := congrArg (fun k => g * k * g⁻¹) hk
    have hgen : FreeGroup.of i = 1 := by
      simpa only [k, mul_assoc, mul_inv_cancel_left, inv_mul_cancel_right,
        one_mul, mul_one, mul_inv_cancel] using he
    exact FreeGroup.of_ne_one i hgen
  refine ⟨B, z, k, hs, hk, ?_⟩
  intro target htarget
  obtain ⟨e, hez, he⟩ := exists_prescribed_extension (ρ (FreeGroup.of i)) T z target
    (fun y hy => (hTb y hy).1.trans_lt htarget)
    (fun y hy => (hTb y hy).2.trans_lt hs)
  let σ : FreeGroup ι →* (ℝ ≃o ℝ) := FreeGroup.lift
    (fun j => if j = i then e * ρ (FreeGroup.of j) else ρ (FreeGroup.of j))
  have hσ : orderPermHom.comp σ = FreeGroup.lift (perturb φ (i, true) e.toEquiv) := by
    apply FreeGroup.ext_hom
    intro j
    simp only [MonoidHom.comp_apply, σ, FreeGroup.lift_apply_of]
    by_cases hji : j = i <;> simp [orderPermHom, perturb, hji, φ] <;> rfl
  have hσeval (v : List (ι × Bool)) :
      σ (FreeGroup.mk v) x = evalWord (perturb φ (i, true) e.toEquiv) v x := by
    change orderPermHom.comp σ (FreeGroup.mk v) x = _
    rw [hσ, lift_mk_apply]
  have hρeval (v : List (ι × Bool)) : evalWord φ v x = ρ (FreeGroup.mk v) x := by
    rw [← lift_mk_apply, lift_generatorPerm]
    rfl
  have hfixw : ∀ y ∈ edgeOutputs φ i x w, e.toEquiv y = y := by
    intro y hy
    exact he y (Finset.mem_union_right _ (List.mem_toFinset.mpr hy))
  have hg : σ (FreeGroup.mk (s :: w)) x = z := by
    rw [hσeval]
    change letterPerm (perturb φ (i, true) e.toEquiv) s
      (evalWord (perturb φ (i, true) e.toEquiv) w x) = z
    rw [evalWord_perturb_of_edgeOutputs_fixed φ i e.toEquiv x w hfixw,
      letterPerm_perturb_other φ (i, true) s e.toEquiv (Ne.symm hi)]
    rfl
  have hiz : σ (FreeGroup.of i) z = target := by
    simpa [σ] using hez
  refine ⟨σ, ?_, ?_⟩
  · intro g hgF
    have hfix : ∀ y ∈ edgeOutputs φ i x g.toWord, e.toEquiv y = y := by
      intro y hy
      exact he y (Finset.mem_union_left _ (Finset.mem_biUnion.mpr
        ⟨g, hgF, List.mem_toFinset.mpr hy⟩))
    have hh := evalWord_perturb_of_edgeOutputs_fixed φ i e.toEquiv x g.toWord hfix
    simpa only [← hσeval, hρeval, FreeGroup.mk_toWord] using hh
  · have hconj : σ g (σ k x) = target := by
      dsimp [k]
      simp only [NoncofinalDynamics.act_mul, NoncofinalDynamics.act_act_inv]
      rw [hg, hiz]
    constructor
    · have hiff : σ g (σ k x) < σ g x ↔ σ k x < x := (σ g).lt_iff_lt
      rw [hconj, hg] at hiff
      exact hiff.symm
    · have hiff : σ g x < σ g (σ k x) ↔ x < σ k x := (σ g).lt_iff_lt
      rw [hconj, hg] at hiff
      exact hiff.symm

/-- The same finite tests admit actions with opposite strict motions of one
common group element, without assuming the original orbit is free. -/
theorem exists_finite_trace_opposite_motions [Nontrivial ι]
    (ρ : FreeGroup ι →* (ℝ ≃o ℝ)) (x : ℝ)
    (hu : ∀ b : ℝ, ∃ g, b < ρ g x) (F : Finset (FreeGroup ι)) :
    ∃ σ τ : FreeGroup ι →* (ℝ ≃o ℝ), ∃ k : FreeGroup ι,
      (∀ g ∈ F, σ g x = ρ g x) ∧ (∀ g ∈ F, τ g x = ρ g x) ∧
        x < σ k x ∧ τ k x < x := by
  obtain ⟨B, z, k, hBz, _, hmotion⟩ := exists_finite_trace_motion_family ρ x hu F
  obtain ⟨y, hBy, hyz⟩ := exists_between hBz
  obtain ⟨σ, hσ, _, hσmove⟩ := hmotion (z + 1) (by linarith)
  obtain ⟨τ, hτ, hτmove, _⟩ := hmotion y hBy
  exact ⟨σ, τ, k, hσ, hτ, hσmove.mpr (by linarith), hτmove.mpr hyz⟩

/-- A finite test can also be preserved while creating a nontrivial stabilizer. -/
theorem exists_finite_trace_stabilizer [Nontrivial ι]
    (ρ : FreeGroup ι →* (ℝ ≃o ℝ)) (x : ℝ)
    (hu : ∀ b : ℝ, ∃ g, b < ρ g x) (F : Finset (FreeGroup ι)) :
    ∃ σ : FreeGroup ι →* (ℝ ≃o ℝ),
      (∀ g ∈ F, σ g x = ρ g x) ∧ ∃ k, k ≠ 1 ∧ σ k x = x := by
  obtain ⟨B, z, k, hBz, hk, hmotion⟩ := exists_finite_trace_motion_family ρ x hu F
  obtain ⟨σ, hσ, hleft, hright⟩ := hmotion z hBz
  refine ⟨σ, hσ, k, hk, le_antisymm ?_ ?_⟩
  · exact le_of_not_gt (fun h => (lt_irrefl z) (hright.mp h))
  · exact le_of_not_gt (fun h => (lt_irrefl z) (hleft.mp h))

end FreeGroupOrbitPerturbation
end FnZPositiveCones
