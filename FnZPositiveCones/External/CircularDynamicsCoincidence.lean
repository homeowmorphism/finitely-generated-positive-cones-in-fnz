module

public import FnZPositiveCones.External.CircularDynamicsCompletion

@[expose] public section

/-!
# Distinct circular completions at a genuine orbit coincidence

A nontrivial stabilizer is resolved in opposite ways by a left order and its
reverse. If another orbit point exists, the triple consisting of identity,
a stabilizer element, and that other label distinguishes the two completions.
This does not assume that such a coincidence can be created by perturbation.
-/

namespace FnZPositiveCones

universe u v

/-- Reversal preserves left invariance, without assuming right invariance. -/
def LeftGroupOrder.reverse {G : Type u} [Group G] (L : LeftGroupOrder G) :
    LeftGroupOrder G where
  order := by
    letI := L.order
    exact inferInstanceAs (LinearOrder Gᵒᵈ)
  mul_le_mul_left a b c hab := L.mul_le_mul_left b a c hab

namespace CircularDynamics

variable {ι : Type u} {X : Type v} [CircularOrder X]
variable (ρ : FreeGroup ι →* Equiv.Perm X) (hρ : ∀ g, PreservesCircular (ρ g))
variable (x : X) (L : LeftGroupOrder (FreeGroup ι))

/-- A nonidentity stabilizer representative has height zero exactly when its
label is positive in the order used to resolve the stabilizer. -/
theorem completionRepresentative_stabilizer_height_zero_iff (k : FreeGroup ι)
    (hk : k ≠ 1) (hkx : ρ k x = x) :
    (completionLift ρ hρ x (completionRepresentative ρ hρ x L k)).height = 0 ↔
      L.order.lt 1 k := by
  let := (completionOrder ρ hρ x L).order
  let r := completionRepresentative ρ hρ x L k
  have hrbase : (completionLift ρ hρ x r).base = k := by simp [r]
  have hrpos : 1 < r :=
    cofinalProductRepresentative_pos (completionOrder ρ hρ x L)
      (completionOrder_center_positive ρ hρ x L) (completionOrder_center_cofinal ρ hρ x L) hk
  have hp := (completionOrder_lt_iff ρ hρ x L 1 r).mp hrpos
  simp only [map_one, inv_one, one_mul] at hp
  have hm := (completionOrder ρ hρ x L).fundamentalRepresentative_mem
    (completionOrder_center_positive ρ hρ x L) (completionOrder_center_cofinal ρ hρ x L) (k, 1)
  change 1 ≤ r ∧ r < cofinalProductZ (FreeGroup ι) at hm
  have ht := (completionOrder_lt_iff ρ hρ x L r (cofinalProductZ (FreeGroup ι))).mp hm.2
  have he := completionLift_zpow ρ hρ x 1
  simp only [zpow_one] at he
  rw [he] at ht
  have hh : ((completionLift ρ hρ x r)⁻¹ *
      (orbitCocycle ρ hρ x).central (Multiplicative.ofAdd 1)).height =
      1 - (completionLift ρ hρ x r).height := by
    simp [NormalizedIntCocycle.central, hrbase, orbitCocycle_inverse_rev, hkx,
      NormalizedIntCocycle.one_right]
    omega
  have hki : ρ k⁻¹ x = x := by
    have he := congrArg (ρ k⁻¹) hkx
    simpa using he.symm
  have hbase : ((completionLift ρ hρ x r)⁻¹ *
      (orbitCocycle ρ hρ x).central (Multiplicative.ofAdd 1)).base = k⁻¹ := by
    simp [hrbase, NormalizedIntCocycle.central]
  constructor
  · intro hz
    change (completionLift ρ hρ x r).height = 0 at hz
    change 0 < _ ∨ (_ = 0 ∧ (ρ _ x ≠ x ∨ L.order.lt 1 _)) at hp
    rcases hp with hp | ⟨_, hp | hp⟩
    · omega
    · exact (hp (hrbase ▸ hkx)).elim
    · simpa only [hrbase] using hp
  · intro hkpos
    have hkneg : ¬ L.order.lt 1 k⁻¹ := by
      let := L.order
      intro h
      have hh := L.mul_lt_mul_left k h
      simp only [mul_one, mul_inv_cancel] at hh
      exact lt_asymm hkpos hh
    have hp0 : 0 ≤ (completionLift ρ hρ x r).height := by
      rcases hp with hp | ⟨hp, _⟩ <;> omega
    change 0 < _ ∨ (_ = 0 ∧ (ρ _ x ≠ x ∨ L.order.lt 1 _)) at ht
    rw [hh, hbase] at ht
    rcases ht with ht | ⟨_, ht | ht⟩
    · change (completionLift ρ hρ x r).height = 0
      omega
    · exact (ht hki).elim
    · exact (hkneg ht).elim

/-- At a stabilizer label and a distinct orbit point, the circular sign records
exactly the stabilizer sign; the other orbit's circular position is irrelevant. -/
theorem completedCircularOrbitOrder_stabilizer_sbtw (k g : FreeGroup ι)
    (hk : k ≠ 1) (hkx : ρ k x = x) (hgx : ρ g x ≠ x) :
    (completedCircularOrbitOrder ρ hρ x L).order.sbtw 1 k g ↔ L.order.lt 1 k := by
  change (cofinalProductCircularGroupOrder (completionOrder ρ hρ x L)
    (completionOrder_center_positive ρ hρ x L)
    (completionOrder_center_cofinal ρ hρ x L)).order.sbtw 1 k g ↔ _
  rw [cofinalProductCircularGroupOrder_sbtw_one]
  have hp := cofinalProductRepresentative_pos (completionOrder ρ hρ x L)
    (completionOrder_center_positive ρ hρ x L) (completionOrder_center_cofinal ρ hρ x L) hk
  rw [and_iff_right hp]
  change (completionOrder ρ hρ x L).order.lt
    (completionRepresentative ρ hρ x L k) (completionRepresentative ρ hρ x L g) ↔ _
  rw [completionOrder_lt_iff, completionRepresentative_lift ρ hρ x L g hgx]
  let r := completionLift ρ hρ x (completionRepresentative ρ hρ x L k)
  have hrbase : r.base = k := by simp [r]
  have hr0 : 0 ≤ r.height := by
    have hp' := (completionOrder_lt_iff ρ hρ x L 1
      (completionRepresentative ρ hρ x L k)).mp hp
    simp only [map_one, inv_one, one_mul] at hp'
    change 0 < r.height ∨ (r.height = 0 ∧ _) at hp'
    rcases hp' with hp' | ⟨hp', _⟩ <;> omega
  have hcarry : (orbitCocycle ρ hρ x).value k⁻¹ g = 0 := by
    have hki : ρ k⁻¹ x = x := by
      have he := congrArg (ρ k⁻¹) hkx
      simpa using he.symm
    change CircularCarry.value x (ρ k⁻¹ x) (ρ (k⁻¹ * g) x) = 0
    rw [hki]
    simp
  have hmove : ρ (k⁻¹ * g) x ≠ x := by
    intro he
    apply hgx
    have he' := congrArg (ρ k) he
    simpa only [← Equiv.Perm.mul_apply, ← map_mul, mul_inv_cancel_left, hkx] using he'
  change (0 < -r.height - (orbitCocycle ρ hρ x).value r.base⁻¹ r.base + 0 +
      (orbitCocycle ρ hρ x).value r.base⁻¹ g ∨
    (-r.height - (orbitCocycle ρ hρ x).value r.base⁻¹ r.base + 0 +
      (orbitCocycle ρ hρ x).value r.base⁻¹ g = 0 ∧
      (ρ (r.base⁻¹ * g) x ≠ x ∨ L.order.lt 1 (r.base⁻¹ * g)))) ↔ _
  rw [hrbase, orbitCocycle_inverse_rev, ite_eq_left hkx, hcarry]
  have hz := completionRepresentative_stabilizer_height_zero_iff ρ hρ x L k hk hkx
  change r.height = 0 ↔ L.order.lt 1 k at hz
  simp only [sub_zero, add_zero, neg_eq_zero]
  have hn : ¬ 0 < -r.height := by omega
  simp only [hn, false_or]
  exact (and_iff_left (Or.inl hmove)).trans hz

/-- Opposite stabilizer resolutions give genuinely distinct completed circular
orders whenever a nonidentity stabilizer and another orbit point exist. -/
theorem completedCircularOrbitOrder_ne_reverse (k g : FreeGroup ι)
    (hk : k ≠ 1) (hkx : ρ k x = x) (hgx : ρ g x ≠ x) :
    completedCircularOrbitOrder ρ hρ x L ≠ completedCircularOrbitOrder ρ hρ x L.reverse := by
  intro he
  have heq : L.order.lt 1 k ↔ L.order.lt k 1 := by
    rw [← completedCircularOrbitOrder_stabilizer_sbtw ρ hρ x L k g hk hkx hgx, he]
    exact completedCircularOrbitOrder_stabilizer_sbtw ρ hρ x L.reverse k g hk hkx hgx
  let := L.order
  rcases lt_or_gt_of_ne (Ne.symm hk) with h | h
  · exact lt_asymm h (heq.mp h)
  · exact lt_asymm (heq.mpr h) h

include hρ L in
/-- A collision supplies a distinct completion while retaining every protected
nondegenerate orbit sign. Either stabilizer orientation may be the original
order, but the two cannot both be. -/
theorem exists_distinct_completion_of_stabilizer
    (O : CircularGroupOrder (FreeGroup ι)) (S : Finset (FreeGroup ι))
    (hinj : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → ρ a x ≠ ρ b x)
    (hsign : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S,
      sbtw (ρ a x) (ρ b x) (ρ c x) ↔ O.order.sbtw a b c)
    (k g : FreeGroup ι) (hk : k ≠ 1) (hkx : ρ k x = x) (hgx : ρ g x ≠ x) :
    ∃ P : CircularGroupOrder (FreeGroup ι), P ≠ O ∧
      ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, P.order.sbtw a b c ↔ O.order.sbtw a b c := by
  classical
  have hne := completedCircularOrbitOrder_ne_reverse ρ hρ x L k g hk hkx hgx
  have hchoice : ∃ K : LeftGroupOrder (FreeGroup ι),
      completedCircularOrbitOrder ρ hρ x K ≠ O := by
    by_cases he : completedCircularOrbitOrder ρ hρ x L = O
    · exact ⟨L.reverse, fun hr => hne (he.trans hr.symm)⟩
    · exact ⟨L, he⟩
  obtain ⟨K, hK⟩ := hchoice
  refine ⟨completedCircularOrbitOrder ρ hρ x K, hK, ?_⟩
  intro a ha b hb c hc
  exact completedCircularOrbitOrder_sign_of_orbit_sign ρ hρ x K O a b c
    (hinj a ha b hb) (hinj b hb c hc) (hinj c hc a ha) (hsign a ha b hb c hc)

/-- Actual approximate actions with a nontrivial stabilizer obstruct isolation.
The approximations need only preserve finitely many orbit points and their
signs; their full orbits need not be free. -/
theorem circularOrder_not_isolated_of_coincidences
    (O : CircularGroupOrder (FreeGroup ι))
    (happrox : ∀ S : Finset (FreeGroup ι),
      ∃ (σ : FreeGroup ι →* Equiv.Perm X) (_hσ : ∀ g, PreservesCircular (σ g)) (y : X),
        (∀ a ∈ S, ∀ b ∈ S, a ≠ b → σ a y ≠ σ b y) ∧
        (∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S,
          sbtw (σ a y) (σ b y) (σ c y) ↔ O.order.sbtw a b c) ∧
        ∃ k g, k ≠ 1 ∧ σ k y = y ∧ σ g y ≠ y) :
    ¬ IsOpen ({O} : Set (CircularGroupOrder (FreeGroup ι))) := by
  classical
  apply circularOrder_not_isolated_of_finite_signs
  intro F
  let S : Finset (FreeGroup ι) :=
    F.image Prod.fst ∪ F.image (fun p => p.2.1) ∪ F.image (fun p => p.2.2)
  obtain ⟨σ, hσ, y, hinj, hsign, k, g, hk, hky, hgy⟩ := happrox S
  obtain ⟨P, hne, hP⟩ := exists_distinct_completion_of_stabilizer σ hσ y
    (freeGroupLeftOrderOfCircular O) O S hinj hsign k g hk hky hgy
  refine ⟨P, hne, ?_⟩
  intro p hp
  have h1 : p.1 ∈ S :=
    Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨p, hp, rfl⟩))
  have h2 : p.2.1 ∈ S :=
    Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨p, hp, rfl⟩))
  have h3 : p.2.2 ∈ S := Finset.mem_union_right _ (Finset.mem_image.mpr ⟨p, hp, rfl⟩)
  simpa only [circularOrderSign, decide_eq_decide] using hP p.1 h1 p.2.1 h2 p.2.2 h3

end CircularDynamics
end FnZPositiveCones
