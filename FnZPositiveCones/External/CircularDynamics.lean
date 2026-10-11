module

public import FnZPositiveCones.External.CircularTopology
public import Mathlib.GroupTheory.FreeGroup.Orbit

@[expose] public section

/-!
Finite orbit calculations for the generator perturbation in Mann–Rivas,
Proposition 4.7. These lemmas include inverse letters and do not assume the
existence of a supported perturbation or the ping-pong domains.
-/
namespace FnZPositiveCones
namespace CircularDynamics
universe u v
variable {ι : Type u} {X : Type v}

/-- A signed free letter; `true` is the generator and `false` its inverse. -/
def letterPerm (ρ : ι → Equiv.Perm X) (s : ι × Bool) : Equiv.Perm X :=
  cond s.2 (ρ s.1) (ρ s.1)⁻¹

/-- Evaluation is right-to-left, as for a left action. -/
def evalWord (ρ : ι → Equiv.Perm X) : List (ι × Bool) → X → X
  | [], x => x
  | s :: w, x => letterPerm ρ s (evalWord ρ w x)

/-- The actual free-group homomorphism agrees with evaluation of signed words. -/
theorem lift_mk_apply (ρ : ι → Equiv.Perm X) (w : List (ι × Bool)) (x : X) :
    FreeGroup.lift ρ (FreeGroup.mk w) x = evalWord ρ w x := by
  rw [FreeGroup.lift_mk]
  induction w with
  | nil => rfl
  | cons s w ih =>
      simp only [List.map_cons, List.prod_cons, Equiv.Perm.mul_apply, ih]
      rfl

/-- All intermediate orbit points, including both the initial and final point. -/
def wordTrace (ρ : ι → Equiv.Perm X) (x : X) : List (ι × Bool) → List X
  | [] => [x]
  | s :: w => evalWord ρ (s :: w) x :: wordTrace ρ x w

@[simp] theorem evalWord_mem_wordTrace (ρ : ι → Equiv.Perm X) (x : X)
    (w : List (ι × Bool)) : evalWord ρ w x ∈ wordTrace ρ x w := by
  cases w <;> simp [wordTrace, evalWord]

/-- Change one signed generator by postcomposition with `h`. The underlying
positive generator is changed on the correct side when the chosen sign is negative. -/
noncomputable def perturb (ρ : ι → Equiv.Perm X) (s : ι × Bool)
    (h : Equiv.Perm X) : ι → Equiv.Perm X := by
  classical
  exact fun i => if i = s.1 then cond s.2 (h * ρ i) (ρ i * h⁻¹) else ρ i

/-- The designated signed generator is postcomposed with the perturbation. -/
theorem letterPerm_perturb_same (ρ : ι → Equiv.Perm X) (s : ι × Bool)
    (h : Equiv.Perm X) : letterPerm (perturb ρ s h) s = h * letterPerm ρ s := by
  rcases s with ⟨i, b⟩
  cases b <;> simp [letterPerm, perturb]

/-- The inverse letter is precomposed with the inverse perturbation. -/
theorem letterPerm_perturb_inverse (ρ : ι → Equiv.Perm X) (s : ι × Bool)
    (h : Equiv.Perm X) :
    letterPerm (perturb ρ s h) (s.1, !s.2) = letterPerm ρ (s.1, !s.2) * h⁻¹ := by
  rcases s with ⟨i, b⟩
  cases b <;> simp [letterPerm, perturb]

/-- Other underlying generators are unchanged. -/
theorem letterPerm_perturb_other (ρ : ι → Equiv.Perm X) (s t : ι × Bool)
    (h : Equiv.Perm X) (hne : t.1 ≠ s.1) :
    letterPerm (perturb ρ s h) t = letterPerm ρ t := by
  simp [letterPerm, perturb, hne]

/-- Fixing both ends of one original orbit edge preserves that edge, for either sign. -/
theorem letterPerm_perturb_apply_of_fixed (ρ : ι → Equiv.Perm X) (s t : ι × Bool)
    (h : Equiv.Perm X) (x : X) (hx : h x = x) (hy : h (letterPerm ρ t x) = letterPerm ρ t x) :
    letterPerm (perturb ρ s h) t x = letterPerm ρ t x := by
  classical
  by_cases hi : t.1 = s.1
  · rcases s with ⟨i, b⟩
    rcases t with ⟨j, c⟩
    dsimp at hi
    subst j
    have hx' : h⁻¹ x = x := by
      apply h.injective
      simpa using hx.symm
    cases b <;> cases c <;>
      simp_all [letterPerm, perturb, Equiv.Perm.mul_apply]
  · rw [letterPerm_perturb_other ρ s t h hi]

/-- A perturbation fixing the original finite itinerary leaves its endpoint unchanged. -/
theorem evalWord_perturb_of_trace_fixed (ρ : ι → Equiv.Perm X) (s : ι × Bool)
    (h : Equiv.Perm X) (x : X) (w : List (ι × Bool))
    (hfix : ∀ y ∈ wordTrace ρ x w, h y = y) :
    evalWord (perturb ρ s h) w x = evalWord ρ w x := by
  induction w with
  | nil => rfl
  | cons t w ih =>
      have hf : ∀ y ∈ wordTrace ρ x w, h y = y :=
        fun y hy => hfix y (List.mem_cons_of_mem _ hy)
      change letterPerm (perturb ρ s h) t (evalWord (perturb ρ s h) w x) =
        letterPerm ρ t (evalWord ρ w x)
      rw [ih hf]
      exact letterPerm_perturb_apply_of_fixed ρ s t h _
        (hf _ (evalWord_mem_wordTrace ρ x w)) (hfix _ (List.mem_cons_self))

/-- The same itinerary statement for the genuine free-group action. -/
theorem lift_mk_perturb_of_trace_fixed (ρ : ι → Equiv.Perm X) (s : ι × Bool)
    (h : Equiv.Perm X) (x : X) (w : List (ι × Bool))
    (hfix : ∀ y ∈ wordTrace ρ x w, h y = y) :
    FreeGroup.lift (perturb ρ s h) (FreeGroup.mk w) x = FreeGroup.lift ρ (FreeGroup.mk w) x := by
  simp only [lift_mk_apply]
  exact evalWord_perturb_of_trace_fixed ρ s h x w hfix

/-- The final occurrence of the chosen signed generator moves exactly by `h`,
while its entire preceding itinerary is unchanged. -/
theorem evalWord_perturb_head (ρ : ι → Equiv.Perm X) (s : ι × Bool)
    (h : Equiv.Perm X) (x : X) (w : List (ι × Bool))
    (hfix : ∀ y ∈ wordTrace ρ x w, h y = y) :
    evalWord (perturb ρ s h) (s :: w) x = h (evalWord ρ (s :: w) x) := by
  change letterPerm (perturb ρ s h) s (evalWord (perturb ρ s h) w x) =
    h (letterPerm ρ s (evalWord ρ w x))
  rw [evalWord_perturb_of_trace_fixed ρ s h x w hfix, letterPerm_perturb_same]
  rfl

/-- Any different signed head stays fixed, including the inverse of the changed
letter. Only its preceding itinerary needs to avoid the perturbation. -/
theorem evalWord_perturb_other_head (ρ : ι → Equiv.Perm X) (s t : ι × Bool)
    (h : Equiv.Perm X) (x : X) (w : List (ι × Bool)) (hne : t ≠ s)
    (hfix : ∀ y ∈ wordTrace ρ x w, h y = y) :
    evalWord (perturb ρ s h) (t :: w) x = evalWord ρ (t :: w) x := by
  change letterPerm (perturb ρ s h) t (evalWord (perturb ρ s h) w x) =
    letterPerm ρ t (evalWord ρ w x)
  rw [evalWord_perturb_of_trace_fixed ρ s h x w hfix]
  by_cases hi : t.1 = s.1
  · have ht : t = (s.1, !s.2) := by
      rcases s with ⟨i, b⟩
      rcases t with ⟨j, c⟩
      dsimp at hi
      subst j
      cases b <;> cases c <;> simp_all
    rw [ht, letterPerm_perturb_inverse]
    change letterPerm ρ (s.1, !s.2) (h⁻¹ (evalWord ρ w x)) = _
    have hf := hfix _ (evalWord_mem_wordTrace ρ x w)
    have hf' : h⁻¹ (evalWord ρ w x) = evalWord ρ w x := by
      apply h.injective
      simpa using hf.symm
    rw [hf']
  · rw [letterPerm_perturb_other ρ s t h hi]

section Circular
variable [CircularOrder X]

/-- Preservation of the actual circular relation by a permutation. -/
def PreservesCircular (e : Equiv.Perm X) : Prop :=
  ∀ a b c, btw (e a) (e b) (e c) ↔ btw a b c

theorem preservesCircular_one : PreservesCircular (1 : Equiv.Perm X) := by
  intro a b c
  rfl

theorem preservesCircular_mul {e f : Equiv.Perm X}
    (he : PreservesCircular e) (hf : PreservesCircular f) : PreservesCircular (e * f) := by
  intro a b c
  exact (he _ _ _).trans (hf _ _ _)

theorem preservesCircular_inv {e : Equiv.Perm X}
    (he : PreservesCircular e) : PreservesCircular e⁻¹ := by
  intro a b c
  simpa using (he (e⁻¹ a) (e⁻¹ b) (e⁻¹ c)).symm

/-- Free extension of circular permutations still preserves the circle order. -/
theorem preservesCircular_lift (ρ : ι → Equiv.Perm X) (hρ : ∀ i, PreservesCircular (ρ i))
    (g : FreeGroup ι) : PreservesCircular (FreeGroup.lift ρ g) := by
  induction g using FreeGroup.induction_on with
  | one => simpa using (preservesCircular_one (X := X))
  | of i => simpa using hρ i
  | inv_of i ih => simpa using preservesCircular_inv ih
  | mul g h hg hh => simpa using preservesCircular_mul hg hh

/-- Perturbing by a circular permutation preserves the defining generator condition. -/
theorem preservesCircular_perturb (ρ : ι → Equiv.Perm X) (hρ : ∀ i, PreservesCircular (ρ i))
    (s : ι × Bool) (h : Equiv.Perm X) (hh : PreservesCircular h) :
    ∀ i, PreservesCircular (perturb ρ s h i) := by
  classical
  intro i
  by_cases hi : i = s.1
  · cases hb : s.2
    · simpa [perturb, hi, hb] using preservesCircular_mul (hρ i) (preservesCircular_inv hh)
    · simpa [perturb, hi, hb] using preservesCircular_mul hh (hρ i)
  · simpa [perturb, hi] using hρ i

/-- Circular orders pull back along actual injections. -/
@[instance_reducible] def circularOrderPullback {Y : Type*} (f : Y → X)
    (hf : Function.Injective f) : CircularOrder Y where
  btw a b c := btw (f a) (f b) (f c)
  sbtw a b c := sbtw (f a) (f b) (f c)
  btw_refl a := btw_refl (f a)
  btw_cyclic_left := btw_cyclic_left
  sbtw_iff_btw_not_btw := sbtw_iff_btw_not_btw
  sbtw_trans_left := sbtw_trans_left
  btw_antisymm hab hba := (btw_antisymm hab hba).elim (fun h => Or.inl (hf h))
    (fun h => h.elim (fun h => Or.inr (Or.inl (hf h))) (fun h => Or.inr (Or.inr (hf h))))
  btw_total a b c := btw_total (f a) (f b) (f c)

/-- An injective orbit of a circular action induces an actual invariant circular order. -/
def circularOrbitOrder {G : Type*} [Group G] (ρ : G →* Equiv.Perm X)
    (hρ : ∀ g, PreservesCircular (ρ g)) (x : X)
    (hx : Function.Injective (fun g => ρ g x)) : CircularGroupOrder G where
  order := circularOrderPullback (fun g => ρ g x) hx
  mul_btw_mul_left a b c d := by
    change btw (ρ (a * b) x) (ρ (a * c) x) (ρ (a * d) x) ↔
      btw (ρ b x) (ρ c x) (ρ d x)
    simpa only [map_mul, Equiv.Perm.mul_apply] using hρ a (ρ b x) (ρ c x) (ρ d x)

@[simp] theorem circularOrbitOrder_sbtw {G : Type*} [Group G]
    (ρ : G →* Equiv.Perm X) (hρ : ∀ g, PreservesCircular (ρ g)) (x : X)
    (hx : Function.Injective (fun g => ρ g x)) (a b c : G) :
    (circularOrbitOrder ρ hρ x hx).order.sbtw a b c ↔ sbtw (ρ a x) (ρ b x) (ρ c x) := Iff.rfl

/-- Fixing the traces of three words preserves their induced circular sign. -/
theorem circularOrbitOrder_perturb_sbtw
    (ρ : ι → Equiv.Perm X) (hρ : ∀ i, PreservesCircular (ρ i))
    (s : ι × Bool) (h : Equiv.Perm X) (hh : PreservesCircular h) (x : X)
    (hx : Function.Injective (fun g => FreeGroup.lift ρ g x))
    (hx' : Function.Injective (fun g => FreeGroup.lift (perturb ρ s h) g x))
    (a b c : List (ι × Bool))
    (hfix : ∀ w ∈ [a, b, c], ∀ y ∈ wordTrace ρ x w, h y = y) :
    (circularOrbitOrder (FreeGroup.lift (perturb ρ s h))
      (preservesCircular_lift _ (preservesCircular_perturb ρ hρ s h hh)) x hx').order.sbtw
        (FreeGroup.mk a) (FreeGroup.mk b) (FreeGroup.mk c) ↔
    (circularOrbitOrder (FreeGroup.lift ρ) (preservesCircular_lift ρ hρ) x hx).order.sbtw
        (FreeGroup.mk a) (FreeGroup.mk b) (FreeGroup.mk c) := by
  simp only [circularOrbitOrder_sbtw]
  rw [lift_mk_perturb_of_trace_fixed ρ s h x a (hfix a (by simp)),
    lift_mk_perturb_of_trace_fixed ρ s h x b (hfix b (by simp)),
    lift_mk_perturb_of_trace_fixed ρ s h x c (hfix c (by simp))]

/-- The source's changed-head calculation gives an actual differing circular sign,
provided that the perturbed action has a free base orbit. -/
theorem circularOrbitOrder_perturb_ne
    (ρ : ι → Equiv.Perm X) (hρ : ∀ i, PreservesCircular (ρ i))
    (s t : ι × Bool) (h : Equiv.Perm X) (hh : PreservesCircular h) (x : X)
    (hx : Function.Injective (fun g => FreeGroup.lift ρ g x))
    (hx' : Function.Injective (fun g => FreeGroup.lift (perturb ρ s h) g x))
    (w v : List (ι × Bool)) (hst : t ≠ s)
    (hw : ∀ y ∈ wordTrace ρ x w, h y = y) (hv : ∀ y ∈ wordTrace ρ x v, h y = y)
    (hchange : ¬(sbtw (h (evalWord ρ (s :: w) x)) (evalWord ρ (t :: v) x) x ↔
      sbtw (evalWord ρ (s :: w) x) (evalWord ρ (t :: v) x) x)) :
    circularOrbitOrder (FreeGroup.lift (perturb ρ s h))
      (preservesCircular_lift _ (preservesCircular_perturb ρ hρ s h hh)) x hx' ≠
    circularOrbitOrder (FreeGroup.lift ρ) (preservesCircular_lift ρ hρ) x hx := by
  intro he
  have hs := congrArg (fun O : CircularGroupOrder (FreeGroup ι) =>
    O.order.sbtw (FreeGroup.mk (s :: w)) (FreeGroup.mk (t :: v)) 1) he
  apply hchange
  change sbtw (FreeGroup.lift (perturb ρ s h) (FreeGroup.mk (s :: w)) x)
      (FreeGroup.lift (perturb ρ s h) (FreeGroup.mk (t :: v)) x)
      (FreeGroup.lift (perturb ρ s h) 1 x) =
    sbtw (FreeGroup.lift ρ (FreeGroup.mk (s :: w)) x)
      (FreeGroup.lift ρ (FreeGroup.mk (t :: v)) x) (FreeGroup.lift ρ 1 x) at hs
  simpa only [lift_mk_apply, map_one, Equiv.Perm.one_apply,
    evalWord_perturb_head ρ s h x w hw,
    evalWord_perturb_other_head ρ s t h x v hst hv] using hs.to_iff

end Circular

section Topology
variable {G : Type*} [Group G]

/-- A finite circular-sign cylinder is genuinely open in the supplied order topology. -/
theorem isOpen_circularSignCylinder (O : CircularGroupOrder G) (F : Finset (G × G × G)) :
    IsOpen {P : CircularGroupOrder G | ∀ p ∈ F, circularOrderSign P p = circularOrderSign O p} := by
  apply isOpen_induced_iff.mpr
  refine ⟨Set.pi (F : Set (G × G × G)) (fun p => {circularOrderSign O p}), ?_, ?_⟩
  · exact isOpen_set_pi F.finite_toSet (fun _ _ => isOpen_discrete _)
  · rfl

/-- Isolation in the circular sign topology is exactly determination by finitely
many actual ternary comparisons. -/
theorem circularOrder_isolated_iff_finite_signs (O : CircularGroupOrder G) :
    IsOpen ({O} : Set (CircularGroupOrder G)) ↔
      ∃ F : Finset (G × G × G), ∀ P : CircularGroupOrder G,
        (∀ p ∈ F, circularOrderSign P p = circularOrderSign O p) → P = O := by
  constructor
  · intro hi
    obtain ⟨U, hU, hpre⟩ := isOpen_induced_iff.mp hi
    have hOU : circularOrderSign O ∈ U := by
      have : O ∈ circularOrderSign ⁻¹' U := by rw [hpre]; exact Set.mem_singleton O
      exact this
    obtain ⟨F, V, hV, hsub⟩ := isOpen_pi_iff.mp hU (circularOrderSign O) hOU
    refine ⟨F, fun P hP => ?_⟩
    have hPU : circularOrderSign P ∈ U := hsub (fun p hp => (hP p hp) ▸ (hV p hp).2)
    exact Set.mem_singleton_iff.mp (hpre ▸ hPU)
  · rintro ⟨F, hF⟩
    have he : {P : CircularGroupOrder G | ∀ p ∈ F, circularOrderSign P p = circularOrderSign O p} = {O} := by
      ext P
      constructor
      · exact hF P
      · rintro rfl
        exact fun _ _ => rfl
    rw [← he]
    exact isOpen_circularSignCylinder O F

/-- Producing a distinct order on every finite comparison set proves nonisolation. -/
theorem circularOrder_not_isolated_of_finite_signs (O : CircularGroupOrder G)
    (h : ∀ F : Finset (G × G × G), ∃ P : CircularGroupOrder G,
      P ≠ O ∧ ∀ p ∈ F, circularOrderSign P p = circularOrderSign O p) :
    ¬ IsOpen ({O} : Set (CircularGroupOrder G)) := by
  intro hi
  obtain ⟨F, hF⟩ := (circularOrder_isolated_iff_finite_signs O).mp hi
  obtain ⟨P, hne, hP⟩ := h F
  exact hne (hF P hP)

end Topology

/-- A finite collection of itinerary-preserving circular perturbations with free
base orbit and a changed sign suffices for nonisolation. Existence of those
perturbations is an explicit hypothesis, not inferred here from failure of ping-pong. -/
theorem circularOrbitOrder_not_isolated_of_perturbations [CircularOrder X]
    (ρ : ι → Equiv.Perm X) (hρ : ∀ i, PreservesCircular (ρ i)) (x : X)
    (hx : Function.Injective (fun g => FreeGroup.lift ρ g x))
    (hpert : ∀ W : Finset (List (ι × Bool)),
      ∃ (s : ι × Bool) (h : Equiv.Perm X) (hh : PreservesCircular h)
        (hx' : Function.Injective (fun g => FreeGroup.lift (perturb ρ s h) g x)),
        (∀ w ∈ W, ∀ y ∈ wordTrace ρ x w, h y = y) ∧
        circularOrbitOrder (FreeGroup.lift (perturb ρ s h))
          (preservesCircular_lift _ (preservesCircular_perturb ρ hρ s h hh)) x hx' ≠
        circularOrbitOrder (FreeGroup.lift ρ) (preservesCircular_lift ρ hρ) x hx) :
    ¬ IsOpen ({circularOrbitOrder (FreeGroup.lift ρ) (preservesCircular_lift ρ hρ) x hx} :
      Set (CircularGroupOrder (FreeGroup ι))) := by
  classical
  apply circularOrder_not_isolated_of_finite_signs
  intro F
  let W : Finset (List (ι × Bool)) :=
    F.image (fun p => p.1.toWord) ∪ F.image (fun p => p.2.1.toWord) ∪ F.image (fun p => p.2.2.toWord)
  obtain ⟨s, h, hh, hx', hfix, hne⟩ := hpert W
  refine ⟨circularOrbitOrder (FreeGroup.lift (perturb ρ s h))
    (preservesCircular_lift _ (preservesCircular_perturb ρ hρ s h hh)) x hx', hne, ?_⟩
  intro p hp
  have hcoords (w : List (ι × Bool)) (hw : w ∈ [p.1.toWord, p.2.1.toWord, p.2.2.toWord]) :
      w ∈ W := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl <;> simp only [W, Finset.mem_union, Finset.mem_image]
    · exact Or.inl (Or.inl ⟨p, hp, rfl⟩)
    · exact Or.inl (Or.inr ⟨p, hp, rfl⟩)
    · exact Or.inr ⟨p, hp, rfl⟩
  have he := circularOrbitOrder_perturb_sbtw ρ hρ s h hh x hx hx'
    p.1.toWord p.2.1.toWord p.2.2.toWord (fun w hw => hfix w (hcoords w hw))
  simpa only [FreeGroup.mk_toWord, circularOrderSign, decide_eq_decide] using he

end CircularDynamics
end FnZPositiveCones
