module

public import FnZPositiveCones.External.NoncofinalTrajectory
public import Mathlib.Algebra.Group.End

@[expose] public section

/-!
# Primitive elements and the entry step in MMRT Claim 4

The primitive-entry step of MMRT Claim 4 is proved by compactness and Nielsen
descent. Failure of entry gives a uniform positive displacement for every
positive primitive on a compact interval. Elementary changes of a free basis
then decrease the sum of two generator displacements by that uniform amount,
contradicting its infimum. Explicit automorphisms supply the changed bases.
The final trajectory lemma records that the protection bound depends on the
chosen basis; no uniformity in all automorphisms is asserted.
-/

namespace FnZPositiveCones.NoncofinalPrimitiveEntry

open NoncofinalDynamics

universe u
variable {ι : Type u}

/-- A primitive is an image of a marked generator under an actual group
automorphism. The automorphism supplies the complete changed free basis. -/
def IsPrimitive (a : FreeGroup ι) : Prop :=
  ∃ e : FreeGroup ι ≃* FreeGroup ι, ∃ i : ι, e (FreeGroup.of i) = a

theorem primitive_of (i : ι) : IsPrimitive (FreeGroup.of i) :=
  ⟨MulEquiv.refl _, i, rfl⟩

theorem primitive_conj {a : FreeGroup ι} (ha : IsPrimitive a) (g : FreeGroup ι) :
    IsPrimitive (g * a * g⁻¹) := by
  obtain ⟨e, i, rfl⟩ := ha
  exact ⟨e.trans (MulAut.conj g), i, rfl⟩

/-- A fixed-point-free increasing homeomorphism has a single direction of
motion on the whole line. -/
theorem positive_everywhere_of_no_fixed (f : ℝ ≃o ℝ)
    (hn : ∀ y : ℝ, f y ≠ y) {x : ℝ} (hx : x < f x) :
    ∀ y : ℝ, y < f y := by
  intro y
  by_contra hy
  obtain ⟨z, hz⟩ := intermediate_value_univ₂ f.continuous continuous_id
    (le_of_not_gt hy) hx.le
  exact hn z hz

/-- Invert one marked free generator, fixing all other generators. -/
noncomputable def invertBasis (i : ι) : FreeGroup ι ≃* FreeGroup ι := by
  classical
  let f : FreeGroup ι →* FreeGroup ι :=
    FreeGroup.lift (fun j => if j = i then (FreeGroup.of j)⁻¹ else FreeGroup.of j)
  have hinv : f.comp f = MonoidHom.id _ := by
    apply FreeGroup.ext_hom
    intro j
    by_cases hji : j = i <;> simp [f, hji]
  exact
    { toFun := f
      invFun := f
      left_inv := fun g => congrArg (fun h : FreeGroup ι →* FreeGroup ι => h g) hinv
      right_inv := fun g => congrArg (fun h : FreeGroup ι →* FreeGroup ι => h g) hinv
      map_mul' := f.map_mul }

@[simp] theorem invertBasis_of [DecidableEq ι] (i j : ι) :
    invertBasis i (FreeGroup.of j) =
      if j = i then (FreeGroup.of j)⁻¹ else FreeGroup.of j := by
  classical
  simp [invertBasis]

/-- Elementary Nielsen subtraction: replace the `j`th generator by
`i⁻¹*j`, with inverse replacing it by `i*j`. -/
noncomputable def subtractBasis (i j : ι) (hij : i ≠ j) :
    FreeGroup ι ≃* FreeGroup ι := by
  classical
  let f : FreeGroup ι →* FreeGroup ι :=
    FreeGroup.lift (fun k => if k = j then (FreeGroup.of i)⁻¹ * FreeGroup.of j
      else FreeGroup.of k)
  let g : FreeGroup ι →* FreeGroup ι :=
    FreeGroup.lift (fun k => if k = j then FreeGroup.of i * FreeGroup.of j
      else FreeGroup.of k)
  have hgf : g.comp f = MonoidHom.id _ := by
    apply FreeGroup.ext_hom
    intro k
    by_cases hkj : k = j <;> simp [f, g, hkj, hij]
  have hfg : f.comp g = MonoidHom.id _ := by
    apply FreeGroup.ext_hom
    intro k
    by_cases hkj : k = j <;> simp [f, g, hkj, hij]
  exact
    { toFun := f
      invFun := g
      left_inv := fun w => congrArg (fun h : FreeGroup ι →* FreeGroup ι => h w) hgf
      right_inv := fun w => congrArg (fun h : FreeGroup ι →* FreeGroup ι => h w) hfg
      map_mul' := f.map_mul }

@[simp] theorem subtractBasis_of [DecidableEq ι] (i j : ι) (hij : i ≠ j) (k : ι) :
    subtractBasis i j hij (FreeGroup.of k) =
      if k = j then (FreeGroup.of i)⁻¹ * FreeGroup.of j else FreeGroup.of k := by
  classical
  simp [subtractBasis]

/-- An unbounded orbit of one primitive fixed point gives primitive fixed
points beyond every prescribed bound. No faithfulness is needed. -/
theorem primitive_fixed_unbounded
    (ρ : FreeGroup ι →* (ℝ ≃o ℝ)) {a : FreeGroup ι} (ha : IsPrimitive a)
    {x : ℝ} (hx : ρ a x = x)
    (hunbounded : ∀ b : ℝ, ∃ g : FreeGroup ι, b < ρ g x) (b : ℝ) :
    ∃ c : FreeGroup ι, IsPrimitive c ∧ ∃ y : ℝ, b < y ∧ ρ c y = y := by
  obtain ⟨g, hg⟩ := hunbounded b
  refine ⟨g * a * g⁻¹, primitive_conj ha g, ρ g x, hg, ?_⟩
  simp only [act_mul, act_inv_act, hx]

/-- In a minimal action, the absence of primitive fixed points on one far
right ray implies their absence everywhere. -/
theorem primitive_no_fixed_of_no_fixed_above
    (ρ : FreeGroup ι →* (ℝ ≃o ℝ))
    (hminimal : ∀ x : ℝ, DenseRange (fun g : FreeGroup ι => ρ g x))
    (b : ℝ)
    (hfar : ∀ a : FreeGroup ι, IsPrimitive a → ∀ x : ℝ, b < x → ρ a x ≠ x) :
    ∀ a : FreeGroup ι, IsPrimitive a → ∀ x : ℝ, ρ a x ≠ x := by
  intro a ha x hx
  have hu : ∀ B : ℝ, ∃ g : FreeGroup ι, B < ρ g x := by
    intro B
    exact (hminimal x).exists_mem_open isOpen_Ioi (Set.nonempty_Ioi)
  obtain ⟨c, hc, y, hby, hy⟩ := primitive_fixed_unbounded ρ ha hx hu b
  exact hfar c hc y hby hy

/-- If no positive primitive enters an interval, conjugation forces every
positive primitive to jump over every translate of that interval. -/
theorem translated_interval_jump
    (ρ : FreeGroup ι →* (ℝ ≃o ℝ)) {l r : ℝ}
    (hno : ∀ a : FreeGroup ι, IsPrimitive a → ρ a l ∉ Set.Ioo l r)
    {a : FreeGroup ι} (ha : IsPrimitive a) (hpos : ∀ x : ℝ, x < ρ a x)
    (g : FreeGroup ι) : ρ g r ≤ ρ a (ρ g l) := by
  have hp : IsPrimitive (g⁻¹ * a * (g⁻¹)⁻¹) := primitive_conj ha g⁻¹
  have hmove : l < ρ (g⁻¹ * a * (g⁻¹)⁻¹) l := by
    simpa only [act_mul, inv_inv, act_inv_act] using (ρ g⁻¹).strictMono (hpos (ρ g l))
  have hle : r ≤ ρ (g⁻¹ * a * (g⁻¹)⁻¹) l := by
    by_contra h
    exact hno _ hp ⟨hmove, lt_of_not_ge h⟩
  simpa only [act_mul, inv_inv, act_act_inv] using (ρ g).monotone hle

/-- Minimality and failure of primitive entry give a uniform positive lower
bound on the displacement of every positive primitive on a compact interval.
This is the compactness input for elementary Nielsen descent. -/
theorem uniform_displacement_of_no_entry
    (ρ : FreeGroup ι →* (ℝ ≃o ℝ))
    (hminimal : ∀ x : ℝ, DenseRange (fun g : FreeGroup ι => ρ g x))
    {l r : ℝ} (hlr : l < r)
    (hno : ∀ a : FreeGroup ι, IsPrimitive a → ρ a l ∉ Set.Ioo l r)
    (A B : ℝ) (hAB : A ≤ B) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a : FreeGroup ι, IsPrimitive a →
      (∀ x : ℝ, x < ρ a x) → ∀ x ∈ Set.Icc A B, x + δ ≤ ρ a x := by
  classical
  have hc (x : ℝ) : ∃ g : FreeGroup ι, ρ g l < x ∧ x < ρ g r := by
    obtain ⟨g, hg⟩ := (hminimal x).exists_mem_open isOpen_Ioo (Set.nonempty_Ioo.mpr hlr)
    refine ⟨g⁻¹, ?_, ?_⟩
    · simpa only [act_inv_act] using (ρ g⁻¹).strictMono hg.1
    · simpa only [act_inv_act] using (ρ g⁻¹).strictMono hg.2
  choose g hg using hc
  let δ : ℝ → ℝ := fun x => (ρ (g x) r - x) / 2
  have hδ (x : ℝ) : 0 < δ x := by dsimp [δ]; linarith [(hg x).2]
  let U : ℝ → Set ℝ := fun x => Set.Ioo (ρ (g x) l) (x + δ x)
  have hcover : Set.Icc A B ⊆ ⋃ x : ℝ, U x := by
    intro x _
    exact Set.mem_iUnion.mpr ⟨x, (hg x).1, by linarith [hδ x]⟩
  obtain ⟨t, ht⟩ := isCompact_Icc.elim_finite_subcover U (fun _ => isOpen_Ioo) hcover
  have htn : t.Nonempty := by
    obtain ⟨x, hx, _⟩ := Set.mem_iUnion₂.mp (ht (show A ∈ Set.Icc A B from ⟨le_rfl, hAB⟩))
    exact ⟨x, hx⟩
  refine ⟨t.inf' htn δ, (Finset.lt_inf'_iff _).mpr (fun x _ => hδ x), ?_⟩
  intro a ha hpos x hx
  obtain ⟨y, hyt, hxy⟩ := Set.mem_iUnion₂.mp (ht hx)
  have hlower := translated_interval_jump ρ hno ha hpos (g y)
  have hpx : ρ (g y) r < ρ a x := hlower.trans_lt ((ρ a).strictMono hxy.1)
  have hsmall : t.inf' htn δ ≤ δ y := Finset.inf'_le _ hyt
  have hupper : x < y + δ y := hxy.2
  dsimp [δ] at hupper hsmall
  linarith

private theorem nielsen_decrease_right
    (ρ : FreeGroup ι →* (ℝ ≃o ℝ)) (i j : ι) (hij : i ≠ j)
    (hn : ∀ a : FreeGroup ι, IsPrimitive a → ∀ x : ℝ, ρ a x ≠ x)
    (x B δ : ℝ)
    (hδ : ∀ a : FreeGroup ι, IsPrimitive a → (∀ y : ℝ, y < ρ a y) →
      ∀ y ∈ Set.Icc x B, y + δ ≤ ρ a y)
    (e : FreeGroup ι ≃* FreeGroup ι)
    (hi : ∀ y : ℝ, y < ρ (e (FreeGroup.of i)) y)
    (_hj : ∀ y : ℝ, y < ρ (e (FreeGroup.of j)) y)
    (hiB : ρ (e (FreeGroup.of i)) x ≤ B)
    (hjB : ρ (e (FreeGroup.of j)) x ≤ B)
    (hijx : ρ (e (FreeGroup.of i)) x < ρ (e (FreeGroup.of j)) x) :
    ∃ e' : FreeGroup ι ≃* FreeGroup ι,
      (∀ y : ℝ, y < ρ (e' (FreeGroup.of i)) y) ∧
      (∀ y : ℝ, y < ρ (e' (FreeGroup.of j)) y) ∧
      ρ (e' (FreeGroup.of i)) x ≤ B ∧ ρ (e' (FreeGroup.of j)) x ≤ B ∧
      ρ (e' (FreeGroup.of i)) x + ρ (e' (FreeGroup.of j)) x + δ ≤
        ρ (e (FreeGroup.of i)) x + ρ (e (FreeGroup.of j)) x := by
  classical
  let e' := (subtractBasis i j hij).trans e
  have hei : e' (FreeGroup.of i) = e (FreeGroup.of i) := by simp [e', hij]
  have hej : e' (FreeGroup.of j) = (e (FreeGroup.of i))⁻¹ * e (FreeGroup.of j) := by
    simp [e']
  have hp : IsPrimitive (e' (FreeGroup.of j)) := ⟨e', j, rfl⟩
  have hx : x < ρ (e' (FreeGroup.of j)) x := by
    rw [hej, act_mul]
    simpa only [act_inv_act] using (ρ (e (FreeGroup.of i))⁻¹).strictMono hijx
  have hpos := positive_everywhere_of_no_fixed _ (hn _ hp) hx
  have hcancel : ρ (e (FreeGroup.of i)) (ρ (e' (FreeGroup.of j)) x) =
      ρ (e (FreeGroup.of j)) x := by
    rw [hej, act_mul, act_act_inv]
  have hcB : ρ (e' (FreeGroup.of j)) x ≤ B := by
    exact (hi _).le.trans (hcancel.symm ▸ hjB)
  have hdec := hδ (e (FreeGroup.of i)) ⟨e, i, rfl⟩ hi _ ⟨hx.le, hcB⟩
  rw [hcancel] at hdec
  exact ⟨e', by simpa only [hei] using hi, hpos, by simpa only [hei] using hiB,
    hcB, by rw [hei]; linarith⟩

/-- Nielsen subtraction of whichever of two positive marked basis elements
moves the basepoint farther strictly decreases their total displacement. -/
theorem nielsen_decrease
    (ρ : FreeGroup ι →* (ℝ ≃o ℝ)) (i j : ι) (hij : i ≠ j)
    (hn : ∀ a : FreeGroup ι, IsPrimitive a → ∀ x : ℝ, ρ a x ≠ x)
    (x B δ : ℝ)
    (hδ : ∀ a : FreeGroup ι, IsPrimitive a → (∀ y : ℝ, y < ρ a y) →
      ∀ y ∈ Set.Icc x B, y + δ ≤ ρ a y)
    (e : FreeGroup ι ≃* FreeGroup ι)
    (hi : ∀ y : ℝ, y < ρ (e (FreeGroup.of i)) y)
    (hj : ∀ y : ℝ, y < ρ (e (FreeGroup.of j)) y)
    (hiB : ρ (e (FreeGroup.of i)) x ≤ B)
    (hjB : ρ (e (FreeGroup.of j)) x ≤ B) :
    ∃ e' : FreeGroup ι ≃* FreeGroup ι,
      (∀ y : ℝ, y < ρ (e' (FreeGroup.of i)) y) ∧
      (∀ y : ℝ, y < ρ (e' (FreeGroup.of j)) y) ∧
      ρ (e' (FreeGroup.of i)) x ≤ B ∧ ρ (e' (FreeGroup.of j)) x ≤ B ∧
      ρ (e' (FreeGroup.of i)) x + ρ (e' (FreeGroup.of j)) x + δ ≤
        ρ (e (FreeGroup.of i)) x + ρ (e (FreeGroup.of j)) x := by
  classical
  have hne : ρ (e (FreeGroup.of i)) x ≠ ρ (e (FreeGroup.of j)) x := by
    intro he
    let e' := (subtractBasis i j hij).trans e
    have hprim : IsPrimitive (e' (FreeGroup.of j)) := ⟨e', j, rfl⟩
    apply hn _ hprim x
    simp only [e', MulEquiv.trans_apply, subtractBasis_of, ite_true, map_mul, map_inv]
    rw [RelIso.mul_apply, ← map_inv, ← he, act_inv_act]
  rcases hne.lt_or_gt with h | h
  · exact nielsen_decrease_right ρ i j hij hn x B δ hδ e hi hj hiB hjB h
  · obtain ⟨e', hi', hj', hiB', hjB', hdec⟩ :=
      nielsen_decrease_right ρ j i hij.symm hn x B δ hδ e hj hi hjB hiB h
    exact ⟨e', hj', hi', hjB', hiB', by linarith⟩

private theorem orient_basis_generator
    (ρ : FreeGroup ι →* (ℝ ≃o ℝ))
    (hn : ∀ a : FreeGroup ι, IsPrimitive a → ∀ x : ℝ, ρ a x ≠ x)
    (e : FreeGroup ι ≃* FreeGroup ι) (i : ι) (x : ℝ) :
    ∃ e' : FreeGroup ι ≃* FreeGroup ι,
      (∀ y : ℝ, y < ρ (e' (FreeGroup.of i)) y) ∧
      ∀ j : ι, j ≠ i → e' (FreeGroup.of j) = e (FreeGroup.of j) := by
  classical
  by_cases hp : x < ρ (e (FreeGroup.of i)) x
  · exact ⟨e, positive_everywhere_of_no_fixed _ (hn _ ⟨e, i, rfl⟩) hp,
      fun _ _ => rfl⟩
  · let e' := (invertBasis i).trans e
    have he : e' (FreeGroup.of i) = (e (FreeGroup.of i))⁻¹ := by simp [e']
    have hneg : ρ (e (FreeGroup.of i)) x < x :=
      lt_of_le_of_ne (le_of_not_gt hp) (hn _ ⟨e, i, rfl⟩ x)
    have hpos : x < ρ (e' (FreeGroup.of i)) x := by
      rw [he]
      simpa only [act_inv_act] using (ρ (e (FreeGroup.of i))⁻¹).strictMono hneg
    refine ⟨e', positive_everywhere_of_no_fixed _ (hn _ ⟨e', i, rfl⟩) hpos, ?_⟩
    intro j hji
    simp [e', hji]

/-- Two marked basis elements can be oriented positively without changing
their membership in one common free basis. -/
theorem exists_positive_basis_pair
    (ρ : FreeGroup ι →* (ℝ ≃o ℝ))
    (hn : ∀ a : FreeGroup ι, IsPrimitive a → ∀ x : ℝ, ρ a x ≠ x)
    (i j : ι) (hij : i ≠ j) :
    ∃ e : FreeGroup ι ≃* FreeGroup ι,
      (∀ y : ℝ, y < ρ (e (FreeGroup.of i)) y) ∧
      (∀ y : ℝ, y < ρ (e (FreeGroup.of j)) y) := by
  obtain ⟨e, hi, _⟩ := orient_basis_generator ρ hn (MulEquiv.refl _) i 0
  obtain ⟨e', hj, he⟩ := orient_basis_generator ρ hn e j 0
  exact ⟨e', by simpa only [he i hij] using hi, hj⟩

/-- In a minimal real action of a nonabelian free group, if every primitive
is fixed-point-free, some primitive moves any prescribed left endpoint
strictly inside any prescribed nonempty interval.

The proof uses compactness and elementary Nielsen subtraction, rather than
assuming that the original marked generators enter the interval. -/
theorem exists_primitive_entry [Nontrivial ι]
    (ρ : FreeGroup ι →* (ℝ ≃o ℝ))
    (hminimal : ∀ x : ℝ, DenseRange (fun g : FreeGroup ι => ρ g x))
    (hn : ∀ a : FreeGroup ι, IsPrimitive a → ∀ x : ℝ, ρ a x ≠ x)
    {l r : ℝ} (hlr : l < r) :
    ∃ a : FreeGroup ι, IsPrimitive a ∧ ρ a l ∈ Set.Ioo l r := by
  classical
  by_contra! hno
  obtain ⟨i, j, hij⟩ := exists_pair_ne ι
  obtain ⟨e, hei, hej⟩ := exists_positive_basis_pair ρ hn i j hij
  let B := max (ρ (e (FreeGroup.of i)) l) (ρ (e (FreeGroup.of j)) l)
  have hlB : l ≤ B := (hei l).le.trans (le_max_left _ _)
  obtain ⟨δ, hδ, hmove⟩ := uniform_displacement_of_no_entry ρ hminimal hlr hno l B hlB
  let good : (FreeGroup ι ≃* FreeGroup ι) → Prop := fun f =>
    (∀ y : ℝ, y < ρ (f (FreeGroup.of i)) y) ∧
    (∀ y : ℝ, y < ρ (f (FreeGroup.of j)) y) ∧
    ρ (f (FreeGroup.of i)) l ≤ B ∧ ρ (f (FreeGroup.of j)) l ≤ B
  let S : Set ℝ := {v | ∃ f : FreeGroup ι ≃* FreeGroup ι, good f ∧
    ρ (f (FreeGroup.of i)) l + ρ (f (FreeGroup.of j)) l = v}
  have hS : S.Nonempty :=
    ⟨_, e, ⟨hei, hej, le_max_left _ _, le_max_right _ _⟩, rfl⟩
  have hbelow : BddBelow S := by
    refine ⟨l + l, ?_⟩
    rintro _ ⟨f, hf, rfl⟩
    exact add_le_add (hf.1 l).le (hf.2.1 l).le
  obtain ⟨v, hv, hvlt⟩ := exists_lt_of_csInf_lt hS (show sInf S < sInf S + δ by linarith)
  obtain ⟨f, hf, rfl⟩ := hv
  obtain ⟨f', hfi, hfj, hfiB, hfjB, hdec⟩ :=
    nielsen_decrease ρ i j hij hn l B δ hmove f hf.1 hf.2.1 hf.2.2.1 hf.2.2.2
  have hnew : ρ (f' (FreeGroup.of i)) l + ρ (f' (FreeGroup.of j)) l ∈ S :=
    ⟨f', ⟨hfi, hfj, hfiB, hfjB⟩, rfl⟩
  have hlow := csInf_le hbelow hnew
  linarith

/-- The exact entry-and-exit configuration used in the last paragraph of
MMRT Claim 4, with the no-far-fixed-point assumption made explicit. -/
theorem exists_primitive_entry_of_no_fixed_above [Nontrivial ι]
    (ρ : FreeGroup ι →* (ℝ ≃o ℝ))
    (hminimal : ∀ x : ℝ, DenseRange (fun g : FreeGroup ι => ρ g x))
    {b l r : ℝ} (hlr : l < r)
    (hfar : ∀ a : FreeGroup ι, IsPrimitive a → ∀ x : ℝ, b < x → ρ a x ≠ x) :
    ∃ a : FreeGroup ι, IsPrimitive a ∧ l < ρ a l ∧ ρ a l < r ∧ r < ρ a r := by
  have hn := primitive_no_fixed_of_no_fixed_above ρ hminimal b hfar
  obtain ⟨a, ha, he⟩ := exists_primitive_entry ρ hminimal hn hlr
  refine ⟨a, ha, he.1, he.2, ?_⟩
  exact positive_everywhere_of_no_fixed _ (hn a ha) he.1 r

/-- An orientation-preserving map with no fixed point on the interval and
positive motion at its left endpoint also moves the right endpoint right. -/
theorem endpoint_exit_of_no_fixed (a : ℝ ≃o ℝ) {l r : ℝ}
    (hlr : l < r) (ha : l < a l)
    (hfix : ∀ x ∈ Set.Icc l r, a x ≠ x) : r < a r := by
  by_contra h
  have har : a r ≤ r := le_of_not_gt h
  obtain ⟨x, hx, hax⟩ := exists_mem_Icc_isFixedPt a.continuous.continuousOn
    hlr.le ha.le har
  exact hfix x hx hax

/-- The endpoint conclusion in MMRT Claim 4 follows once the primitive
entry has been established; it is not another independent dynamical claim. -/
theorem primitive_entry_exits
    (ρ : FreeGroup ι →* (ℝ ≃o ℝ)) {a : FreeGroup ι} (ha : IsPrimitive a)
    {b l r : ℝ} (hbl : b < l) (hentry : ρ a l ∈ Set.Ioo l r)
    (hfar : ∀ c : FreeGroup ι, IsPrimitive c → ∀ x : ℝ, b < x → ρ c x ≠ x) :
    r < ρ a r := by
  exact endpoint_exit_of_no_fixed (ρ a) (hentry.1.trans hentry.2) hentry.1
    (fun x hx => hfar a ha x (hbl.trans_le hx.1))

/-- The marking on the product changes only the free factor. -/
def productBasis (e : FreeGroup ι ≃* FreeGroup ι) :
    FreeGroup ι × Multiplicative ℤ ≃* FreeGroup ι × Multiplicative ℤ :=
  e.prodCongr (MulEquiv.refl _)

@[simp] theorem productBasis_center (e : FreeGroup ι ≃* FreeGroup ι)
    (m : Multiplicative ℤ) : productBasis e (1, m) = (1, m) := by
  change (e 1, m) = (1, m)
  rw [map_one]

/-- For each explicitly chosen primitive basis, all original finite word
tests have a common trajectory bound in that basis. The quantifier order
records that this bound can depend on the basis. -/
theorem exists_changedBasis_trajectory_bound
    (ρ : FreeGroup ι × Multiplicative ℤ →* (ℝ ≃o ℝ))
    (e : FreeGroup ι ≃* FreeGroup ι)
    (F : Finset (FreeGroup ι × Multiplicative ℤ)) (x : ℝ) :
    ∃ b : ℝ, ∀ σ : FreeGroup ι × Multiplicative ℤ →* (ℝ ≃o ℝ),
      (∀ m : Multiplicative ℤ, σ (1, m) = ρ (1, m)) →
      (∀ i : ι, ∀ y : ℝ, y ≤ b →
        σ (e (FreeGroup.of i), 1) y = ρ (e (FreeGroup.of i), 1) y) →
      ∀ g ∈ F, σ g x = ρ g x := by
  classical
  let E := productBasis e
  obtain ⟨b, hb⟩ := NoncofinalTrajectory.exists_finiteTrajectory_bound
    (ρ.comp E.toMonoidHom) (F.image E.symm) x
  refine ⟨b, ?_⟩
  intro σ hz hagree g hg
  have h := hb (σ.comp E.toMonoidHom) (by simpa [E] using hz) hagree
    (E.symm g) (Finset.mem_image.mpr ⟨g, hg, rfl⟩)
  change σ (E (E.symm g)) x = ρ (E (E.symm g)) x at h
  simpa only [MulEquiv.apply_symm_apply] using h

end FnZPositiveCones.NoncofinalPrimitiveEntry
