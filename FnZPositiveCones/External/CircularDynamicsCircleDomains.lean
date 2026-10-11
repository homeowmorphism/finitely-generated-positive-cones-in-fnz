module

public import FnZPositiveCones.External.CircularDynamicsDomains
public import FnZPositiveCones.External.CircularDynamicsObstruction

@[expose] public section

/-! Finite real color cells transferred to actual closed arcs of the circle. -/
namespace FnZPositiveCones
namespace CircularDynamics

@[simp] theorem circleCoordinate_coe {x : ℝ} (hx : x ∈ Set.Ico (0 : ℝ) 1) :
    circleCoordinate (x : StandardCircle) = x := by
  apply (AddCircle.coe_eq_coe_iff_of_mem_Ico (a := (0 : ℝ))
    (by simpa using circleCoordinate_mem (x : StandardCircle))
    (by simpa using hx)).mp
  exact coe_circleCoordinate _

theorem continuousAt_circleCoordinate {x : StandardCircle} (hx : x ≠ 0) :
    ContinuousAt circleCoordinate x := by
  exact continuous_subtype_val.continuousAt.comp
    (AddCircle.continuousAt_equivIco (1 : ℝ) 0 hx)

/-- The image of a closed interval in one fundamental real chart. -/
def closedCircleArc (a b : ℝ) : Set StandardCircle :=
  (fun x : ℝ => (x : StandardCircle)) '' Set.Icc a b

theorem isCompact_closedCircleArc (a b : ℝ) : IsCompact (closedCircleArc a b) :=
  isCompact_Icc.image continuous_quotient_mk'

/-- A compact colored circle set avoiding the basepoint admits an actual finite
cover by pairwise disjoint monochrome closed arcs. Local color separation is
explicit, and all arc endpoints belong to the original compact set. -/
theorem exists_finite_monochrome_circle_arcs {C : Type*}
    (K : Set StandardCircle) (hK : IsCompact K) (hzero : 0 ∉ K)
    (color : StandardCircle → C)
    (hlocal : ∀ x ∈ K, ∃ ε > 0, ∀ y ∈ K, dist x y < ε → color x = color y) :
    ∃ (I : Type) (_ : Fintype I) (a b : I → ℝ),
      (∀ i, 0 < a i ∧ a i ≤ b i ∧ b i < 1 ∧
        (a i : StandardCircle) ∈ K ∧ (b i : StandardCircle) ∈ K) ∧
      (∀ x ∈ K, ∃ i, x ∈ closedCircleArc (a i) (b i)) ∧
      (∀ i, ∀ x ∈ K, x ∈ closedCircleArc (a i) (b i) →
        color x = color (a i : StandardCircle)) ∧
      (∀ i j, i ≠ j → Disjoint (closedCircleArc (a i) (b i))
        (closedCircleArc (a j) (b j))) := by
  let R := circleCoordinate '' K
  have hR : IsCompact R := hK.image_of_continuousOn (fun x hx =>
    (continuousAt_circleCoordinate (fun he => hzero (he ▸ hx))).continuousWithinAt)
  have hRmem : ∀ x ∈ R, (x : StandardCircle) ∈ K := by
    rintro x ⟨y, hy, rfl⟩
    simpa using hy
  have hRIco : ∀ x ∈ R, x ∈ Set.Ico (0 : ℝ) 1 := by
    rintro x ⟨y, _, rfl⟩
    exact circleCoordinate_mem y
  have hRpos : ∀ x ∈ R, 0 < x := by
    intro x hx
    apply lt_of_le_of_ne (hRIco x hx).1
    intro he
    apply hzero
    simpa [← he] using hRmem x hx
  have hRlocal : ∀ x ∈ R, ∃ ε > 0, ∀ y ∈ R, dist x y < ε →
      color (x : StandardCircle) = color (y : StandardCircle) := by
    intro x hx
    obtain ⟨ε, hε, hm⟩ := hlocal (x : StandardCircle) (hRmem x hx)
    exact ⟨ε, hε, fun y hy hxy => hm y (hRmem y hy)
      ((circle_dist_coe_le x y).trans_lt hxy)⟩
  obtain ⟨I, finI, a, b, hab, hcover, hmono, hdisj⟩ :=
    exists_finite_monochrome_intervals R hR (fun x : ℝ => color (x : StandardCircle)) hRlocal
  have hIco : ∀ i, ∀ x ∈ Set.Icc (a i) (b i), x ∈ Set.Ico (0 : ℝ) 1 := by
    intro i x hx
    exact ⟨(hRIco (a i) (hab i).1).1.trans hx.1,
      hx.2.trans_lt (hRIco (b i) (hab i).2.1).2⟩
  refine ⟨I, finI, a, b, ?_, ?_, ?_, ?_⟩
  · intro i
    exact ⟨hRpos (a i) (hab i).1, (hab i).2.2, (hRIco (b i) (hab i).2.1).2,
      hRmem (a i) (hab i).1, hRmem (b i) (hab i).2.1⟩
  · intro x hx
    obtain ⟨i, hi⟩ := hcover (circleCoordinate x) ⟨x, hx, rfl⟩
    exact ⟨i, circleCoordinate x, hi, coe_circleCoordinate x⟩
  · intro i x hx hxi
    obtain ⟨y, hy, rfl⟩ := hxi
    have hyR : y ∈ R := by
      refine ⟨(y : StandardCircle), hx, ?_⟩
      exact circleCoordinate_coe (hIco i y hy)
    exact hmono i y hyR hy
  · intro i j hij
    apply Set.disjoint_left.mpr
    rintro x ⟨y, hy, hyx⟩ ⟨z, hz, hzx⟩
    have hyz : y = z := (AddCircle.coe_eq_coe_iff_of_mem_Ico (a := (0 : ℝ))
      (by simpa using hIco i y hy) (by simpa using hIco j z hz)).mp (hyx.trans hzx.symm)
    exact Set.disjoint_left.mp (hdisj i j hij) hy (hyz ▸ hz)

end CircularDynamics
end FnZPositiveCones
