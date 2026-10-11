module

public import FnZPositiveCones.External.CircularDynamicsDomainTransport
public import FnZPositiveCones.External.CircularDynamicsCircleFilled

@[expose] public section

/-! Finite canonical first-letter domains from the precise separation premise. -/
namespace FnZPositiveCones
namespace CircularDynamics

/-- A finite family of disjoint closed color sets supplies the local constancy
used in the interval extraction; no local constancy premise remains here. -/
theorem local_color_constancy_of_finite_closed_partition {X C : Type*}
    [MetricSpace X] [Finite C] (K : Set X) (D : C → Set X) (color : X → C)
    (hclosed : ∀ c, IsClosed (D c))
    (hsep : ∀ c d, c ≠ d → Disjoint (D c) (D d))
    (hcolor : ∀ x ∈ K, x ∈ D (color x)) :
    ∀ x ∈ K, ∃ ε > 0, ∀ y ∈ K, dist x y < ε → color x = color y := by
  intro x hx
  let bad := ⋃ c : {c : C // c ≠ color x}, D c.val
  have hb : IsClosed bad := isClosed_iUnion_of_finite (fun c => hclosed c.val)
  have hxU : x ∈ badᶜ := by
    intro he
    obtain ⟨c, hc⟩ := Set.mem_iUnion.mp he
    exact Set.disjoint_left.mp (hsep c.val (color x) c.property) hc (hcolor x hx)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hb.isOpen_compl x hxU
  refine ⟨ε, hε, ?_⟩
  intro y hy hxy
  by_contra hne
  have hyU : y ∈ badᶜ := hball (by simpa [Metric.mem_ball, dist_comm] using hxy)
  apply hyU
  exact Set.mem_iUnion.mpr ⟨⟨color y, fun he => hne he.symm⟩, hcolor y hy⟩

universe u
variable {ι : Type u} [Nonempty ι] [Finite ι]

omit [Nonempty ι] in
/-- The finite union of actual color closures is compact on the circle. -/
theorem isCompact_coloredOrbitClosure (ρ : ι → Equiv.Perm StandardCircle) (base : StandardCircle) :
    IsCompact (coloredOrbitClosure ρ base) :=
  (isClosed_iUnion_of_finite (fun _ => isClosed_closure)).isCompact

omit [Nonempty ι] [Finite ι] in
theorem base_not_mem_coloredOrbitClosure (ρ : ι → Equiv.Perm StandardCircle) (base : StandardCircle)
    (hbase : ∀ s, base ∉ closure (letterOrbit ρ base s)) :
    base ∉ coloredOrbitClosure ρ base := by
  intro he
  obtain ⟨s, hs⟩ := Set.mem_iUnion.mp he
  exact hbase s hs

/-- Separation of the actual closed first-letter colors implies their local
monochrome property. Proving the displayed separation from isolation is still
an independent obligation. -/
theorem orbitClosureColor_local (ρ : ι → Equiv.Perm StandardCircle) (base : StandardCircle)
    (hsep : ∀ s t, s ≠ t → Disjoint (closure (letterOrbit ρ base s))
      (closure (letterOrbit ρ base t))) :
    ∀ x ∈ coloredOrbitClosure ρ base, ∃ ε > 0,
      ∀ y ∈ coloredOrbitClosure ρ base, dist x y < ε →
        orbitClosureColor ρ base x = orbitClosureColor ρ base y :=
  local_color_constancy_of_finite_closed_partition (coloredOrbitClosure ρ base)
    (fun s => closure (letterOrbit ρ base s)) (orbitClosureColor ρ base)
    (fun _ => isClosed_closure) hsep
    (fun _ hx => mem_closure_letterOrbit_of_mem_coloredOrbitClosure ρ base hx)

/-- The canonical first-letter domain is genuinely a finite union of closed
arcs; neither its finiteness nor its gap filling is assumed. -/
theorem firstLetterDomain_finite_arcs (ρ : ι → Equiv.Perm StandardCircle)
    (hsep : ∀ s t, s ≠ t → Disjoint (closure (letterOrbit ρ 0 s))
      (closure (letterOrbit ρ 0 t)))
    (hbase : ∀ s, (0 : StandardCircle) ∉ closure (letterOrbit ρ 0 s)) (s : ι × Bool) :
    ∃ F : Finset (ℝ × ℝ), firstLetterDomain ρ 0 s = ⋃ p ∈ F, closedCircleArc p.1 p.2 :=
  circularColorFilledHull_finite_arcs (coloredOrbitClosure ρ 0) (isCompact_coloredOrbitClosure ρ 0)
    (base_not_mem_coloredOrbitClosure ρ 0 hbase) (orbitClosureColor ρ 0)
    (orbitClosureColor_local ρ 0 hsep) s

theorem isCompact_firstLetterDomain (ρ : ι → Equiv.Perm StandardCircle)
    (hsep : ∀ s t, s ≠ t → Disjoint (closure (letterOrbit ρ 0 s))
      (closure (letterOrbit ρ 0 t)))
    (hbase : ∀ s, (0 : StandardCircle) ∉ closure (letterOrbit ρ 0 s)) (s : ι × Bool) :
    IsCompact (firstLetterDomain ρ 0 s) :=
  isCompact_circularColorFilledHull (coloredOrbitClosure ρ 0) (isCompact_coloredOrbitClosure ρ 0)
    (base_not_mem_coloredOrbitClosure ρ 0 hbase) (orbitClosureColor ρ 0)
    (orbitClosureColor_local ρ 0 hsep) s

omit [Finite ι] in
theorem firstLetterDomain_disjoint (ρ : ι → Equiv.Perm StandardCircle)
    (hbase : ∀ s, (0 : StandardCircle) ∉ closure (letterOrbit ρ 0 s))
    {s t : ι × Bool} (hst : s ≠ t) :
    Disjoint (firstLetterDomain ρ 0 s) (firstLetterDomain ρ 0 t) :=
  circularColorFilledHull_disjoint (coloredOrbitClosure ρ 0)
    (base_not_mem_coloredOrbitClosure ρ 0 hbase) (orbitClosureColor ρ 0) hst

omit [Finite ι] in
theorem firstLetterDomain_nonempty (ρ : ι → Equiv.Perm StandardCircle)
    (hsep : ∀ s t, s ≠ t → Disjoint (closure (letterOrbit ρ 0 s))
      (closure (letterOrbit ρ 0 t)))
    (hbase : ∀ s, (0 : StandardCircle) ∉ closure (letterOrbit ρ 0 s)) (s : ι × Bool) :
    (firstLetterDomain ρ 0 s).Nonempty := by
  obtain ⟨x, hx⟩ := letterOrbit_nonempty ρ 0 s
  have hxC : x ∈ closure (letterOrbit ρ 0 s) := subset_closure hx
  have hxK : x ∈ coloredOrbitClosure ρ 0 := Set.mem_iUnion.mpr ⟨s, hxC⟩
  have hxColor := orbitClosureColor_eq_of_mem ρ 0 hsep hxC
  have hxD : x ∈ circularColorFilledHull (coloredOrbitClosure ρ 0) (orbitClosureColor ρ 0) 0 s ∩
      coloredOrbitClosure ρ 0 := by
    rw [circularColorFilledHull_inter _ _ _ (base_not_mem_coloredOrbitClosure ρ 0 hbase)]
    exact ⟨hxK, hxColor⟩
  exact ⟨x, hxD.1⟩

end CircularDynamics
end FnZPositiveCones
