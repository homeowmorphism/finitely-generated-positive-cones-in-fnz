module

public import FnZPositiveCones.External.CircularDynamics
public import FnZPositiveCones.External.CircularCocycle

@[expose] public section

/-! Circular gap-filled domains and actual generator transport. -/
namespace FnZPositiveCones
namespace CircularDynamics
universe u v
variable {X : Type u} [CircularOrder X]

/-- The oriented closed segment, with a singleton when both endpoints coincide. -/
def circularClosedSegment (a b : X) : Set X := {x | x = a ∨ x = b ∨ sbtw a x b}

theorem mem_circularClosedSegment_left (a b : X) : a ∈ circularClosedSegment a b :=
  Or.inl rfl

theorem mem_circularClosedSegment_right (a b : X) : b ∈ circularClosedSegment a b :=
  Or.inr (Or.inl rfl)

theorem circularClosedSegment_perm (e : Equiv.Perm X) (he : PreservesCircular e)
    (a b x : X) : e x ∈ circularClosedSegment (e a) (e b) ↔ x ∈ circularClosedSegment a b := by
  simp only [circularClosedSegment, Set.mem_ofPred_eq, e.injective.eq_iff,
    sbtw_iff_btw_not_btw, he a x b, he b x a]


/-- Strict betweenness in a segment avoiding a cut is ordinary betweenness in
the induced linear order at that cut. -/
theorem sbtw_cut_iff {base a b x : X} (hab : sbtw base a b) :
    sbtw a x b ↔ sbtw base a x ∧ sbtw base x b := by
  constructor
  · intro h
    exact ⟨(h.cyclic_left.trans_left hab.cyclic_right).cyclic_left,
      hab.trans_left h⟩
  · rintro ⟨hax, hxb⟩
    have haxne : a ≠ x := by intro he; subst x; exact sbtw_irrefl_right hax
    have hxbne : x ≠ b := by intro he; subst x; exact sbtw_irrefl_right hxb
    have habne : b ≠ a := by intro he; subst b; exact sbtw_irrefl_right hab
    rcases CircularCarry.strict_or_reverse haxne hxbne habne with h | h
    · exact h
    · exact False.elim (hxb.not_sbtw (hax.trans_left h.cyclic_right).cyclic_left)

/-- Fill the monochrome oriented segments avoiding the basepoint. -/
def circularColorFilledHull {C : Type v} (K : Set X) (color : X → C) (base : X)
    (c : C) : Set X :=
  {x | ∃ a ∈ K, ∃ b ∈ K, x ∈ circularClosedSegment a b ∧
    base ∉ circularClosedSegment a b ∧
    ∀ z ∈ K, z ∈ circularClosedSegment a b → color z = c}

theorem base_not_mem_circularColorFilledHull {C : Type v}
    (K : Set X) (color : X → C) (base : X) (c : C) :
    base ∉ circularColorFilledHull K color base c := by
  rintro ⟨a, ha, b, hb, hx, hbase, hm⟩
  exact hbase hx

theorem circularColorFilledHull_inter {C : Type v}
    (K : Set X) (color : X → C) (base : X) (hbase : base ∉ K) (c : C) :
    circularColorFilledHull K color base c ∩ K = {x | x ∈ K ∧ color x = c} := by
  ext x
  constructor
  · rintro ⟨⟨a, ha, b, hb, hx, hba, hm⟩, hxK⟩
    exact ⟨hxK, hm x hxK hx⟩
  · rintro ⟨hx, hc⟩
    refine ⟨⟨x, hx, x, hx, Or.inl rfl, ?_, ?_⟩, hx⟩
    · rintro (he | he | hs)
      · exact hbase (he ▸ hx)
      · exact hbase (he ▸ hx)
      · exact sbtw_irrefl_left_right hs
    · intro z hz hzx
      rcases hzx with he | he | hs
      · exact he ▸ hc
      · exact he ▸ hc
      · exact False.elim (sbtw_irrefl_left_right hs)

/-- Transport of filled color domains follows from the actual color transition
on the orbit closure. The inverse-image exception is precisely the basepoint,
and the color of its preimage prevents an image segment from crossing the cut. -/
theorem mapsTo_circularColorFilledHull {C : Type v}
    (K : Set X) (color : X → C) (base : X) (c d : C)
    (e : Equiv.Perm X) (he : PreservesCircular e)
    (hprebase : e.symm base ∈ K) (hprecolor : color (e.symm base) ≠ c)
    (hforward : ∀ x ∈ K, color x = c → e x ∈ K ∧ color (e x) = d)
    (hinverse : ∀ z ∈ K, e.symm z ∈ K ∨ e.symm z = base) :
    Set.MapsTo e (circularColorFilledHull K color base c)
      (circularColorFilledHull K color base d) := by
  rintro x ⟨a, ha, b, hb, hxab, hbase, hm⟩
  have haC := hm a ha (mem_circularClosedSegment_left a b)
  have hbC := hm b hb (mem_circularClosedSegment_right a b)
  refine ⟨e a, (hforward a ha haC).1, e b, (hforward b hb hbC).1,
    (circularClosedSegment_perm e he a b x).mpr hxab, ?_, ?_⟩
  · intro hbe
    have hin : e.symm base ∈ circularClosedSegment a b :=
      (circularClosedSegment_perm e he a b (e.symm base)).mp (by simpa using hbe)
    exact hprecolor (hm _ hprebase hin)
  · intro z hz hzin
    have hzi : e.symm z ∈ circularClosedSegment a b :=
      (circularClosedSegment_perm e he a b (e.symm z)).mp (by simpa using hzin)
    rcases hinverse z hz with hK | hzero
    · simpa using (hforward (e.symm z) hK (hm _ hK hzi)).2
    · exact False.elim (hbase (hzero ▸ hzi))

end CircularDynamics
end FnZPositiveCones
