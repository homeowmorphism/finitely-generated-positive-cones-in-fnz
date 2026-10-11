module

public import FnZPositiveCones.External.NoncofinalFreeCone
public import FnZPositiveCones.External.CircularDynamicsGapWords
public import FnZPositiveCones.External.CofinalCocycle
public import FnZPositiveCones.External.OrderedActionsCircleRealization
public import FnZPositiveCones.External.CircularDynamicsObstruction

@[expose] public section

/-!
# Finite free-coordinate cutsets from finite positive generation

Positive products give monotone paths in the left order. Every reduced prefix
of their free projection has an interpolation point on that path, whose free
coordinate differs from the prefix by one of finitely many generator suffixes.
Consequently an interval joining different initial free letters meets a finite
set of free coordinates. The topological separation adapter is developed in
`CircularFGSeparationTopology`.
-/

namespace FnZPositiveCones.CircularFGSeparation

open FreeGroup NoncofinalFreeSubgroup NoncofinalFreeCone

universe u v
variable {G : Type u} [Group G] {ι : Type v} [DecidableEq ι]

/-- A reduced free prefix has an interpolation point in the closed positive
order interval, with a suffix correction from a fixed set. -/
def PrefixInterpolable (P : PositiveCone G) (φ : G →* FreeGroup ι)
    (T : Set (FreeGroup ι)) (p : G) : Prop :=
  ∀ q ∈ vertices (MonoidHom.id _) (φ p).toWord,
    ∃ u : G, ∃ r ∈ T,
      (coneLeftOrder P).order.le 1 u ∧ (coneLeftOrder P).order.le u p ∧ φ u = q * r

/-- Prefix interpolation is stable under multiplication of positive elements.
The second factor's interpolation point is translated on the left. -/
theorem prefixInterpolable_mul (P : PositiveCone G) (φ : G →* FreeGroup ι)
    (T : Set (FreeGroup ι)) {g h : G}
    (hg : g ∈ P.1) (hh : h ∈ P.1)
    (hgT : PrefixInterpolable P φ T g) (hhT : PrefixInterpolable P φ T h) :
    PrefixInterpolable P φ T (g * h) := by
  let O := coneLeftOrder P
  let := O.order
  have hgpos : (1 : G) < g := by change 1⁻¹ * g ∈ P.1; simpa using hg
  have hhpos : (1 : G) < h := by change 1⁻¹ * h ∈ P.1; simpa using hh
  have hgh : g ≤ g * h := by simpa using O.mul_le_mul_left 1 h g hhpos.le
  intro q hq
  rw [φ.map_mul, toWord_mul] at hq
  have hq' := vertices_reduce_subset (MonoidHom.id _) _ hq
  rw [vertices_append, mk_toWord, MonoidHom.id_apply] at hq'
  rcases hq' with hq' | ⟨v, hv, rfl⟩
  · obtain ⟨u, r, hr, h1u, hug, hφ⟩ := hgT q hq'
    exact ⟨u, r, hr, h1u, hug.trans hgh, hφ⟩
  · obtain ⟨u, r, hr, h1u, huh, hφ⟩ := hhT v hv
    have hgu : g ≤ g * u := by simpa using O.mul_le_mul_left 1 u g h1u
    refine ⟨g * u, r, hr, hgpos.le.trans hgu, O.mul_le_mul_left u h g huh, ?_⟩
    rw [φ.map_mul, hφ, mul_assoc]

/-- Finite semigroup generation gives a finite suffix set controlling all
positive intervals, with both order inequalities checked in the original cone. -/
theorem exists_finite_prefix_interpolators (P : PositiveCone G)
    (φ : G →* FreeGroup ι) (hfg : SemigroupFG P.1) :
    ∃ T : Set (FreeGroup ι), T.Finite ∧
      ∀ p ∈ P.1, PrefixInterpolable P φ T p := by
  classical
  obtain ⟨S, hS⟩ := hfg
  let T : Set (FreeGroup ι) := ⋃ g ∈ (S : Set G), suffixes (φ g).toWord
  have hfin : T.Finite := S.finite_toSet.biUnion (fun g _ => suffixes_finite (φ g).toWord)
  let Q : Subsemigroup G :=
    { carrier := {p | p ∈ P.1 ∧ PrefixInterpolable P φ T p}
      mul_mem' := fun hg hh => ⟨P.1.mul_mem hg.1 hh.1,
        prefixInterpolable_mul P φ T hg.1 hh.1 hg.2 hh.2⟩ }
  have hle : P.1 ≤ Q := by
    nth_rw 1 [← hS]
    apply Subsemigroup.closure_le.mpr
    intro g hg
    have hgP : g ∈ P.1 := by rw [← hS]; exact Subsemigroup.subset_closure hg
    refine ⟨hgP, ?_⟩
    intro q hq
    obtain ⟨r, hr, hqr⟩ := vertex_suffix (φ g).toWord q hq
    refine ⟨g, r, Set.mem_iUnion.mpr ⟨g, Set.mem_iUnion.mpr ⟨hg, hr⟩⟩, ?_, ?_, ?_⟩
    · let := (coneLeftOrder P).order
      apply le_of_lt
      change 1⁻¹ * g ∈ P.1
      simpa using hgP
    · let := (coneLeftOrder P).order
      exact le_rfl
    · simpa only [mk_toWord] using hqr.symm
  exact ⟨T, hfin, fun p hp => (hle hp).2⟩

/-- Distinct initial letters make the inverse of the first word a prefix of
the reduced difference. This uses a checked reduced-word identity. -/
theorem inverse_mem_difference_vertices (g h : FreeGroup ι)
    (s t : ι × Bool) (w z : List (ι × Bool))
    (hg : g.toWord = s :: w) (hh : h.toWord = t :: z) (hst : s ≠ t) :
    g⁻¹ ∈ vertices (MonoidHom.id _) (g⁻¹ * h).toWord := by
  have hr := CircularDynamics.different_heads_inv_mul_reduced g h s t w z hg hh hst
  rw [toWord_mul, toWord_inv, hr.reduce_eq, vertices_append]
  left
  simpa only [← inv_mk, mk_toWord, MonoidHom.id_apply] using
    endpoint_mem_vertices (MonoidHom.id _) (invRev g.toWord)

/-- Every ordered interval between different free initial letters contains
an element whose free coordinate lies in a single finite set. -/
theorem exists_finite_interval_cutset (P : PositiveCone G)
    (φ : G →* FreeGroup ι) (hfg : SemigroupFG P.1) :
    ∃ T : Set (FreeGroup ι), T.Finite ∧
      ∀ g h : G, (coneLeftOrder P).order.lt g h →
      ∀ s t : ι × Bool, ∀ w z : List (ι × Bool),
      (φ g).toWord = s :: w → (φ h).toWord = t :: z → s ≠ t →
      ∃ v : G, (coneLeftOrder P).order.le g v ∧
        (coneLeftOrder P).order.le v h ∧ φ v ∈ T := by
  obtain ⟨T, hT, hint⟩ := exists_finite_prefix_interpolators P φ hfg
  refine ⟨T, hT, ?_⟩
  intro g h hgh s t w z hgs hht hst
  have hpos : g⁻¹ * h ∈ P.1 := hgh
  have hvertex : (φ g)⁻¹ ∈ vertices (MonoidHom.id _) (φ (g⁻¹ * h)).toWord := by
    rw [φ.map_mul, _root_.map_inv]
    exact inverse_mem_difference_vertices (φ g) (φ h) s t w z hgs hht hst
  obtain ⟨u, r, hr, h1u, huh, hφ⟩ := hint (g⁻¹ * h) hpos _ hvertex
  let O := coneLeftOrder P
  have hgu := O.mul_le_mul_left 1 u g h1u
  have hugh := O.mul_le_mul_left u (g⁻¹ * h) g huh
  refine ⟨g * u, by simpa using hgu, by simpa using hugh, ?_⟩
  rw [φ.map_mul, hφ, mul_inv_cancel_left]
  exact hr

section Product
variable (O : LeftGroupOrder (FreeGroup ι × Multiplicative ℤ))
variable (hz : O.order.lt 1 (cofinalProductZ (FreeGroup ι)))
variable (hc : O.IsCofinal (cofinalProductZ (FreeGroup ι)))

omit [DecidableEq ι] in
/-- An element already between the central powers zero and one is the
distinguished representative of its free coordinate. -/
theorem representative_eq_of_fundamental (v : FreeGroup ι × Multiplicative ℤ)
    (hv : O.order.le 1 v ∧ O.order.lt v (cofinalProductZ (FreeGroup ι))) :
    cofinalProductRepresentative O hz hc v.1 = v := by
  have he : v = cofinalProductZ (FreeGroup ι) ^ v.2.toAdd * (v.1, 1) := by
    apply Prod.ext
    · simp [cofinalProductZ]
    · apply Multiplicative.toAdd.injective
      simp [cofinalProductZ]
  have hf := congrArg (O.fundamentalRepresentative hz hc) he
  rw [O.fundamentalRepresentative_zpow_mul] at hf
  exact hf.symm.trans (O.fundamentalRepresentative_eq_self hz hc hv)

end Product

/-- The finite free-coordinate cutset descends to distinguished representatives
in the fundamental interval. Thus it is a single finite set of circular orbit
points, rather than infinitely many central translates. -/
theorem exists_finite_representative_cutset
    (P : PositiveCone (FreeGroup ι × Multiplicative ℤ)) (hfg : SemigroupFG P.1)
    (hz : (coneLeftOrder P).order.lt 1 (cofinalProductZ (FreeGroup ι)))
    (hc : (coneLeftOrder P).IsCofinal (cofinalProductZ (FreeGroup ι))) :
    ∃ T : Set (FreeGroup ι), T.Finite ∧
      ∀ g h : FreeGroup ι,
      (coneLeftOrder P).order.lt
        (cofinalProductRepresentative (coneLeftOrder P) hz hc g)
        (cofinalProductRepresentative (coneLeftOrder P) hz hc h) →
      ∀ s t : ι × Bool, ∀ w z : List (ι × Bool),
      g.toWord = s :: w → h.toWord = t :: z → s ≠ t →
      ∃ r ∈ T,
        (coneLeftOrder P).order.le
          (cofinalProductRepresentative (coneLeftOrder P) hz hc g)
          (cofinalProductRepresentative (coneLeftOrder P) hz hc r) ∧
        (coneLeftOrder P).order.le
          (cofinalProductRepresentative (coneLeftOrder P) hz hc r)
          (cofinalProductRepresentative (coneLeftOrder P) hz hc h) := by
  let O := coneLeftOrder P
  let := O.order
  let rep := cofinalProductRepresentative O hz hc
  obtain ⟨T, hT, hcut⟩ := exists_finite_interval_cutset P
    (MonoidHom.fst (FreeGroup ι) (Multiplicative ℤ)) hfg
  refine ⟨T, hT, ?_⟩
  intro g h hgh s t w z hgs hht hst
  have hgs' : ((MonoidHom.fst (FreeGroup ι) (Multiplicative ℤ)) (rep g)).toWord = s :: w := by
    change (rep g).1.toWord = s :: w
    simpa only [rep, cofinalProductRepresentative_fst] using hgs
  have hht' : ((MonoidHom.fst (FreeGroup ι) (Multiplicative ℤ)) (rep h)).toWord = t :: z := by
    change (rep h).1.toWord = t :: z
    simpa only [rep, cofinalProductRepresentative_fst] using hht
  obtain ⟨v, hgv, hvh, hvT⟩ := hcut (rep g) (rep h) hgh s t w z hgs' hht' hst
  have hgfund := O.fundamentalRepresentative_mem hz hc (g, 1)
  have hhfund := O.fundamentalRepresentative_mem hz hc (h, 1)
  have hvfund : 1 ≤ v ∧ v < cofinalProductZ (FreeGroup ι) :=
    ⟨hgfund.1.trans hgv, hvh.trans_lt hhfund.2⟩
  have hvrep := representative_eq_of_fundamental O hz hc v hvfund
  refine ⟨v.1, hvT, ?_⟩
  change rep g ≤ rep v.1 ∧ rep v.1 ≤ rep h
  change rep v.1 = v at hvrep
  rw [hvrep]
  exact ⟨hgv, hvh⟩

section CircleCoordinates
open CircularDynamics
variable (O : LeftGroupOrder (FreeGroup ι × Multiplicative ℤ))
variable (hz : O.order.lt 1 (cofinalProductZ (FreeGroup ι)))
variable (hc : O.IsCofinal (cofinalProductZ (FreeGroup ι)))
variable (R : CircularRealization (cofinalProductCircularGroupOrder O hz hc))

omit [DecidableEq ι] in
private theorem orbit_coordinate_one : circleCoordinate (R.action 1 0) = 0 := by
  simp only [_root_.map_one, Equiv.Perm.one_apply]
  apply (AddCircle.coe_eq_coe_iff_of_mem_Ico (a := (0 : ℝ)) (p := (1 : ℝ))
    (by simpa using circleCoordinate_mem 0) (by norm_num)).mp
  exact coe_circleCoordinate 0

omit [DecidableEq ι] in
private theorem orbit_coordinate_pos {g : FreeGroup ι} (hg : g ≠ 1) :
    0 < circleCoordinate (R.action g 0) := by
  apply lt_of_le_of_ne (circleCoordinate_mem _).1
  intro he
  apply hg
  apply R.orbit_injective
  change R.action g 0 = R.action 1 0
  rw [← coe_circleCoordinate (R.action g 0), ← he]
  simp

/-- The original cone's normalized representative order agrees with the
standard coordinate order of every realization of its circular quotient.
The realization's auxiliary lift need not equal the original cone order. -/
theorem representative_lt_iff_coordinate (g h : FreeGroup ι) :
    O.order.lt (cofinalProductRepresentative O hz hc g)
      (cofinalProductRepresentative O hz hc h) ↔
    circleCoordinate (R.action g 0) < circleCoordinate (R.action h 0) := by
  let := O.order
  by_cases hg : g = 1
  · subst g
    rw [cofinalProductRepresentative_one, orbit_coordinate_one]
    by_cases hh : h = 1
    · subst h
      rw [cofinalProductRepresentative_one, orbit_coordinate_one]
      simp
    · exact iff_of_true (cofinalProductRepresentative_pos O hz hc hh)
        (orbit_coordinate_pos O hz hc R hh)
  · have hs := (cofinalProductCircularGroupOrder_sbtw_one O hz hc g h).symm.trans
      (R.orbit_sbtw 1 g h)
    have ht := OrderedActions.circle_sbtw_zero_iff
      (circleCoordinate_mem (R.action g 0)) (circleCoordinate_mem (R.action h 0))
    rw [coe_circleCoordinate, coe_circleCoordinate] at ht
    simp only [_root_.map_one, Equiv.Perm.one_apply] at hs
    have he := hs.trans ht
    simpa only [cofinalProductRepresentative_pos O hz hc hg,
      orbit_coordinate_pos O hz hc R hg, true_and] using he

theorem representative_le_iff_coordinate (g h : FreeGroup ι) :
    O.order.le (cofinalProductRepresentative O hz hc g)
      (cofinalProductRepresentative O hz hc h) ↔
    circleCoordinate (R.action g 0) ≤ circleCoordinate (R.action h 0) := by
  let := O.order
  exact (not_lt.symm.trans (not_congr (representative_lt_iff_coordinate O hz hc R h g))).trans not_lt

end CircleCoordinates

/-- A single finite set of realized orbit points separates every pair of
differently colored orbit points in the standard coordinate interval. -/
theorem exists_finite_circle_cutset
    (P : PositiveCone (FreeGroup ι × Multiplicative ℤ)) (hfg : SemigroupFG P.1)
    (hz : (coneLeftOrder P).order.lt 1 (cofinalProductZ (FreeGroup ι)))
    (hc : (coneLeftOrder P).IsCofinal (cofinalProductZ (FreeGroup ι)))
    (R : CircularRealization (cofinalProductCircularGroupOrder (coneLeftOrder P) hz hc)) :
    ∃ T : Set (FreeGroup ι), T.Finite ∧
      ∀ g h : FreeGroup ι, ∀ s t : ι × Bool, ∀ w z : List (ι × Bool),
      g.toWord = s :: w → h.toWord = t :: z → s ≠ t →
      ∃ r ∈ T, CircularDynamics.circleCoordinate (R.action r 0) ∈
        Set.uIcc (CircularDynamics.circleCoordinate (R.action g 0))
          (CircularDynamics.circleCoordinate (R.action h 0)) := by
  let O := coneLeftOrder P
  let := O.order
  let rep := cofinalProductRepresentative O hz hc
  obtain ⟨T, hT, hcut⟩ := exists_finite_representative_cutset P hfg hz hc
  refine ⟨T, hT, ?_⟩
  intro g h s t w z hgs hht hst
  have hne : rep g ≠ rep h := by
    intro he
    have hgh := cofinalProductRepresentative_injective O hz hc he
    have heq : s :: w = t :: z := hgs.symm.trans (hgh ▸ hht)
    exact hst (List.cons.inj heq).1
  rcases hne.lt_or_gt with hgh | hhg
  · obtain ⟨r, hr, hgr, hrh⟩ := hcut g h hgh s t w z hgs hht hst
    refine ⟨r, hr, Set.mem_uIcc.mpr (Or.inl ⟨?_, ?_⟩)⟩
    · exact (representative_le_iff_coordinate O hz hc R g r).mp hgr
    · exact (representative_le_iff_coordinate O hz hc R r h).mp hrh
  · obtain ⟨r, hr, hhr, hrg⟩ := hcut h g hhg t s z w hht hgs hst.symm
    refine ⟨r, hr, Set.mem_uIcc.mpr (Or.inr ⟨?_, ?_⟩)⟩
    · exact (representative_le_iff_coordinate O hz hc R h r).mp hhr
    · exact (representative_le_iff_coordinate O hz hc R r g).mp hrg

end FnZPositiveCones.CircularFGSeparation
