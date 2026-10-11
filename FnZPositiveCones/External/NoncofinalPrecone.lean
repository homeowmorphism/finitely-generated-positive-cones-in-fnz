module

public import FnZPositiveCones.External.NoncofinalFreeCone
public import FnZPositiveCones.External.CircularQuotient

@[expose] public section

/-!
# Finitely generated total precones in nonabelian free groups

The finite-prefix completion argument also applies to a total, reflexive
precone: identity is allowed in its image, while the original positive cone
remains strict. Any finitely generated such precone in a nonabelian free group
is the whole group. Applying this to projection onto the free factor proves
cofinality of the central cyclic factor for every finitely generated strict
positive cone, independently of the stronger isolated-order statement.
-/

namespace FnZPositiveCones.NoncofinalPrecone

open FreeGroup NoncofinalFreeSubgroup NoncofinalFreeCone

universe u v
variable {G : Type u} [Group G] {ι : Type v}

/-- Finite subsets have an upper bound in the reflexive total left preorder
defined by a precone. This uses no antisymmetry or normality. -/
theorem finite_upper_bound (P : Subsemigroup G) (h1 : 1 ∈ P)
    (htotal : ∀ g : G, g ∈ P ∨ g⁻¹ ∈ P)
    (T : Set G) (hT : T.Finite) : ∃ b : G, ∀ r ∈ T, r⁻¹ * b ∈ P := by
  induction T, hT using Set.Finite.induction_on with
  | empty => exact ⟨1, fun _ h => h.elim⟩
  | @insert a T ha hT ih =>
    obtain ⟨b, hb⟩ := ih
    rcases htotal (a⁻¹ * b) with hab | hba
    · refine ⟨b, ?_⟩
      intro r hr
      rcases hr with rfl | hr
      · exact hab
      · exact hb r hr
    · have hba' : b⁻¹ * a ∈ P := by simpa using hba
      refine ⟨a, ?_⟩
      intro r hr
      rcases hr with rfl | hr
      · simpa using h1
      · simpa only [mul_assoc, mul_inv_cancel_left] using P.mul_mem (hb r hr) hba'

/-- Totality alone ensures that every prescribed reduced prefix extends to
an element of a precone. The reduced conjugate and its inverse share that
prefix, so strictness is unnecessary. -/
theorem exists_precone_vertex [Nontrivial ι] [DecidableEq ι]
    (P : Subsemigroup (FreeGroup ι))
    (htotal : ∀ g : FreeGroup ι, g ∈ P ∨ g⁻¹ ∈ P) (g : FreeGroup ι) :
    ∃ h ∈ P, g ∈ vertices (MonoidHom.id _) h.toWord := by
  let i : ι := Classical.choice (inferInstance : Nonempty ι)
  obtain ⟨s, hs⟩ := exists_reduced_conjugate_prefix g.toWord [(i, true)]
    isReduced_toWord IsReduced.singleton (by simp)
  let w := g.toWord ++ [s] ++ [(i, true)] ++ invRev [s] ++ invRev g.toWord
  have hw : IsReduced w := hs
  have hg : g ∈ vertices (MonoidHom.id _) w := by
    dsimp [w]
    rw [List.append_assoc, List.append_assoc, List.append_assoc, vertices_append]
    left
    simpa only [mk_toWord, MonoidHom.id_apply] using
      endpoint_mem_vertices (MonoidHom.id _) g.toWord
  have hginv : g ∈ vertices (MonoidHom.id _) (invRev w) := by
    dsimp [w]
    simp only [invRev_append, invRev_invRev]
    rw [vertices_append]
    left
    simpa only [mk_toWord, MonoidHom.id_apply] using
      endpoint_mem_vertices (MonoidHom.id _) g.toWord
  rcases htotal (mk w) with hpos | hneg
  · refine ⟨mk w, hpos, ?_⟩
    simpa only [toWord_mk, hw.reduce_eq] using hg
  · refine ⟨(mk w)⁻¹, hneg, ?_⟩
    simpa only [toWord_inv, toWord_mk, hw.reduce_eq] using hginv

/-- A finitely generated, reflexive total precone in a nonabelian free group
must contain the whole group. Finite generation still uses nonempty products. -/
theorem eq_top_of_semigroupFG_total [Nontrivial ι]
    (P : Subsemigroup (FreeGroup ι)) (h1 : 1 ∈ P)
    (htotal : ∀ g : FreeGroup ι, g ∈ P ∨ g⁻¹ ∈ P)
    (hfg : SemigroupFG P) : P = ⊤ := by
  classical
  obtain ⟨T, hT, hcomplete⟩ := exists_finite_completions P hfg
  obtain ⟨b, hb⟩ := finite_upper_bound P h1 htotal T hT
  apply top_unique
  intro q _
  obtain ⟨g, hg, hq⟩ := exists_precone_vertex P htotal (q * b⁻¹)
  obtain ⟨r, hr, hpos⟩ := hcomplete g hg (q * b⁻¹) hq
  have hp := P.mul_mem hpos (hb r hr)
  simpa only [mul_assoc, mul_inv_cancel_left, inv_mul_cancel, mul_one] using hp

/-- Images of finite semigroup presentations remain finite semigroup
presentations; the image may contain identity. -/
theorem semigroupFG_map {H : Type*} [Group H] (φ : G →* H)
    (P : Subsemigroup G) (hfg : SemigroupFG P) :
    SemigroupFG (P.map φ.toMulHom) := by
  classical
  obtain ⟨S, rfl⟩ := hfg
  refine ⟨S.image φ, ?_⟩
  rw [Finset.coe_image, MulHom.map_mclosure]
  rfl

/-- The image of a strict product cone under the free projection is the
whole free group. Identity in this image comes from one sign of the nontrivial
central generator, without changing the original strict cone. -/
theorem projection_eq_top [Nontrivial ι]
    (P : PositiveCone (FreeGroup ι × Multiplicative ℤ)) (hfg : SemigroupFG P.1) :
    P.1.map (MonoidHom.fst (FreeGroup ι) (Multiplicative ℤ)).toMulHom = ⊤ := by
  let φ := MonoidHom.fst (FreeGroup ι) (Multiplicative ℤ)
  let Q := P.1.map φ.toMulHom
  have h1 : 1 ∈ Q := by
    rcases P.2.2 (cofinalProductZ (FreeGroup ι)) with hz | hz | hz
    · have h := congrArg (fun g : FreeGroup ι × Multiplicative ℤ => g.2.toAdd) hz
      norm_num [cofinalProductZ] at h
    · exact ⟨cofinalProductZ (FreeGroup ι), hz, rfl⟩
    · exact ⟨(cofinalProductZ (FreeGroup ι))⁻¹, hz, rfl⟩
  have htotal (g : FreeGroup ι) : g ∈ Q ∨ g⁻¹ ∈ Q := by
    rcases P.2.2 (g, 1) with he | hp | hn
    · have hg : g = 1 := congrArg Prod.fst he
      exact Or.inl (hg ▸ h1)
    · exact Or.inl ⟨(g, 1), hp, rfl⟩
    · exact Or.inr ⟨(g, 1)⁻¹, hn, rfl⟩
  exact eq_top_of_semigroupFG_total Q h1 htotal (semigroupFG_map φ P.1 hfg)

/-- Every free coordinate has a strictly positive lift. -/
theorem exists_positive_lift [Nontrivial ι]
    (P : PositiveCone (FreeGroup ι × Multiplicative ℤ)) (hfg : SemigroupFG P.1)
    (g : FreeGroup ι) : ∃ m : Multiplicative ℤ, (g, m) ∈ P.1 := by
  have hg : g ∈ P.1.map (MonoidHom.fst (FreeGroup ι) (Multiplicative ℤ)).toMulHom := by
    rw [projection_eq_top P hfg]
    trivial
  obtain ⟨⟨g', m⟩, hp, he⟩ := hg
  change g' = g at he
  subst g'
  exact ⟨m, hp⟩

private theorem central_zpow (k : ℤ) :
    cofinalProductZ (FreeGroup ι) ^ k = (1, Multiplicative.ofAdd k) := by
  simp [cofinalProductZ, ← ofAdd_zsmul]

/-- Finite semigroup generation forces cofinality of the central cyclic
factor in every strict cone on a nonabelian free group times the integers.
This stronger FG hypothesis makes the noncofinal dynamical perturbation
unnecessary for the classification endpoint. The definition of cofinality
allows integer exponents, so positivity of the chosen generator is not needed. -/
theorem center_cofinal_of_semigroupFG [Nontrivial ι]
    (P : PositiveCone (FreeGroup ι × Multiplicative ℤ)) (hfg : SemigroupFG P.1) :
    (coneLeftOrder P).IsCofinal (cofinalProductZ (FreeGroup ι)) := by
  let := (coneLeftOrder P).order
  intro g
  obtain ⟨m, hm⟩ := exists_positive_lift P hfg g.1
  obtain ⟨n, hn⟩ := exists_positive_lift P hfg g.1⁻¹
  refine ⟨g.2.toAdd - m.toAdd, g.2.toAdd + n.toAdd, ?_, ?_⟩
  · apply le_of_lt
    change (cofinalProductZ (FreeGroup ι) ^ (g.2.toAdd - m.toAdd))⁻¹ * g ∈ P.1
    have he : (cofinalProductZ (FreeGroup ι) ^ (g.2.toAdd - m.toAdd))⁻¹ * g =
        (g.1, m) := by
      rw [central_zpow]
      apply Prod.ext
      · simp
      · change Multiplicative.ofAdd (-(g.2.toAdd - m.toAdd) + g.2.toAdd) = m
        rw [neg_sub, sub_add_cancel]
        rfl
    rwa [he]
  · apply le_of_lt
    change g⁻¹ * cofinalProductZ (FreeGroup ι) ^ (g.2.toAdd + n.toAdd) ∈ P.1
    have he : g⁻¹ * cofinalProductZ (FreeGroup ι) ^ (g.2.toAdd + n.toAdd) =
        (g.1⁻¹, n) := by
      rw [central_zpow]
      apply Prod.ext
      · simp
      · change Multiplicative.ofAdd (-g.2.toAdd + (g.2.toAdd + n.toAdd)) = n
        rw [neg_add_cancel_left]
        rfl
    rwa [he]

theorem finite_rank_center_cofinal {n : ℕ} (hn : 2 ≤ n)
    (P : PositiveCone (FnZ n)) (hfg : SemigroupFG P.1) :
    (coneLeftOrder P).IsCofinal (cofinalProductZ (FreeGroup (Fin n))) := by
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  exact center_cofinal_of_semigroupFG P hfg

end FnZPositiveCones.NoncofinalPrecone
