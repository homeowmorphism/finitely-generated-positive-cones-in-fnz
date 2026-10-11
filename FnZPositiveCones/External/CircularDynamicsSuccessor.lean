module

public import FnZPositiveCones.External.CircularDynamicsTraces
public import Mathlib.GroupTheory.FreeGroup.CyclicallyReduced
public import Mathlib.Topology.UniformSpace.HeineCantor

@[expose] public section

/-! Uniform bounds for suffix collisions of pairs having a fixed group successor. -/
namespace FnZPositiveCones
namespace CircularDynamics
universe u v
variable {ι : Type u} [DecidableEq ι]

/-- If an adjacent pair has a fixed right difference, a suffix collision can add
only as many letters as occur in that fixed successor. -/
theorem successor_suffix_length_bound (u v h : FreeGroup ι)
    (hnext : v = u * h) (p : List (ι × Bool))
    (hprefix : u.toWord = p ++ v.toWord) : p.length ≤ FreeGroup.norm h := by
  have hu : u = v * h⁻¹ := by rw [hnext]; group
  have hn := FreeGroup.norm_mul_le v h⁻¹
  rw [← hu, FreeGroup.norm_inv_eq] at hn
  change u.toWord.length ≤ v.toWord.length + FreeGroup.norm h at hn
  rw [hprefix, List.length_append] at hn
  omega

/-- The same bound in the opposite suffix direction. -/
theorem successor_suffix_length_bound_rev (u v h : FreeGroup ι)
    (hnext : v = u * h) (p : List (ι × Bool))
    (hprefix : v.toWord = p ++ u.toWord) : p.length ≤ FreeGroup.norm h := by
  have hn := FreeGroup.norm_mul_le u h
  rw [← hnext] at hn
  change v.toWord.length ≤ u.toWord.length + FreeGroup.norm h at hn
  rw [hprefix, List.length_append] at hn
  omega

/-- Every conjugator stripped from a suffix-collision word has uniformly bounded
length. The displayed conjugate decomposition is an equality of actual words. -/
theorem successor_collision_conjugator_bound (u v h : FreeGroup ι)
    (hnext : v = u * h) (p q r : List (ι × Bool))
    (hprefix : u.toWord = p ++ v.toWord)
    (hconj : p = q ++ r ++ FreeGroup.invRev q) : 2 * q.length ≤ FreeGroup.norm h := by
  have hb := successor_suffix_length_bound u v h hnext p hprefix
  rw [hconj, List.length_append, List.length_append, FreeGroup.invRev_length] at hb
  omega

/-- Pinned mathlib's actual cyclic reduction therefore has a uniformly bounded
conjugator whenever the endpoints are related by the fixed successor. -/
theorem successor_cyclicReduction_bound (u v h : FreeGroup ι)
    (hnext : v = u * h) (p : List (ι × Bool))
    (hprefix : u.toWord = p ++ v.toWord) :
    2 * (FreeGroup.reduceCyclically.conjugator p).length ≤ FreeGroup.norm h := by
  apply successor_collision_conjugator_bound u v h hnext p
    (FreeGroup.reduceCyclically.conjugator p) (FreeGroup.reduceCyclically p) hprefix
  exact (FreeGroup.reduceCyclically.conj_conjugator_reduceCyclically p).symm

/-- A bounded set of reduced words over a finite alphabet is genuinely finite. -/
theorem finite_freeGroup_norm_ball [Finite ι] (N : ℕ) :
    Set.Finite {g : FreeGroup ι | FreeGroup.norm g ≤ N} := by
  classical
  let Words := (n : Fin (N + 1)) × (Fin n.val → ι × Bool)
  have hf : Set.Finite (Set.range (fun p : Words => FreeGroup.mk (List.ofFn p.2))) := Set.finite_range _
  apply hf.subset
  intro g hg
  refine ⟨⟨⟨g.toWord.length, by change g.toWord.length ≤ N at hg; omega⟩, g.toWord.get⟩, ?_⟩
  simp only [List.ofFn_get, FreeGroup.mk_toWord]

/-- Finitely many continuous maps on a compact metric space share one uniform
modulus. This is the uniformity step for bounded inverse-word translations. -/
theorem finite_family_uniform_modulus {A : Type*} {X : Type v}
    [PseudoMetricSpace X] [CompactSpace X] (S : Finset A) (f : A → X → X)
    (hf : ∀ a ∈ S, Continuous (f a)) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ x y, dist x y < δ → ∀ a ∈ S, dist (f a x) (f a y) < ε := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, zero_lt_one, fun _ _ _ a ha => (Finset.notMem_empty a ha).elim⟩
  | @insert a S ha ih =>
      have hfa := hf a (Finset.mem_insert_self a S)
      obtain ⟨δa, hδa, hma⟩ := Metric.uniformContinuous_iff.mp
        (CompactSpace.uniformContinuous_of_continuous hfa) ε hε
      obtain ⟨δS, hδS, hmS⟩ := ih (fun b hb => hf b (Finset.mem_insert_of_mem hb))
      refine ⟨min δa δS, lt_min hδa hδS, ?_⟩
      intro x y hxy b hb
      rcases Finset.mem_insert.mp hb with rfl | hb
      · exact hma (hxy.trans_le (min_le_left _ _))
      · exact hmS x y (hxy.trans_le (min_le_right _ _)) b hb

/-- All translations represented by bounded-length words have one uniform
continuity modulus, including inverse words. -/
theorem bounded_word_uniform_modulus [Finite ι] {X : Type v}
    [PseudoMetricSpace X] [CompactSpace X]
    (ρ : FreeGroup ι → X → X) (hρ : ∀ g, Continuous (ρ g)) (N : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ x y, dist x y < δ → ∀ g, FreeGroup.norm g ≤ N →
      dist (ρ g x) (ρ g y) < ε := by
  classical
  let S := (finite_freeGroup_norm_ball (ι := ι) N).toFinset
  obtain ⟨δ, hδ, hm⟩ := finite_family_uniform_modulus S ρ (fun g _ => hρ g) hε
  refine ⟨δ, hδ, fun x y hxy g hg => hm x y hxy g ?_⟩
  simpa [S] using hg

end CircularDynamics
end FnZPositiveCones
