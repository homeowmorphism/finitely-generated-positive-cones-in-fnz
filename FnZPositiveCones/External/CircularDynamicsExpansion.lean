module

public import FnZPositiveCones.External.PingPongGaps

@[expose] public section

/-! The finite principal-gap enlargement from Mann--Rivas Proposition 4.7. -/
namespace FnZPositiveCones
namespace CircularDynamics
universe u v
variable {ι : Type u} {X : Type v} {N : ℕ}

/-- Add a terminal part of the preceding gap to each word letter, and the
initial part of the following gap to its inverse. All pieces are actual chart
images of closed real intervals. -/
def expandAlongGapChain (D : ι × Bool → Set X) (word : Fin N → ι × Bool)
    (chart : Fin (N + 1) → ℝ → X) (cut : Fin N → ℝ) (s : ι × Bool) : Set X :=
  D s ∪ {x | ∃ j, word j = s ∧ ∃ t ∈ Set.Icc (cut j) 1, chart j.castSucc t = x} ∪
    {x | ∃ j, PingPong.inverseLetter (word j) = s ∧
      ∃ t ∈ Set.Icc 0 (cut j), chart j.succ t = x}

theorem subset_expandAlongGapChain (D : ι × Bool → Set X) (word : Fin N → ι × Bool)
    (chart : Fin (N + 1) → ℝ → X) (cut : Fin N → ℝ) (s : ι × Bool) :
    D s ⊆ expandAlongGapChain D word chart cut s := fun _ hx => Or.inl (Or.inl hx)

theorem mem_expandAlongGapChain_right (D : ι × Bool → Set X) (word : Fin N → ι × Bool)
    (chart : Fin (N + 1) → ℝ → X) (cut : Fin N → ℝ) (j : Fin N) {t : ℝ}
    (ht : t ∈ Set.Icc (cut j) 1) :
    chart j.castSucc t ∈ expandAlongGapChain D word chart cut (word j) :=
  Or.inl (Or.inr ⟨j, rfl, t, ht, rfl⟩)

theorem mem_expandAlongGapChain_left (D : ι × Bool → Set X) (word : Fin N → ι × Bool)
    (chart : Fin (N + 1) → ℝ → X) (cut : Fin N → ℝ) (j : Fin N) {t : ℝ}
    (ht : t ∈ Set.Icc 0 (cut j)) :
    chart j.succ t ∈ expandAlongGapChain D word chart cut (PingPong.inverseLetter (word j)) :=
  Or.inr ⟨j, rfl, t, ht, rfl⟩

/-- Full complement ping-pong follows from the actual finite gap chain. The two
exceptional letters move one gap to its neighbor; every other letter sends the
gap into a raw colored domain. Thus no full complement condition is assumed. -/
theorem expandAlongGapChain_fullPingPong
    (ρ : ι → Equiv.Perm X) (base : X) (D : ι × Bool → Set X)
    (word : Fin N → ι × Bool) (chart : Fin (N + 1) → ℝ → X) (cut : Fin N → ℝ)
    (htrap : PingPong.DomainTrapping ρ D)
    (hbase : ∀ s, letterPerm ρ s base ∈ D s)
    (hcover : ∀ x, x = base ∨ (∃ s, x ∈ D s) ∨
      ∃ i t, t ∈ Set.Ioo (0 : ℝ) 1 ∧ chart i t = x)
    (hstep : ∀ j t, letterPerm ρ (PingPong.inverseLetter (word j)) (chart j.castSucc t) =
      chart j.succ t)
    (hother : ∀ i s t, t ∈ Set.Ioo (0 : ℝ) 1 →
      (¬∃ j, i = j.succ ∧ s = word j) →
      (¬∃ j, i = j.castSucc ∧ s = PingPong.inverseLetter (word j)) →
      letterPerm ρ s (chart i t) ∈ D s) :
    ∀ s, Set.MapsTo (letterPerm ρ s)
      (expandAlongGapChain D word chart cut (PingPong.inverseLetter s))ᶜ
      (expandAlongGapChain D word chart cut s) := by
  classical
  intro s x hx
  rcases hcover x with rfl | ⟨t, ht⟩ | ⟨i, t, ht, rfl⟩
  · exact subset_expandAlongGapChain _ _ _ _ _ (hbase s)
  · have hts : t ≠ PingPong.inverseLetter s := by
      intro he
      exact hx (subset_expandAlongGapChain _ _ _ _ _ (he ▸ ht))
    exact subset_expandAlongGapChain _ _ _ _ _ (htrap s t hts ht)
  · by_cases hleft : ∃ j, i = j.succ ∧ s = word j
    · obtain ⟨j, rfl, rfl⟩ := hleft
      have hcut : cut j < t := by
        by_contra h
        exact hx (mem_expandAlongGapChain_left _ _ _ _ j ⟨ht.1.le, le_of_not_gt h⟩)
      have he : letterPerm ρ (word j) (chart j.succ t) = chart j.castSucc t := by
        have hh := congrArg (letterPerm ρ (word j)) (hstep j t)
        simpa [PingPong.letterPerm_inverseLetter] using hh.symm
      rw [he]
      exact mem_expandAlongGapChain_right _ _ _ _ j ⟨hcut.le, ht.2.le⟩
    · by_cases hright : ∃ j, i = j.castSucc ∧ s = PingPong.inverseLetter (word j)
      · obtain ⟨j, rfl, rfl⟩ := hright
        have hcut : t < cut j := by
          by_contra h
          apply hx
          simpa only [PingPong.inverseLetter_inverse] using
            mem_expandAlongGapChain_right D word chart cut j ⟨le_of_not_gt h, ht.2.le⟩
        rw [hstep]
        exact mem_expandAlongGapChain_left _ _ _ _ j ⟨ht.1.le, hcut.le⟩
      · exact subset_expandAlongGapChain _ _ _ _ _ (hother i s t ht hleft hright)

end CircularDynamics
end FnZPositiveCones
