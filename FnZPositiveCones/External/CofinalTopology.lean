module

public import FnZPositiveCones.External.FiniteCentral

@[expose] public section

/-!
# Openness of positive central cofinality

Finite group generators reduce central cofinality to finitely many power bounds.
When the central element is positive, weak bounds can be enlarged to strict
bounds, which are open conditions in the product sign topology. This supplies
the open domain for the cofinal quotient construction, but does not supply the
separate circular-order local section.
-/

namespace FnZPositiveCones

universe u
variable {G : Type u} [Group G]

/-- A strict comparison is an open sign coordinate on the space of left orders. -/
theorem isOpen_leftOrder_lt (g h : G) :
    IsOpen {O : LeftGroupOrder G | O.order.lt g h} := by
  have hc : Continuous (fun O : LeftGroupOrder G => leftOrderSign O (g, h)) :=
    (continuous_apply (g, h)).comp
      (show Continuous (leftOrderSign (G := G)) from continuous_induced_dom)
  convert (isOpen_discrete ({true} : Set Bool)).preimage hc using 1
  ext O
  simp [leftOrderSign]

/-- Existence of strict integer-power bounds is open in the sign topology. -/
theorem isOpen_leftOrder_strictPowerBounds (z g : G) :
    IsOpen {O : LeftGroupOrder G | ∃ m n : ℤ,
      O.order.lt (z ^ m) g ∧ O.order.lt g (z ^ n)} := by
  have he : {O : LeftGroupOrder G | ∃ m n : ℤ,
      O.order.lt (z ^ m) g ∧ O.order.lt g (z ^ n)} =
      ⋃ m : ℤ, ⋃ n : ℤ, {O : LeftGroupOrder G | O.order.lt (z ^ m) g} ∩
        {O : LeftGroupOrder G | O.order.lt g (z ^ n)} := by
    ext O
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
  rw [he]
  exact isOpen_iUnion fun m => isOpen_iUnion fun n =>
    (isOpen_leftOrder_lt (z ^ m) g).inter (isOpen_leftOrder_lt g (z ^ n))

/-- For positive elements, integer-power bounds can always be made strict. -/
theorem LeftGroupOrder.strictPowerBounds_of_isCofinal (O : LeftGroupOrder G)
    {z : G} (hz : O.order.lt 1 z) (hc : O.IsCofinal z) (g : G) :
    ∃ m n : ℤ, O.order.lt (z ^ m) g ∧ O.order.lt g (z ^ n) := by
  let := O.order
  obtain ⟨m, n, hm, hn⟩ := hc g
  have hmono := O.zpow_strictMono hz
  exact ⟨m - 1, n + 1, (hmono (by omega : m - 1 < m)).trans_le hm,
    hn.trans_lt (hmono (by omega : n < n + 1))⟩

/-- Finite subgroup generators give an explicit open description of positive
cofinality for a fixed central element. No normality of other subgroups is used. -/
theorem isOpen_positiveCofinal_of_generators (z : G)
    (hcentral : ∀ g : G, Commute z g) (S : Finset G)
    (hS : Subgroup.closure (S : Set G) = ⊤) :
    IsOpen {O : LeftGroupOrder G | O.order.lt 1 z ∧ O.IsCofinal z} := by
  have he : {O : LeftGroupOrder G | O.order.lt 1 z ∧ O.IsCofinal z} =
      {O : LeftGroupOrder G | O.order.lt 1 z} ∩
        ⋂ s ∈ S, {O : LeftGroupOrder G | ∃ m n : ℤ,
          O.order.lt (z ^ m) s ∧ O.order.lt s (z ^ n)} := by
    ext O
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
    constructor
    · rintro ⟨hz, hc⟩
      exact ⟨hz, fun s _ => O.strictPowerBounds_of_isCofinal hz hc s⟩
    · rintro ⟨hz, hb⟩
      refine ⟨hz, O.isCofinal_of_generators_bounded z hcentral S hS ?_⟩
      intro s hs
      obtain ⟨m, n, hm, hn⟩ := hb s hs
      let := O.order
      exact ⟨m, n, hm.le, hn.le⟩
  rw [he]
  exact (isOpen_leftOrder_lt 1 z).inter
    (isOpen_biInter_finset fun s _ => isOpen_leftOrder_strictPowerBounds z s)

/-- In a finitely generated group the positive-cofinal locus of a fixed central
element is open in the actual topology of left-order signs. -/
theorem isOpen_positiveCofinal [Group.FG G] (z : G)
    (hcentral : ∀ g : G, Commute z g) :
    IsOpen {O : LeftGroupOrder G | O.order.lt 1 z ∧ O.IsCofinal z} := by
  obtain ⟨S, hS, hfin⟩ := Group.fg_iff.mp (inferInstance : Group.FG G)
  classical
  exact isOpen_positiveCofinal_of_generators z hcentral hfin.toFinset (by simpa using hS)

/-- The same open locus in the strict-positive-cone sign topology. -/
theorem isOpen_positiveCone_cofinal [Group.FG G] (z : G)
    (hcentral : ∀ g : G, Commute z g) :
    IsOpen {P : PositiveCone G | z ∈ P.1 ∧ (coneLeftOrder P).IsCofinal z} := by
  have h := (isOpen_positiveCofinal z hcentral).preimage
    (positiveConeHomeomorphLeftOrder (G := G)).continuous
  change IsOpen {P : PositiveCone G | (coneLeftOrder P).order.lt 1 z ∧
    (coneLeftOrder P).IsCofinal z} at h
  simpa only [coneLeftOrder_lt, inv_one, one_mul] using h

end FnZPositiveCones
