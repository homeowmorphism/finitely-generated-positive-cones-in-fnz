module

public import FnZPositiveCones.External.CircularTopology
public import FnZPositiveCones.External.CircularQuotient
public import FnZPositiveCones.External.CircularCocycle

@[expose] public section

/-! The actual multiplication cocycle of the cofinal product representatives. -/
namespace FnZPositiveCones
universe u
variable {G : Type u} [Group G]
variable (O : LeftGroupOrder (G × Multiplicative ℤ))
variable (hz : O.order.lt 1 (cofinalProductZ G)) (hc : O.IsCofinal (cofinalProductZ G))

noncomputable def cofinalSectionHeight (g : G) : ℤ :=
  (cofinalProductRepresentative O hz hc g).2.toAdd

@[simp] theorem cofinalProductRepresentative_one :
    cofinalProductRepresentative O hz hc 1 = 1 := by
  exact O.fundamentalRepresentative_eq_self hz hc ⟨O.order.le_refl 1, hz⟩

@[simp] theorem cofinalSectionHeight_one : cofinalSectionHeight O hz hc 1 = 0 := by
  simp [cofinalSectionHeight]

/-- Multiplication carries in the fundamental interval. -/
noncomputable def cofinalProductCocycle : NormalizedIntCocycle G where
  value g h := cofinalSectionHeight O hz hc g + cofinalSectionHeight O hz hc h -
    cofinalSectionHeight O hz hc (g * h)
  one_left g := by simp
  one_right g := by simp
  cocycle g h k := by rw [mul_assoc]; omega

/-- The integer carry is exactly the floor of the product of representatives. -/
theorem cofinalProductCocycle_value (g h : G) :
    (cofinalProductCocycle O hz hc).value g h =
      O.powerFloor hz hc (cofinalProductRepresentative O hz hc g *
        cofinalProductRepresentative O hz hc h) := by
  have hr := O.fundamentalRepresentative_rep_mul_rep hz hc cofinalProductZ_central
    (g, 1) (h, 1)
  have hh := congrArg (fun p : G × Multiplicative ℤ => p.2.toAdd) hr
  change (O.fundamentalRepresentative hz hc (cofinalProductRepresentative O hz hc g *
    cofinalProductRepresentative O hz hc h)).2.toAdd =
    cofinalSectionHeight O hz hc (g * h) at hh
  simp [LeftGroupOrder.fundamentalRepresentative, cofinalProductZ] at hh
  change -O.powerFloor hz hc (cofinalProductRepresentative O hz hc g *
        cofinalProductRepresentative O hz hc h) +
      (cofinalSectionHeight O hz hc g + cofinalSectionHeight O hz hc h) =
      cofinalSectionHeight O hz hc (g * h) at hh
  change cofinalSectionHeight O hz hc g + cofinalSectionHeight O hz hc h -
      cofinalSectionHeight O hz hc (g * h) = _
  omega

/-- Strict comparison from the cut at the identity is ordinary comparison of representatives. -/
theorem cofinalProductCircularGroupOrder_sbtw_one (g h : G) :
    (cofinalProductCircularGroupOrder O hz hc).order.sbtw 1 g h ↔
      O.order.lt 1 (cofinalProductRepresentative O hz hc g) ∧
      O.order.lt (cofinalProductRepresentative O hz hc g) (cofinalProductRepresentative O hz hc h) := by
  let := O.order
  change ((O.order.lt (cofinalProductRepresentative O hz hc 1) (cofinalProductRepresentative O hz hc g) ∧
      O.order.lt (cofinalProductRepresentative O hz hc g) (cofinalProductRepresentative O hz hc h)) ∨
    (O.order.lt (cofinalProductRepresentative O hz hc g) (cofinalProductRepresentative O hz hc h) ∧
      O.order.lt (cofinalProductRepresentative O hz hc h) (cofinalProductRepresentative O hz hc 1)) ∨
    (O.order.lt (cofinalProductRepresentative O hz hc h) (cofinalProductRepresentative O hz hc 1) ∧
      O.order.lt (cofinalProductRepresentative O hz hc 1) (cofinalProductRepresentative O hz hc g))) ↔ _
  rw [cofinalProductRepresentative_one]
  have hh := (O.fundamentalRepresentative_mem hz hc (h, 1)).1
  constructor
  · rintro (h | h | h)
    · exact h
    · exact (not_lt_of_ge hh h.2).elim
    · exact (not_lt_of_ge hh h.1).elim
  · exact Or.inl

/-- Nonidentity elements have representatives strictly above the identity. -/
theorem cofinalProductRepresentative_pos {g : G} (hg : g ≠ 1) :
    O.order.lt 1 (cofinalProductRepresentative O hz hc g) := by
  let := O.order
  apply lt_of_le_of_ne (O.fundamentalRepresentative_mem hz hc (g, 1)).1
  intro he
  change (1 : G × Multiplicative ℤ) = cofinalProductRepresentative O hz hc g at he
  have hf := congrArg Prod.fst he
  exact hg (by simpa only [Prod.fst_one, cofinalProductRepresentative_fst] using hf.symm)

/-- A product that does not cross the cut has carry zero. -/
theorem cofinalProductCocycle_zero_of_lt (g h : G)
    (hcut : O.order.lt (cofinalProductRepresentative O hz hc g *
      cofinalProductRepresentative O hz hc h) (cofinalProductZ G)) :
    (cofinalProductCocycle O hz hc).value g h = 0 := by
  let := O.order
  rw [cofinalProductCocycle_value]
  apply Eq.symm
  apply O.fundamentalRepresentative_unique_exponent hz hc _ 0
  simp only [neg_zero, zpow_zero, one_mul]
  refine ⟨?_, hcut⟩
  have hg := O.fundamentalRepresentative_mem hz hc (g, 1)
  have hh := O.fundamentalRepresentative_mem hz hc (h, 1)
  have hm := O.mul_le_mul_left _ _ (cofinalProductRepresentative O hz hc g) hh.1
  exact hg.1.trans (by simpa only [mul_one, cofinalProductRepresentative] using hm)

/-- A product that crosses the cut has carry one. -/
theorem cofinalProductCocycle_one_of_ge (g h : G)
    (hcut : O.order.le (cofinalProductZ G) (cofinalProductRepresentative O hz hc g *
      cofinalProductRepresentative O hz hc h)) :
    (cofinalProductCocycle O hz hc).value g h = 1 := by
  let := O.order
  rw [cofinalProductCocycle_value]
  apply Eq.symm
  apply O.fundamentalRepresentative_unique_exponent hz hc _ 1
  simp only [zpow_neg_one]
  constructor
  · simpa only [inv_mul_cancel] using O.mul_le_mul_left _ _ (cofinalProductZ G)⁻¹ hcut
  · exact (O.normalized_wrap_lt cofinalProductZ_central
      (O.fundamentalRepresentative_mem hz hc (h, 1)).2).trans
      (O.fundamentalRepresentative_mem hz hc (g, 1)).2

/-- The circular-order carry is exactly the actual multiplication carry of the cofinal section. -/
theorem cofinalProductCocycle_eq_circular_value (g h : G) :
    (cofinalProductCocycle O hz hc).value g h =
      (cofinalProductCircularGroupOrder O hz hc).toNormalizedIntCocycle.value g h := by
  classical
  let := O.order
  by_cases hg : g = 1
  · subst g
    rw [NormalizedIntCocycle.one_left, NormalizedIntCocycle.one_left]
  by_cases hh : h = 1
  · subst h
    rw [NormalizedIntCocycle.one_right, NormalizedIntCocycle.one_right]
  have hrep : O.fundamentalRepresentative hz hc
      (cofinalProductRepresentative O hz hc g * cofinalProductRepresentative O hz hc h) =
      cofinalProductRepresentative O hz hc (g * h) := by
    simpa only [cofinalProductRepresentative, Prod.mk_mul_mk, one_mul] using
      O.fundamentalRepresentative_rep_mul_rep hz hc cofinalProductZ_central (g, 1) (h, 1)
  have hgm := O.fundamentalRepresentative_mem hz hc (g, 1)
  have hhm := O.fundamentalRepresentative_mem hz hc (h, 1)
  by_cases hcut : cofinalProductRepresentative O hz hc g *
      cofinalProductRepresentative O hz hc h < cofinalProductZ G
  · rw [cofinalProductCocycle_zero_of_lt O hz hc g h hcut]
    have hr : cofinalProductRepresentative O hz hc (g * h) =
        cofinalProductRepresentative O hz hc g * cofinalProductRepresentative O hz hc h := by
      rw [← hrep]
      exact O.fundamentalRepresentative_mul_of_lt hz hc hgm hhm hcut
    have hstep : cofinalProductRepresentative O hz hc g < cofinalProductRepresentative O hz hc (g * h) := by
      rw [hr]
      simpa only [mul_one] using O.mul_lt_mul_left (cofinalProductRepresentative O hz hc g)
        (cofinalProductRepresentative_pos O hz hc hh)
    have hgh : g * h ≠ 1 := by
      intro he
      rw [he, cofinalProductRepresentative_one] at hstep
      exact (not_lt_of_ge hgm.1) hstep
    have hs : (cofinalProductCircularGroupOrder O hz hc).order.sbtw 1 g (g * h) :=
      (cofinalProductCircularGroupOrder_sbtw_one O hz hc g (g * h)).mpr
        ⟨cofinalProductRepresentative_pos O hz hc hg, hstep⟩
    simp [CircularGroupOrder.toNormalizedIntCocycle, CircularCarry.value, Ne.symm hg,
      hh, Ne.symm hgh, hs]
  · have hcut' := le_of_not_gt hcut
    rw [cofinalProductCocycle_one_of_ge O hz hc g h hcut']
    have hr : cofinalProductRepresentative O hz hc (g * h) =
        (cofinalProductZ G)⁻¹ *
          (cofinalProductRepresentative O hz hc g * cofinalProductRepresentative O hz hc h) := by
      rw [← hrep]
      exact O.fundamentalRepresentative_mul_of_ge hz hc cofinalProductZ_central hgm hhm hcut'
    have hstep : cofinalProductRepresentative O hz hc (g * h) < cofinalProductRepresentative O hz hc g := by
      rw [hr]
      exact O.normalized_wrap_lt cofinalProductZ_central hhm.2
    have hs : ¬(cofinalProductCircularGroupOrder O hz hc).order.sbtw 1 g (g * h) := by
      intro hs
      exact (not_lt_of_ge hstep.le) ((cofinalProductCircularGroupOrder_sbtw_one O hz hc g (g * h)).mp hs).2
    simp [CircularGroupOrder.toNormalizedIntCocycle, CircularCarry.value, Ne.symm hg, hh, hs]

/-- Equality is between the complete checked cocycle structures. -/
theorem cofinalProductCocycle_eq_circular :
    cofinalProductCocycle O hz hc =
      (cofinalProductCircularGroupOrder O hz hc).toNormalizedIntCocycle := by
  have he : (cofinalProductCocycle O hz hc).value =
      (cofinalProductCircularGroupOrder O hz hc).toNormalizedIntCocycle.value :=
    funext fun g => funext fun h => cofinalProductCocycle_eq_circular_value O hz hc g h
  have hExt : ∀ c d : NormalizedIntCocycle G, c.value = d.value → c = d := by
    rintro ⟨c, hc1, hc2, hc3⟩ ⟨d, hd1, hd2, hd3⟩ he
    cases he
    rfl
  exact hExt _ _ he

/-- The actual cofinal multiplication cocycle satisfies the strict circular range contract. -/
theorem cofinalProductCocycle_isCircular : (cofinalProductCocycle O hz hc).IsCircular := by
  rw [cofinalProductCocycle_eq_circular]
  exact (cofinalProductCircularGroupOrder O hz hc).toNormalizedIntCocycle_isCircular

/-- The extension of the actual carry is isomorphic to the original product, with explicit inverse. -/
noncomputable def cofinalProductExtensionEquiv :
    (cofinalProductCocycle O hz hc).Extension ≃* (G × Multiplicative ℤ) where
  toFun x := (x.base, Multiplicative.ofAdd (cofinalSectionHeight O hz hc x.base + x.height))
  invFun p := ⟨p.1, p.2.toAdd - cofinalSectionHeight O hz hc p.1⟩
  left_inv x := by ext <;> simp
  right_inv p := by ext <;> simp
  map_mul' x y := by
    apply Prod.ext
    · rfl
    · change cofinalSectionHeight O hz hc (x.base * y.base) +
        (x.height + y.height + (cofinalProductCocycle O hz hc).value x.base y.base) =
        (cofinalSectionHeight O hz hc x.base + x.height) +
          (cofinalSectionHeight O hz hc y.base + y.height)
      change cofinalSectionHeight O hz hc (x.base * y.base) +
        (x.height + y.height + (cofinalSectionHeight O hz hc x.base +
          cofinalSectionHeight O hz hc y.base - cofinalSectionHeight O hz hc (x.base * y.base))) = _
      omega

theorem cofinalProductRepresentative_eq (g : G) :
    cofinalProductRepresentative O hz hc g = (g, Multiplicative.ofAdd (cofinalSectionHeight O hz hc g)) := by
  apply Prod.ext
  · exact cofinalProductRepresentative_fst O hz hc g
  · rfl

/-- Extension height is the power coordinate relative to the fundamental representative. -/
theorem cofinalProductExtensionEquiv_eq_zpow
    (x : (cofinalProductCocycle O hz hc).Extension) :
    cofinalProductExtensionEquiv O hz hc x =
      cofinalProductZ G ^ x.height * cofinalProductRepresentative O hz hc x.base := by
  rw [cofinalProductRepresentative_eq]
  apply Prod.ext
  · simp [cofinalProductExtensionEquiv, cofinalProductZ]
  · change cofinalSectionHeight O hz hc x.base + x.height =
      (cofinalProductZ G ^ x.height).2.toAdd + cofinalSectionHeight O hz hc x.base
    simp [cofinalProductZ, add_comm]

/-- The extension integer is exactly the floor in the original order. -/
theorem cofinalProductExtensionEquiv_floor
    (x : (cofinalProductCocycle O hz hc).Extension) :
    O.powerFloor hz hc (cofinalProductExtensionEquiv O hz hc x) = x.height := by
  apply Eq.symm
  apply O.fundamentalRepresentative_unique_exponent hz hc
  rw [cofinalProductExtensionEquiv_eq_zpow]
  simpa only [← mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, one_mul,
    cofinalProductRepresentative] using O.fundamentalRepresentative_mem hz hc (x.base, 1)

/-- The strict extension cone recovers the original order, not merely some left order. -/
theorem cofinalProductExtensionEquiv_positive_iff
    (x : (cofinalProductCocycle O hz hc).Extension) :
    O.order.lt 1 (cofinalProductExtensionEquiv O hz hc x) ↔
      x ∈ (cofinalProductCocycle O hz hc).positive (cofinalProductCocycle_isCircular O hz hc) := by
  let := O.order
  change 1 < cofinalProductExtensionEquiv O hz hc x ↔
    0 < x.height ∨ (x.height = 0 ∧ x.base ≠ 1)
  have hm := O.powerFloor_spec hz hc (cofinalProductExtensionEquiv O hz hc x)
  rw [cofinalProductExtensionEquiv_floor] at hm
  have hmono := O.zpow_strictMono hz
  constructor
  · intro hp
    by_cases hzero : x.height = 0
    · right
      refine ⟨hzero, ?_⟩
      intro hbase
      have he : cofinalProductExtensionEquiv O hz hc x = 1 := by
        simp [cofinalProductExtensionEquiv, hzero, hbase]
      rw [he] at hp
      exact lt_irrefl _ hp
    · left
      by_contra hneg
      have hle : x.height + 1 ≤ 0 := by omega
      have hzle : cofinalProductZ G ^ (x.height + 1) ≤ 1 := by simpa using hmono.monotone hle
      exact not_lt_of_ge hp.le (hm.2.trans_le hzle)
  · rintro (hpos | ⟨hzero, hbase⟩)
    · have hzlt : 1 < cofinalProductZ G ^ x.height := by simpa using hmono hpos
      exact hzlt.trans_le hm.1
    · rw [cofinalProductExtensionEquiv_eq_zpow, hzero, zpow_zero, one_mul]
      exact cofinalProductRepresentative_pos O hz hc hbase

section FreeGroup
variable {ι : Type u}
variable (O : LeftGroupOrder (FreeGroup ι × Multiplicative ℤ))
variable (hz : O.order.lt 1 (cofinalProductZ (FreeGroup ι)))
variable (hc : O.IsCofinal (cofinalProductZ (FreeGroup ι)))

/-- Generator heights that make the lifted circular order pass through the given cofinal order. -/
noncomputable def cofinalGeneratorHeights (i : ι) : ℤ :=
  -cofinalSectionHeight O hz hc (FreeGroup.of i)

/-- The chosen free section maps to the original marked free generators. -/
theorem cofinalProductExtensionEquiv_freeSection :
    (cofinalProductExtensionEquiv O hz hc).toMonoidHom.comp
      ((cofinalProductCocycle O hz hc).freeSection (cofinalGeneratorHeights O hz hc)) =
      MonoidHom.inl (FreeGroup ι) (Multiplicative ℤ) := by
  apply FreeGroup.ext_hom
  intro i
  apply Prod.ext
  · simp [NormalizedIntCocycle.freeSection, cofinalProductExtensionEquiv]
  · simp [NormalizedIntCocycle.freeSection, cofinalProductExtensionEquiv, cofinalGeneratorHeights]

/-- Splitting with these fixed generator heights recovers the identity of the original product. -/
theorem cofinalProductExtensionEquiv_freeProductHom (p : FreeGroup ι × Multiplicative ℤ) :
    cofinalProductExtensionEquiv O hz hc
      ((cofinalProductCocycle O hz hc).freeProductHom (cofinalGeneratorHeights O hz hc) p) = p := by
  change cofinalProductExtensionEquiv O hz hc
    (((cofinalProductCocycle O hz hc).freeSection (cofinalGeneratorHeights O hz hc) p.1) *
      (cofinalProductCocycle O hz hc).central p.2) = p
  rw [map_mul]
  have he := DFunLike.congr_fun (cofinalProductExtensionEquiv_freeSection O hz hc) p.1
  change cofinalProductExtensionEquiv O hz hc
    ((cofinalProductCocycle O hz hc).freeSection (cofinalGeneratorHeights O hz hc) p.1) = (p.1, 1) at he
  rw [he]
  have hz' : cofinalProductExtensionEquiv O hz hc ((cofinalProductCocycle O hz hc).central p.2) =
      (1, p.2) := by
    simp [cofinalProductExtensionEquiv, NormalizedIntCocycle.central]
  rw [hz']
  simp

/-- The recovered positive semigroup is exactly the original order's cone. -/
theorem cofinalProductPositive_recovery :
    (cofinalProductCocycle O hz hc).freeProductPositive (cofinalGeneratorHeights O hz hc)
      (cofinalProductCocycle_isCircular O hz hc) = (leftOrderCone O).val := by
  ext p
  change ((cofinalProductCocycle O hz hc).freeProductHom (cofinalGeneratorHeights O hz hc) p) ∈
      (cofinalProductCocycle O hz hc).positive (cofinalProductCocycle_isCircular O hz hc) ↔ O.order.lt 1 p
  rw [← cofinalProductExtensionEquiv_positive_iff, cofinalProductExtensionEquiv_freeProductHom]

/-- The lift of the actual quotient circular order, with fixed marked generator heights,
passes through the given cofinal left order. -/
theorem cofinalCircularProductPositive_recovery :
    (cofinalProductCircularGroupOrder O hz hc).toNormalizedIntCocycle.freeProductPositive
      (cofinalGeneratorHeights O hz hc)
      (cofinalProductCircularGroupOrder O hz hc).toNormalizedIntCocycle_isCircular =
      (leftOrderCone O).val := by
  have h := cofinalProductPositive_recovery O hz hc
  simpa only [cofinalProductCocycle_eq_circular] using h

/-- The continuous lift with the chosen generator heights passes through the original cone. -/
theorem circularFreeProductCone_cofinalProductCircularGroupOrder :
    circularFreeProductCone (cofinalGeneratorHeights O hz hc)
      (cofinalProductCircularGroupOrder O hz hc) = leftOrderCone O := by
  apply Subtype.ext
  exact cofinalCircularProductPositive_recovery O hz hc

/-- An isolated left order with positive cofinal center induces an isolated circular order.
The proof uses the continuous injective lift through this specific order. -/
theorem isOpen_singleton_cofinalProductCircularGroupOrder
    (hiso : IsOpen ({O} : Set (LeftGroupOrder (FreeGroup ι × Multiplicative ℤ)))) :
    IsOpen ({cofinalProductCircularGroupOrder O hz hc} : Set (CircularGroupOrder (FreeGroup ι))) := by
  apply isOpen_singleton_of_circularFreeProductCone (cofinalGeneratorHeights O hz hc)
  rw [circularFreeProductCone_cofinalProductCircularGroupOrder]
  apply (finiteDetermination_iff_isolated (leftOrderCone O)).mp
  apply (finiteDetermination_iff_leftOrder_isolated (leftOrderCone O)).mpr
  simpa only [coneLeftOrder_leftOrderCone] using hiso

end FreeGroup
end FnZPositiveCones
