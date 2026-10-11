module

public import FnZPositiveCones.External.NoncofinalIsolatedTower
public import FnZPositiveCones.External.FreeGroupNonIsolation

@[expose] public section

/-! A countable free group carrying an isolated order is cyclic. Convex
subgroups inherit this conclusion through finite determination, including
subgroups whose first projection embeds them in a free group. -/

namespace FnZPositiveCones.CyclicConvexSubgroups

universe u v
variable {G : Type u} [Group G]

/-- A basis with at most one element gives a cyclic free group; the empty
basis is included. -/
private theorem freeGroup_isCyclic_of_subsingleton {ι : Type u} [Subsingleton ι] :
    IsCyclic (FreeGroup ι) := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl he => have : IsEmpty ι := he; infer_instance
  | inr hn =>
    let : Unique ι := ⟨⟨Classical.choice hn⟩, fun _ => Subsingleton.elim _ _⟩
    infer_instance

/-- Nonabelian free-group nonisolation forces the actual free basis to have
at most one element. No rank upper bound is substituted for cyclicity. -/
theorem isFreeGroup_isCyclic_of_finitelyDetermined [Countable G] [IsFreeGroup G]
    (P : PositiveCone G) (hfd : FinitelyDetermined P.1) : IsCyclic G := by
  classical
  let e := IsFreeGroup.toFreeGroup G
  have : Countable (IsFreeGroup.Generators G) :=
    Function.Injective.countable (e.symm.injective.comp FreeGroup.of_injective)
  have hsmall : Subsingleton (IsFreeGroup.Generators G) := by
    by_contra h
    have : Nontrivial (IsFreeGroup.Generators G) := not_subsingleton_iff_nontrivial.mp h
    exact FreeGroupNonIsolation.not_finitelyDetermined
      (NoncofinalFreeTowerModel.transportCone P e)
      (NoncofinalIsolatedTower.transport_finitelyDetermined P e hfd)
  let := hsmall
  exact e.isCyclic.mpr freeGroup_isCyclic_of_subsingleton

/-- Every convex subgroup which is free inherits cyclicity from an isolated
ambient order. Normality and finite generation are not required. -/
theorem convex_isFreeGroup_isCyclic [Countable G]
    (P : PositiveCone G) (hfd : FinitelyDetermined P.1)
    (K : Subgroup G) (hK : ConeConvex P K) [IsFreeGroup K] : IsCyclic K :=
  isFreeGroup_isCyclic_of_finitelyDetermined (NoncofinalConvex.restrictedCone P K)
    (hK.finitelyDetermined_restrict hfd)

/-- An injective map into a free group supplies the checked Nielsen–Schreier
basis before applying the cyclicity theorem. -/
theorem convex_isCyclic_of_injective_free_hom [Countable G] {ι : Type v}
    (P : PositiveCone G) (hfd : FinitelyDetermined P.1)
    (K : Subgroup G) (hK : ConeConvex P K)
    (φ : K →* FreeGroup ι) (hφ : Function.Injective φ) : IsCyclic K := by
  let e := MonoidHom.ofInjective hφ
  let : IsFreeGroup K := ((IsFreeGroup.basis φ.range).map e.symm).isFreeGroup
  exact convex_isFreeGroup_isCyclic P hfd K hK

/-- A convex subgroup of the free-group product whose free projection is
injective is cyclic. This applies to bounded real interval stabilizers. -/
theorem convex_isCyclic_of_projection_injective {ι : Type u} [Countable ι]
    (P : PositiveCone (FreeGroup ι × Multiplicative ℤ)) (hfd : FinitelyDetermined P.1)
    (K : Subgroup (FreeGroup ι × Multiplicative ℤ)) (hK : ConeConvex P K)
    (hproj : Function.Injective (fun k : K => (k : FreeGroup ι × Multiplicative ℤ).1)) :
    IsCyclic K :=
  convex_isCyclic_of_injective_free_hom P hfd K hK
    ((MonoidHom.fst (FreeGroup ι) (Multiplicative ℤ)).comp K.subtype) hproj

/-- Convex root closure applies to every nonzero integer power, including
negative exponents. -/
theorem mem_convex_of_zpow_mem (O : LeftGroupOrder G) (K : Subgroup G)
    (hK : letI := O.order; Set.OrdConnected (K : Set G))
    {g : G} {n : ℤ} (hn : n ≠ 0) (hg : g ^ n ∈ K) : g ∈ K := by
  cases n with
  | ofNat n =>
    have hn' : n ≠ 0 := by
      intro he
      subst n
      exact hn rfl
    exact O.mem_convex_of_pow_mem K hK (Nat.pos_of_ne_zero hn') (by simpa using hg)
  | negSucc n =>
    exact O.mem_convex_of_pow_mem K hK (Nat.succ_pos n) (by simpa using K.inv_mem hg)

/-- A convex subgroup containing a cofinal element is the whole group. -/
theorem convex_eq_top_of_cofinal_mem (O : LeftGroupOrder G) (K : Subgroup G)
    (hK : letI := O.order; Set.OrdConnected (K : Set G))
    (z : G) (hz : z ∈ K) (hc : O.IsCofinal z) : K = ⊤ := by
  let := O.order
  apply top_unique
  intro g _
  obtain ⟨m, n, hm, hn⟩ := hc g
  exact hK.out (K.zpow_mem hz m) (K.zpow_mem hz n) ⟨hm, hn⟩

/-- In a cofinal product order every proper convex subgroup embeds in the
first factor. A nontrivial element of the kernel would force the central
generator, and hence the whole group, into the subgroup. -/
theorem proper_convex_projection_injective
    (O : LeftGroupOrder (G × Multiplicative ℤ))
    (hc : O.IsCofinal (cofinalProductZ G))
    (K : Subgroup (G × Multiplicative ℤ))
    (hK : letI := O.order; Set.OrdConnected (K : Set (G × Multiplicative ℤ)))
    (hne : K ≠ ⊤) :
    Function.Injective (fun k : K => (k : G × Multiplicative ℤ).1) := by
  have hker (g : G × Multiplicative ℤ) (hg : g ∈ K) (hfst : g.1 = 1) : g = 1 := by
    have he : g = cofinalProductZ G ^ g.2.toAdd := by
      apply Prod.ext
      · simpa [cofinalProductZ] using hfst
      · apply Multiplicative.toAdd.injective
        simp [cofinalProductZ]
    by_cases hn : g.2.toAdd = 0
    · simpa only [hn, zpow_zero] using he
    · have hz : cofinalProductZ G ∈ K :=
        mem_convex_of_zpow_mem O K hK hn (he ▸ hg)
      exact (hne (convex_eq_top_of_cofinal_mem O K hK _ hz hc)).elim
  intro a b hab
  change a.val.1 = b.val.1 at hab
  have h : (a : G × Multiplicative ℤ)⁻¹ * (b : G × Multiplicative ℤ) = 1 :=
    hker _ (K.mul_mem (K.inv_mem a.2) b.2) (by
      change a.val.1⁻¹ * b.val.1 = 1
      rw [hab, inv_mul_cancel])
  exact Subtype.ext (inv_mul_eq_one.mp h)

/-- Every proper convex subgroup of an isolated cofinal free-group product
is cyclic. This statement has no separate injectivity or normality premise. -/
theorem proper_convex_isCyclic {ι : Type u} [Countable ι]
    (P : PositiveCone (FreeGroup ι × Multiplicative ℤ)) (hfd : FinitelyDetermined P.1)
    (hc : (coneLeftOrder P).IsCofinal (cofinalProductZ (FreeGroup ι)))
    (K : Subgroup (FreeGroup ι × Multiplicative ℤ)) (hK : ConeConvex P K) (hne : K ≠ ⊤) :
    IsCyclic K :=
  convex_isCyclic_of_projection_injective P hfd K hK
    (proper_convex_projection_injective (coneLeftOrder P) hc K hK hne)

end FnZPositiveCones.CyclicConvexSubgroups
