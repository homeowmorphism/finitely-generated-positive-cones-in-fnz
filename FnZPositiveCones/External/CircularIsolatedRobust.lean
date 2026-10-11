module

public import FnZPositiveCones.External.CircularIsolatedDomains

@[expose] public section

/-! A finite, action-independent freeness certificate forced by isolation. -/
namespace FnZPositiveCones
namespace CircularDynamics
universe u v
variable {ι : Type u} [Nonempty ι] {X : Type v} [CircularOrder X]

/-- Isolation yields one finite orbit configuration which forces the entire
orbit of every compatible action to be free. The action is arbitrary and need
not arise from a faithful representation or have a free orbit in advance.
This is the robust-freeness input for finite partial-action perturbations. -/
theorem isolated_finite_freeness_certificate
    (O : CircularGroupOrder (FreeGroup ι))
    (hi : IsOpen ({O} : Set (CircularGroupOrder (FreeGroup ι)))) :
    ∃ S : Finset (FreeGroup ι), 1 ∈ S ∧
      ∀ (ρ : FreeGroup ι →* Equiv.Perm X) (hρ : ∀ g, PreservesCircular (ρ g)) (x : X),
        (∀ a ∈ S, ∀ b ∈ S, a ≠ b → ρ a x ≠ ρ b x) →
        (∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S,
          sbtw (ρ a x) (ρ b x) (ρ c x) ↔ O.order.sbtw a b c) →
        Function.Injective (fun g => ρ g x) ∧
          ∀ L : LeftGroupOrder (FreeGroup ι), completedCircularOrbitOrder ρ hρ x L = O := by
  classical
  obtain ⟨F, hF⟩ := (circularOrder_isolated_iff_finite_signs O).mp hi
  let g₀ := FreeGroup.of (Classical.arbitrary ι)
  let T : Finset (FreeGroup ι) :=
    F.image Prod.fst ∪ F.image (fun p => p.2.1) ∪ F.image (fun p => p.2.2)
  let S := insert 1 (insert g₀ T)
  have hTS : T ⊆ S := fun _ hx => Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx)
  refine ⟨S, Finset.mem_insert_self _ _, ?_⟩
  intro ρ hρ x hinj hsign
  have hg₀ : ρ g₀ x ≠ x := by
    have hh := hinj g₀ (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
      1 (Finset.mem_insert_self _ _) (FreeGroup.of_ne_one _)
    simpa only [map_one, Equiv.Perm.one_apply] using hh
  have heq (L : LeftGroupOrder (FreeGroup ι)) : completedCircularOrbitOrder ρ hρ x L = O := by
    apply hF
    intro p hp
    have h1 : p.1 ∈ S := hTS
      (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨p, hp, rfl⟩)))
    have h2 : p.2.1 ∈ S := hTS
      (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨p, hp, rfl⟩)))
    have h3 : p.2.2 ∈ S := hTS (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨p, hp, rfl⟩))
    have hs := completedCircularOrbitOrder_sign_of_orbit_sign ρ hρ x L O p.1 p.2.1 p.2.2
      (hinj _ h1 _ h2) (hinj _ h2 _ h3) (hinj _ h3 _ h1) (hsign _ h1 _ h2 _ h3)
    simpa only [circularOrderSign, decide_eq_decide] using hs
  have hfix : ∀ k, ρ k x = x → k = 1 := by
    intro k hk
    by_contra hne
    let L := freeGroupLeftOrderOfCircular O
    exact completedCircularOrbitOrder_ne_reverse ρ hρ x L k g₀ hne hk hg₀
      ((heq L).trans (heq L.reverse).symm)
  refine ⟨?_, heq⟩
  intro a b hab
  change ρ a x = ρ b x at hab
  apply inv_mul_eq_one.mp (hfix (a⁻¹ * b) ?_)
  rw [map_mul, map_inv]
  change (ρ a).symm (ρ b x) = x
  rw [← hab, Equiv.symm_apply_apply]

/-- In particular, compatible finite orbit data cannot extend to any actual
action with a nontrivial stabilizer. This exposes exactly what a partial-action
merging construction must contradict. -/
theorem isolated_finite_no_stabilizer_certificate
    (O : CircularGroupOrder (FreeGroup ι))
    (hi : IsOpen ({O} : Set (CircularGroupOrder (FreeGroup ι)))) :
    ∃ S : Finset (FreeGroup ι),
      ∀ (ρ : FreeGroup ι →* Equiv.Perm X) (_hρ : ∀ g, PreservesCircular (ρ g)) (x : X),
        (∀ a ∈ S, ∀ b ∈ S, a ≠ b → ρ a x ≠ ρ b x) →
        (∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S,
          sbtw (ρ a x) (ρ b x) (ρ c x) ↔ O.order.sbtw a b c) →
        ∀ k, k ≠ 1 → ρ k x ≠ x := by
  obtain ⟨S, h1, hS⟩ := isolated_finite_freeness_certificate (X := X) O hi
  refine ⟨S, ?_⟩
  intro ρ hρ x hinj hsign k hk hfix
  apply hk
  apply (hS ρ hρ x hinj hsign).1
  simpa only [map_one, Equiv.Perm.one_apply] using hfix

end CircularDynamics
end FnZPositiveCones
