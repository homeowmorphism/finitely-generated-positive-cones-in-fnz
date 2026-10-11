module

public import FnZPositiveCones.External.NoncofinalConvexJump

@[expose] public section

namespace FnZPositiveCones.NoncofinalDenseAction
open NoncofinalCrossings
universe u v
variable {G : Type u} [Group G] {X : Type v} [LinearOrder X]

/-- Finite intervals form a transitive relation in any linear order. -/
theorem finite_uIcc_trans {x y z : X} (hxy : (Set.uIcc x y).Finite)
    (hyz : (Set.uIcc y z).Finite) : (Set.uIcc x z).Finite :=
  (hxy.union hyz).subset Set.uIcc_subset_uIcc_union_uIcc

theorem finite_uIcc_map (f : X ≃o X) {x y : X} (h : (Set.uIcc x y).Finite) :
    (Set.uIcc (f x) (f y)).Finite := by
  apply (h.image f).subset
  intro z hz
  refine ⟨f.symm z, ?_, f.apply_symm_apply z⟩
  rw [Set.mem_uIcc] at hz ⊢
  rcases hz with hz | hz
  · exact Or.inl ⟨f.le_iff_le.mp (by simpa using hz.1),
      f.le_iff_le.mp (by simpa using hz.2)⟩
  · exact Or.inr ⟨f.le_iff_le.mp (by simpa using hz.1),
      f.le_iff_le.mp (by simpa using hz.2)⟩

/-- Elements moving the basepoint by a finite interval form a subgroup. -/
def finiteIntervalSubgroup (ρ : G →* (X ≃o X)) (x : X) : Subgroup G where
  carrier := {g | (Set.uIcc x (ρ g x)).Finite}
  one_mem' := by simp
  mul_mem' := by
    intro g h hg hh
    change (Set.uIcc x (ρ (g * h) x)).Finite
    have hm := finite_uIcc_map (ρ g) hh
    simpa only [map_mul, RelIso.mul_apply] using finite_uIcc_trans hg hm
  inv_mem' := by
    intro g hg
    change (Set.uIcc x (ρ g⁻¹ x)).Finite
    have hm := finite_uIcc_map (ρ g⁻¹) hg
    simpa only [map_inv, RelIso.inv_apply_self, Set.uIcc_comm] using hm

/-- Monotone orbit maps make the finite-interval subgroup convex. -/
theorem finiteIntervalSubgroup_convex (O : LeftGroupOrder G) (ρ : G →* (X ≃o X))
    (x : X) (hmono : ∀ a b, O.order.le a b → ρ a x ≤ ρ b x) :
    letI := O.order; Set.OrdConnected (finiteIntervalSubgroup ρ x : Set G) := by
  let := O.order
  constructor
  intro a ha b hb g hg
  change (Set.uIcc x (ρ g x)).Finite
  change (Set.uIcc x (ρ a x)).Finite at ha
  change (Set.uIcc x (ρ b x)).Finite at hb
  have hab := finite_uIcc_trans (by simpa only [Set.uIcc_comm] using ha) hb
  have hag : (Set.uIcc (ρ a x) (ρ g x)).Finite := hab.subset (by
    intro y hy
    rw [Set.mem_uIcc] at hy ⊢
    have hga := hmono a g hg.1
    have hgb := hmono g b hg.2
    rcases hy with hy | hy
    · exact Or.inl ⟨hy.1, hy.2.trans hgb⟩
    · exact Or.inl ⟨hga.trans hy.1, hy.2.trans (hga.trans hgb)⟩)
  exact finite_uIcc_trans ha hag

/-- A crossing forces an infinite interval between its endpoints. -/
theorem crossing_interval_infinite {f g : X ≃o X} {u v w : X} (h : Crossing f g u v w) :
    (Set.uIcc u v).Infinite := by
  have hgu : u < g u := by
    by_contra hn
    have hle : g u ≤ u := le_of_not_gt hn
    have hpow : ∀ n : ℕ, (g ^ n) u ≤ u := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
          simpa only [pow_succ', RelIso.mul_apply] using (g.monotone ih).trans hle
    obtain ⟨N, M, hN, hM⟩ := h.crosses
    exact (h.left_lt_middle.trans hM).not_ge (hpow M)
  have hmono : StrictMono (fun n : ℕ => (g ^ n) u) := by
    apply strictMono_nat_of_lt_succ
    intro n
    simpa only [pow_succ, RelIso.mul_apply] using (g ^ n).strictMono hgu
  apply (Set.infinite_range_of_injective hmono.injective).mono
  rintro _ ⟨n, rfl⟩
  rw [Set.mem_uIcc]
  exact Or.inl ⟨by simpa using hmono.monotone (Nat.zero_le n), (h.left_bounded n).le⟩

/-- For a transitive action with a crossing, finite-interval motions cannot exhaust the group. -/
theorem finiteIntervalSubgroup_ne_top (ρ : G →* (X ≃o X)) (x : X)
    (htrans : Function.Surjective (fun g => ρ g x))
    (hcross : ∃ f g u v w, Crossing (ρ f) (ρ g) u v w) : finiteIntervalSubgroup ρ x ≠ ⊤ := by
  intro he
  obtain ⟨f, g, u, v, w, h⟩ := hcross
  obtain ⟨a, ha⟩ := htrans u
  obtain ⟨b, hb⟩ := htrans v
  have hua : (Set.uIcc x (ρ a x)).Finite := by
    change a ∈ finiteIntervalSubgroup ρ x
    rw [he]; trivial
  have hub : (Set.uIcc x (ρ b x)).Finite := by
    change b ∈ finiteIntervalSubgroup ρ x
    rw [he]; trivial
  dsimp only at ha hb
  rw [ha] at hua
  rw [hb] at hub
  exact crossing_interval_infinite h (finite_uIcc_trans (by simpa only [Set.uIcc_comm] using hua) hub)


/-- A crossing and maximal convex point stabilizer force a dense orbit order. -/
theorem denselyOrdered_of_maximal_stabilizer (O : LeftGroupOrder G)
    (ρ : G →* (X ≃o X)) (x : X) (C : Subgroup G)
    (hstab : ∀ g, g ∈ C ↔ ρ g x = x)
    (hmono : ∀ a b, O.order.le a b → ρ a x ≤ ρ b x)
    (hmax : ∀ S : Subgroup G, (letI := O.order; Set.OrdConnected (S : Set G)) →
      C < S → S = ⊤)
    (htrans : Function.Surjective (fun g => ρ g x))
    (hcross : ∃ f g u v w, Crossing (ρ f) (ρ g) u v w) : DenselyOrdered X := by
  rw [denselyOrdered_iff_forall_not_covBy]
  intro u v huv
  let S := finiteIntervalSubgroup ρ x
  have hCS : C ≤ S := by
    intro g hg
    change (Set.uIcc x (ρ g x)).Finite
    rw [(hstab g).mp hg, Set.uIcc_self]
    exact Set.finite_singleton x
  obtain ⟨a, ha⟩ := htrans u
  obtain ⟨b, hb⟩ := htrans v
  dsimp only at ha hb
  have hab : x ⋖ ρ (a⁻¹ * b) x := by
    have hh := (apply_covBy_apply_iff (ρ a⁻¹)).mpr huv
    rw [← ha, ← hb] at hh
    simpa only [map_mul, map_inv, RelIso.mul_apply, RelIso.inv_apply_self] using hh
  have habS : a⁻¹ * b ∈ S := by
    change (Set.uIcc x (ρ (a⁻¹ * b) x)).Finite
    rw [Set.uIcc_of_le hab.le, hab.Icc_eq]
    exact Set.toFinite _
  have habC : a⁻¹ * b ∉ C := by
    intro hh
    exact hab.ne ((hstab _).mp hh).symm
  have hStop : S = ⊤ := hmax S (finiteIntervalSubgroup_convex O ρ x hmono)
    (lt_of_le_of_ne hCS (fun he => habC (he ▸ habS)))
  exact finiteIntervalSubgroup_ne_top ρ x htrans hcross hStop

/-- The ordered cosets in the nonnormal convex jump have no adjacent pair. -/
theorem coset_denselyOrdered (O : LeftGroupOrder G) (C : Subgroup G)
    (hC : letI := O.order; Set.OrdConnected (C : Set G)) (hne : C ≠ ⊤)
    (hmax : ∀ S : Subgroup G, (letI := O.order; Set.OrdConnected (S : Set G)) →
      C < S → S = ⊤) (hnormal : ¬ C.Normal) :
    letI := NoncofinalConvexJump.cosetLinearOrder O C hC
    DenselyOrdered (G ⧸ C) := by
  let := NoncofinalConvexJump.cosetLinearOrder O C hC
  apply denselyOrdered_of_maximal_stabilizer O
    (NoncofinalConvexJump.cosetAction O C hC) (QuotientGroup.mk 1) C
  · intro g
    exact (NoncofinalConvexJump.coset_base_fixed_iff O C hC g).symm
  · intro a b hab
    simp only [NoncofinalConvexJump.cosetAction_base]
    exact (NoncofinalConvexJump.coset_mk_le_mk O C hC a b).mpr (Or.inl hab)
  · exact hmax
  · intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨g, NoncofinalConvexJump.cosetAction_base O C hC g⟩
  · exact NoncofinalConvexJump.exists_crossing_of_maximal_convex_not_normal O C hC
      hne hmax hnormal

end FnZPositiveCones.NoncofinalDenseAction
