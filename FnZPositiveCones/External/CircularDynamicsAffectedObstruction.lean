module

public import FnZPositiveCones.External.CircularDynamicsObstruction
public import FnZPositiveCones.External.CircularDynamicsAffectedTrace

@[expose] public section

/-! Isolation obstructs even the weaker generator-sensitive local crossings. -/
namespace FnZPositiveCones
namespace CircularDynamics
universe u
variable {ι : Type u} (ρ : ι → Equiv.Perm StandardCircle)

/-- The generator-sensitive local crossing configuration. Protected sample words
retain complete traces, while the two comparison words protect only the points
affected by this signed generator. -/
structure AffectedCrossingConfig (W : Finset (List (ι × Bool))) where
  first : ι × Bool
  second : ι × Bool
  leftTail : List (ι × Bool)
  rightTail : List (ι × Bool)
  different : second ≠ first
  leftCoord : ℝ
  rightCoord : ℝ
  left_pos : 0 < leftCoord
  left_lt_right : leftCoord < rightCoord
  right_lt_one : rightCoord < 1
  left_value : evalWord ρ (first :: leftTail) 0 = (leftCoord : StandardCircle)
  right_value : evalWord ρ (second :: rightTail) 0 = (rightCoord : StandardCircle)
  avoids : ∀ y,
    y ∈ protectedTrace ρ W ∨ y ∈ affectedTrace ρ first 0 leftTail ∨ y ∈ affectedTrace ρ first 0 (second :: rightTail) →
    circleCoordinate y ∉ Set.Icc leftCoord rightCoord

/-- An admissible local crossing constructs a distinct completed circular order
while preserving every protected orbit word. The new action need not have a free orbit. -/
theorem affectedCrossingConfig_distinct_order
    (hρ : ∀ i, PreservesCircular (ρ i))
    (hx : Function.Injective (fun g => FreeGroup.lift ρ g (0 : StandardCircle)))
    (W : Finset (List (ι × Bool))) (K : AffectedCrossingConfig ρ W) :
    ∃ P : CircularGroupOrder (FreeGroup ι),
      P ≠ circularOrbitOrder (FreeGroup.lift ρ) (preservesCircular_lift ρ hρ) 0 hx ∧
      ∀ a ∈ W, ∀ b ∈ W, ∀ c ∈ W,
        P.order.sbtw (FreeGroup.mk a) (FreeGroup.mk b) (FreeGroup.mk c) ↔
          sbtw (evalWord ρ a 0) (evalWord ρ b 0) (evalWord ρ c 0) := by
  classical
  let F := protectedTrace ρ W ∪ (affectedTrace ρ K.first 0 K.leftTail).toFinset ∪
    (affectedTrace ρ K.first 0 (K.second :: K.rightTail)).toFinset
  let R := F.image circleCoordinate
  have hR : ∀ y ∈ R, y ∈ Set.Ico (0 : ℝ) 1 := by
    intro y hy
    obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hy
    exact circleCoordinate_mem z
  have havoid : ∀ y ∈ R, y ∉ Set.Icc K.leftCoord K.rightCoord := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
    apply K.avoids z
    simp only [F, Finset.mem_union, List.mem_toFinset] at hz
    tauto
  obtain ⟨h, c, hh, _, hbc, hc1, hac, hfix, _⟩ :=
    exists_circle_crossing_fixing_finset R K.leftCoord K.rightCoord 2 K.left_pos K.left_lt_right K.right_lt_one
      (by linarith [K.left_pos, K.right_lt_one]) hR havoid
  have hF : ∀ y ∈ F, h y = y := by
    intro y hy
    have he := hfix (circleCoordinate y) (Finset.mem_image.mpr ⟨y, hy, rfl⟩)
    simpa only [coe_circleCoordinate] using he
  have hw : ∀ y ∈ affectedTrace ρ K.first 0 K.leftTail, h y = y := by
    intro y hy
    exact hF y (Finset.mem_union_left _ (Finset.mem_union_right _ (List.mem_toFinset.mpr hy)))
  have hv : ∀ y ∈ affectedTrace ρ K.first 0 (K.second :: K.rightTail), h y = y := by
    intro y hy
    exact hF y (Finset.mem_union_right _ (List.mem_toFinset.mpr hy))
  let σ := FreeGroup.lift (perturb ρ K.first h)
  have hσ : ∀ g, PreservesCircular (σ g) :=
    preservesCircular_lift _ (preservesCircular_perturb ρ hρ K.first h hh)
  let O := circularOrbitOrder (FreeGroup.lift ρ) (preservesCircular_lift ρ hρ) 0 hx
  let L := freeGroupLeftOrderOfCircular O
  let P := completedCircularOrbitOrder σ hσ 0 L
  have hleft : σ (FreeGroup.mk (K.first :: K.leftTail)) 0 = (c : StandardCircle) := by
    change FreeGroup.lift (perturb ρ K.first h) (FreeGroup.mk (K.first :: K.leftTail)) 0 = _
    rw [lift_mk_apply, evalWord_perturb_head_of_affectedTrace_fixed ρ K.first h 0 K.leftTail hw, K.left_value, hac]
  have hright : σ (FreeGroup.mk (K.second :: K.rightTail)) 0 = (K.rightCoord : StandardCircle) := by
    change FreeGroup.lift (perturb ρ K.first h) (FreeGroup.mk (K.second :: K.rightTail)) 0 = _
    rw [lift_mk_apply, evalWord_perturb_of_affectedTrace_fixed ρ K.first h 0 (K.second :: K.rightTail) hv,
      K.right_value]
  have hcz : 0 < c := K.left_pos.trans (K.left_lt_right.trans hbc)
  have hrz : 0 < K.rightCoord := K.left_pos.trans K.left_lt_right
  have hne (a b : ℝ) (ha : a ∈ Set.Ico (0 : ℝ) 1) (hb : b ∈ Set.Ico (0 : ℝ) 1) (hab : a ≠ b) :
      (a : StandardCircle) ≠ (b : StandardCircle) := by
    intro he
    exact hab ((AddCircle.coe_eq_coe_iff_of_mem_Ico (a := (0 : ℝ)) (p := (1 : ℝ)) (by simpa using ha) (by simpa using hb)).mp he)
  have hPne : P ≠ O := by
    apply completedCircularOrbitOrder_ne_of_changed_sign σ hσ 0 L O
      (FreeGroup.mk (K.first :: K.leftTail)) (FreeGroup.mk (K.second :: K.rightTail)) 1
    · rw [hleft, hright]
      exact hne c K.rightCoord ⟨hcz.le, hc1⟩ ⟨hrz.le, K.right_lt_one⟩ (ne_of_gt hbc)
    · rw [hright, map_one, Equiv.Perm.one_apply]
      exact hne K.rightCoord 0 ⟨hrz.le, K.right_lt_one⟩ ⟨le_rfl, zero_lt_one⟩ (ne_of_gt hrz)
    · rw [hleft, map_one, Equiv.Perm.one_apply]
      exact hne 0 c ⟨le_rfl, zero_lt_one⟩ ⟨hcz.le, hc1⟩ (ne_of_lt hcz)
    · rw [hleft, hright, map_one, Equiv.Perm.one_apply]
      change ¬(sbtw (c : StandardCircle) (K.rightCoord : StandardCircle) 0 ↔
        sbtw (FreeGroup.lift ρ (FreeGroup.mk (K.first :: K.leftTail)) 0)
          (FreeGroup.lift ρ (FreeGroup.mk (K.second :: K.rightTail)) 0) (FreeGroup.lift ρ 1 0))
      rw [lift_mk_apply, lift_mk_apply, K.left_value, K.right_value, map_one, Equiv.Perm.one_apply,
        circle_sbtw_coe_zero_iff c K.rightCoord hcz hc1 hrz K.right_lt_one,
        circle_sbtw_coe_zero_iff K.leftCoord K.rightCoord K.left_pos (K.left_lt_right.trans K.right_lt_one) hrz K.right_lt_one]
      exact fun he => (not_lt_of_gt hbc) (he.mpr K.left_lt_right)
  refine ⟨P, hPne, ?_⟩
  have heval : ∀ w ∈ W, σ (FreeGroup.mk w) 0 = FreeGroup.lift ρ (FreeGroup.mk w) 0 := by
    intro w hw
    exact lift_mk_perturb_of_trace_fixed ρ K.first h 0 w (fun y hy =>
      hF y (Finset.mem_union_left _ (Finset.mem_union_left _ (mem_protectedTrace ρ W hw hy))))
  intro a ha b hb c hc
  have hab : FreeGroup.mk a ≠ FreeGroup.mk b → σ (FreeGroup.mk a) 0 ≠ σ (FreeGroup.mk b) 0 := by
    intro hn he
    rw [heval a ha, heval b hb] at he
    exact hn (hx he)
  have hbc : FreeGroup.mk b ≠ FreeGroup.mk c → σ (FreeGroup.mk b) 0 ≠ σ (FreeGroup.mk c) 0 := by
    intro hn he
    rw [heval b hb, heval c hc] at he
    exact hn (hx he)
  have hca : FreeGroup.mk c ≠ FreeGroup.mk a → σ (FreeGroup.mk c) 0 ≠ σ (FreeGroup.mk a) 0 := by
    intro hn he
    rw [heval c hc, heval a ha] at he
    exact hn (hx he)
  have hs : sbtw (σ (FreeGroup.mk a) 0) (σ (FreeGroup.mk b) 0) (σ (FreeGroup.mk c) 0) ↔
      O.order.sbtw (FreeGroup.mk a) (FreeGroup.mk b) (FreeGroup.mk c) := by
    rw [heval a ha, heval b hb, heval c hc]
    rfl
  exact (completedCircularOrbitOrder_sign_of_orbit_sign σ hσ 0 L O _ _ _ hab hbc hca hs).trans
    (by simp only [O, circularOrbitOrder_sbtw, lift_mk_apply])

/-- Every isolated free circular orbit has a finite set of protected trajectories
blocking all admissible local crossings. This is a proved consequence of isolation;
constructing crossings from overlapping initial-letter closures remains separate. -/
theorem isolated_has_finite_affected_crossing_obstruction
    (hρ : ∀ i, PreservesCircular (ρ i))
    (hx : Function.Injective (fun g => FreeGroup.lift ρ g (0 : StandardCircle)))
    (hiso : IsOpen ({circularOrbitOrder (FreeGroup.lift ρ) (preservesCircular_lift ρ hρ) 0 hx} :
      Set (CircularGroupOrder (FreeGroup ι)))) :
    ∃ W : Finset (List (ι × Bool)), ¬Nonempty (AffectedCrossingConfig ρ W) := by
  classical
  obtain ⟨F, hF⟩ := (circularOrder_isolated_iff_finite_signs _).mp hiso
  let W := F.image (fun p => p.1.toWord) ∪ F.image (fun p => p.2.1.toWord) ∪ F.image (fun p => p.2.2.toWord)
  refine ⟨W, ?_⟩
  rintro ⟨K⟩
  obtain ⟨P, hne, hP⟩ := affectedCrossingConfig_distinct_order ρ hρ hx W K
  apply hne
  apply hF
  intro p hp
  have ha : p.1.toWord ∈ W := Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨p, hp, rfl⟩))
  have hb : p.2.1.toWord ∈ W := Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨p, hp, rfl⟩))
  have hc : p.2.2.toWord ∈ W := Finset.mem_union_right _ (Finset.mem_image.mpr ⟨p, hp, rfl⟩)
  have he := hP p.1.toWord ha p.2.1.toWord hb p.2.2.toWord hc
  simpa only [FreeGroup.mk_toWord, ← lift_mk_apply, FreeGroup.mk_toWord,
    circularOrderSign, circularOrbitOrder_sbtw, decide_eq_decide] using he

end CircularDynamics
end FnZPositiveCones
