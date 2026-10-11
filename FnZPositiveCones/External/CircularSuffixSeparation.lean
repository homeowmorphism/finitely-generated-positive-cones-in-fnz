module

public import FnZPositiveCones.External.CircularDynamicsTraces

@[expose] public section

/-!
Closed-interval suffix avoidance in the separation argument.  The density
hypothesis is explicit: every nested mixed-head interval contains an orbit
word with any prescribed last letter.  No full-orbit adjacency is inferred
from adjacency in a finite collection of traces.
-/

namespace FnZPositiveCones.CircularDynamics
universe u
variable {ι : Type u}

/-- A nonempty suffix has the same last letter as its containing word. -/
theorem getLast?_eq_of_nonempty_suffix {α : Type*} {v w : List α}
    (hvw : v.IsSuffix w) (hv : v ≠ []) : w.getLast? = v.getLast? := by
  obtain ⟨p, rfl⟩ := hvw
  exact List.getLast?_append_of_ne_nil p hv

/-- The complete closed interval avoids every proper suffix of both labels. -/
def ClosedSuffixAvoiding (coordinate : List (ι × Bool) → ℝ)
    (a b : List (ι × Bool)) : Prop :=
  ∀ v, (v.IsSuffix a ∧ v ≠ a) ∨ (v.IsSuffix b ∧ v ≠ b) →
    coordinate v ∉ Set.Icc (coordinate a) (coordinate b)

/-- A shortest word with a prescribed last letter inside an interval has no
proper suffix anywhere in its closed interval, when that last letter differs
from those of the two endpoints. -/
theorem exists_lastLetter_minimal_interval
    (coordinate : List (ι × Bool) → ℝ)
    (hinj : ∀ v w, FreeGroup.IsReduced v → FreeGroup.IsReduced w →
      coordinate v = coordinate w → v = w)
    (a b : List (ι × Bool)) (ha : FreeGroup.IsReduced a) (hb : FreeGroup.IsReduced b)
    (hzero : coordinate [] ∉ Set.Icc (coordinate a) (coordinate b))
    (r : ι × Bool) (har : a.getLast? ≠ some r) (hbr : b.getLast? ≠ some r)
    (hex : ∃ w, FreeGroup.IsReduced w ∧ w.getLast? = some r ∧
      coordinate w ∈ Set.Ioo (coordinate a) (coordinate b)) :
    ∃ w, FreeGroup.IsReduced w ∧ w.getLast? = some r ∧
      coordinate w ∈ Set.Ioo (coordinate a) (coordinate b) ∧
      ∀ v, v.IsSuffix w → v ≠ w →
        coordinate v ∉ Set.Icc (coordinate a) (coordinate b) := by
  classical
  have hn : ∃ n : ℕ, ∃ w, w.length = n ∧ FreeGroup.IsReduced w ∧
      w.getLast? = some r ∧ coordinate w ∈ Set.Ioo (coordinate a) (coordinate b) := by
    obtain ⟨w, hw, hwr, hwab⟩ := hex
    exact ⟨w.length, w, rfl, hw, hwr, hwab⟩
  obtain ⟨w, hlen, hw, hwr, hwab⟩ := Nat.find_spec hn
  refine ⟨w, hw, hwr, hwab, ?_⟩
  intro v hv hvw hvab
  have hvnil : v ≠ [] := by
    rintro rfl
    exact hzero hvab
  have hvr : v.getLast? = some r := (getLast?_eq_of_nonempty_suffix hv hvnil).symm.trans hwr
  have hvred : FreeGroup.IsReduced v := hw.suffix hv
  have hva : coordinate v ≠ coordinate a := by
    intro he
    exact har ((hinj v a hvred ha he) ▸ hvr)
  have hvb : coordinate v ≠ coordinate b := by
    intro he
    exact hbr ((hinj v b hvred hb he) ▸ hvr)
  have hvopen : coordinate v ∈ Set.Ioo (coordinate a) (coordinate b) :=
    ⟨lt_of_le_of_ne hvab.1 (Ne.symm hva), lt_of_le_of_ne hvab.2 hvb⟩
  have hmin : Nat.find hn ≤ v.length := Nat.find_min' hn ⟨v, rfl, hvred, hvr, hvopen⟩
  exact hvw (hv.eq_of_length_le (hlen ▸ hmin))

/-- Different last letters exclude the remaining endpoint coincidences after
the open interval has been cleared of suffixes. -/
theorem closedSuffixAvoiding_of_open_of_last_ne
    (coordinate : List (ι × Bool) → ℝ)
    (hinj : ∀ v w, FreeGroup.IsReduced v → FreeGroup.IsReduced w →
      coordinate v = coordinate w → v = w)
    (a b : List (ι × Bool)) (ha : FreeGroup.IsReduced a) (hb : FreeGroup.IsReduced b)
    (hzero : coordinate [] ∉ Set.Icc (coordinate a) (coordinate b))
    (hlast : a.getLast? ≠ b.getLast?)
    (hgap : ∀ v, v.IsSuffix a ∨ v.IsSuffix b →
      coordinate v ∉ Set.Ioo (coordinate a) (coordinate b)) :
    ClosedSuffixAvoiding coordinate a b := by
  intro v hv hvab
  have hvnil : v ≠ [] := by
    rintro rfl
    exact hzero hvab
  have hva : coordinate v ≠ coordinate a := by
    intro he
    rcases hv with ⟨hva, hne⟩ | ⟨hvb, _⟩
    · exact hne (hinj v a (ha.suffix hva) ha he)
    · have hve := hinj v a (hb.suffix hvb) ha he
      exact hlast (hve ▸ (getLast?_eq_of_nonempty_suffix hvb hvnil).symm)
  have hvb : coordinate v ≠ coordinate b := by
    intro he
    rcases hv with ⟨hva, _⟩ | ⟨hvb, hne⟩
    · have hve := hinj v b (ha.suffix hva) hb he
      exact hlast (hve ▸ getLast?_eq_of_nonempty_suffix hva hvnil)
    · exact hne (hinj v b (hb.suffix hvb) hb he)
  exact hgap v (hv.imp And.left And.left)
    ⟨lt_of_le_of_ne hvab.1 (Ne.symm hva), lt_of_le_of_ne hvab.2 hvb⟩

/-- Prescribed-last-letter density repairs finite trace adjacency into the
closed-interval avoidance required by the supported perturbation. -/
theorem exists_closed_suffix_avoiding_pair
    (coordinate : List (ι × Bool) → ℝ)
    (hinj : ∀ v w, FreeGroup.IsReduced v → FreeGroup.IsReduced w →
      coordinate v = coordinate w → v = w)
    (a b : List (ι × Bool)) (ha : FreeGroup.IsReduced a) (hb : FreeGroup.IsReduced b)
    (hab : coordinate a < coordinate b) (hhead : a.head? ≠ b.head?)
    (hzero : coordinate [] ∉ Set.Icc (coordinate a) (coordinate b))
    (hdense : ∀ u v, FreeGroup.IsReduced u → FreeGroup.IsReduced v →
      coordinate a ≤ coordinate u → coordinate u < coordinate v → coordinate v ≤ coordinate b →
      u.head? ≠ v.head? → ∀ r : ι × Bool,
      ∃ w, FreeGroup.IsReduced w ∧ w.getLast? = some r ∧
        coordinate w ∈ Set.Ioo (coordinate u) (coordinate v)) :
    ∃ u v, FreeGroup.IsReduced u ∧ FreeGroup.IsReduced v ∧
      coordinate a ≤ coordinate u ∧ coordinate u < coordinate v ∧ coordinate v ≤ coordinate b ∧
      u.head? ≠ v.head? ∧ ClosedSuffixAvoiding coordinate u v := by
  classical
  let S : Finset (List (ι × Bool)) := a.tails.toFinset ∪ b.tails.toFinset
  have hS (w : List (ι × Bool)) : w ∈ S ↔ w.IsSuffix a ∨ w.IsSuffix b := by
    simp only [S, Finset.mem_union, List.mem_toFinset, List.mem_tails]
  have hSred (w : List (ι × Bool)) (hw : w ∈ S) : FreeGroup.IsReduced w := by
    rcases (hS w).mp hw with hw | hw
    · exact ha.suffix hw
    · exact hb.suffix hw
  have haS : a ∈ S := (hS a).mpr (Or.inl ⟨[], rfl⟩)
  have hbS : b ∈ S := (hS b).mpr (Or.inr ⟨[], rfl⟩)
  obtain ⟨u, huS, v, hvS, hau, huv, hvb, hheads, hgap⟩ :=
    exists_adjacent_colored_labels S coordinate List.head?
      (fun x hx y hy he => hinj x y (hSred x hx) (hSred y hy) he) haS hbS hab hhead
  have hured := hSred u huS
  have hvred := hSred v hvS
  have hzero' : coordinate [] ∉ Set.Icc (coordinate u) (coordinate v) := by
    intro h
    exact hzero ⟨hau.trans h.1, h.2.trans hvb⟩
  have hgap' (w : List (ι × Bool)) (hw : w.IsSuffix u ∨ w.IsSuffix v) :
      coordinate w ∉ Set.Ioo (coordinate u) (coordinate v) := by
    apply hgap w
    apply (hS w).mpr
    rcases hw with hw | hw
    · exact ((hS u).mp huS).imp (hw.trans) (hw.trans)
    · exact ((hS v).mp hvS).imp (hw.trans) (hw.trans)
  by_cases hlast : u.getLast? = v.getLast?
  · have hunil : u ≠ [] := by
      rintro rfl
      exact hzero' ⟨le_rfl, huv.le⟩
    obtain ⟨r, hur⟩ := Option.ne_none_iff_exists'.mp
      (fun h => hunil (List.getLast?_eq_none_iff.mp h))
    let t : ι × Bool := (r.1, !r.2)
    have hrt : r ≠ t := by
      rintro he
      have hh := congrArg Prod.snd he
      change r.2 = !r.2 at hh
      cases h : r.2 <;> simp [h] at hh
    have hut : u.getLast? ≠ some t := by
      rw [hur]
      exact fun h => hrt (Option.some.inj h)
    have hvt : v.getLast? ≠ some t := by rw [← hlast]; exact hut
    obtain ⟨w, hwred, _, huw, hwavoid⟩ := exists_lastLetter_minimal_interval
      coordinate hinj u v hured hvred hzero' t hut hvt
      (hdense u v hured hvred hau huv hvb hheads t)
    by_cases hheads' : u.head? = w.head?
    · refine ⟨w, v, hwred, hvred, hau.trans huw.1.le, huw.2, hvb, ?_, ?_⟩
      · exact fun h => hheads (hheads'.trans h)
      · intro p hp hpwv
        rcases hp with ⟨hpw, hne⟩ | ⟨hpv, hne⟩
        · exact hwavoid p hpw hne ⟨huw.1.le.trans hpwv.1, hpwv.2⟩
        · have hpne : coordinate p ≠ coordinate v := by
            intro he
            exact hne (hinj p v (hvred.suffix hpv) hvred he)
          exact hgap' p (Or.inr hpv)
            ⟨huw.1.trans_le hpwv.1, lt_of_le_of_ne hpwv.2 hpne⟩
    · refine ⟨u, w, hured, hwred, hau, huw.1, huw.2.le.trans hvb, hheads', ?_⟩
      intro p hp hpuw
      rcases hp with ⟨hpu, hne⟩ | ⟨hpw, hne⟩
      · have hpne : coordinate p ≠ coordinate u := by
          intro he
          exact hne (hinj p u (hured.suffix hpu) hured he)
        exact hgap' p (Or.inl hpu)
          ⟨lt_of_le_of_ne hpuw.1 (Ne.symm hpne), hpuw.2.trans_lt huw.2⟩
      · exact hwavoid p hpw hne ⟨hpuw.1, hpuw.2.trans huw.2.le⟩
  · exact ⟨u, v, hured, hvred, hau, huv, hvb, hheads,
      closedSuffixAvoiding_of_open_of_last_ne coordinate hinj u v hured hvred hzero' hlast hgap'⟩

end FnZPositiveCones.CircularDynamics
