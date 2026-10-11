module

public import FnZPositiveCones.External.OddRank

@[expose] public section

/-!
# The finite parity calculation underlying the MMRT obstruction

This file checks the permutation calculation for the boundary of the orientable
surface used in MMRT, Theorem 1.3. It does not yet extract that finite data from
an isolated order, and therefore does not prove the odd-rank obstruction.
-/

namespace FnZPositiveCones
namespace MMRTParity

open Equiv

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- A permutation with no fixed points has full support. -/
theorem support_eq_univ_of_no_fixed (p : Perm D) (hp : ∀ d, p d ≠ d) :
    p.support = Finset.univ := by
  ext d
  simp [Perm.mem_support, hp]

/-- The gluing pairs an even number of edges, hence its dart involution is even. -/
theorem pairing_sign (pairing : Perm D) (hinvol : pairing ^ 2 = 1)
    (hfree : ∀ d, pairing d ≠ d) (K : ℕ) (hcard : Fintype.card D = 4 * K) :
    Perm.sign pairing = 1 := by
  have hs := support_eq_univ_of_no_fixed pairing hfree
  have hf : Fintype.card (Function.fixedPoints pairing) = 0 := by
    rw [Perm.card_fixedPoints, Perm.sum_cycleType, hs, Finset.card_univ, Nat.sub_self]
  rw [Perm.sign_of_pow_two_eq_one hinvol, hf, Nat.sub_zero, hcard]
  have he : 4 * K / 2 = 2 * K := by omega
  rw [he]
  exact (even_two_mul K).neg_one_pow

/-- A single boundary component on `4*K` darts has odd sign. -/
theorem boundary_sign (boundary : Perm D) (hcycle : boundary.IsCycle)
    (hfree : ∀ d, boundary d ≠ d) (K : ℕ) (hcard : Fintype.card D = 4 * K) :
    Perm.sign boundary = -1 := by
  rw [hcycle.sign, support_eq_univ_of_no_fixed boundary hfree, Finset.card_univ, hcard]
  have he : Even (4 * K) := ⟨2 * K, by omega⟩
  rw [he.neg_one_pow]

/--
The surface obtained from one base disc and `n` polygon discs cannot have a
single boundary component when `n` is odd. The rotation has one cycle per disc;
the edge gluing is a fixed-point-free involution on `4*K` darts.

The hypotheses are explicit finite combinatorial data, not hypotheses about
orders. Constructing this data from an isolated order remains separate work.
-/
theorem even_of_one_boundary (n K : ℕ) (rotation pairing : Perm D)
    (hcard : Fintype.card D = 4 * K)
    (hrotation : ∀ d, rotation d ≠ d)
    (hvertices : rotation.cycleType.card = n + 1)
    (hinvol : pairing ^ 2 = 1)
    (hpairing : ∀ d, pairing d ≠ d)
    (hboundary : (rotation * pairing).IsCycle)
    (hboundary_free : ∀ d, (rotation * pairing) d ≠ d) : Even n := by
  have hp := pairing_sign pairing hinvol hpairing K hcard
  have hb := boundary_sign (rotation * pairing) hboundary hboundary_free K hcard
  have hr : Perm.sign rotation = -1 := by simpa [map_mul, hp] using hb
  rw [Perm.sign_of_cycleType, Perm.sum_cycleType,
    support_eq_univ_of_no_fixed rotation hrotation, Finset.card_univ, hcard, hvertices] at hr
  have he : Even (4 * K) := ⟨2 * K, by omega⟩
  rw [pow_add, he.neg_one_pow, one_mul, pow_succ] at hr
  have hn : (-1 : ℤˣ) ^ n = 1 := by
    have h := congrArg (fun x : ℤˣ => x * (-1)) hr
    simpa [mul_assoc] using h
  by_contra hodd
  have ho : Odd n := Nat.not_even_iff_odd.mp hodd
  rw [ho.neg_one_pow] at hn
  norm_num at hn

end MMRTParity
end FnZPositiveCones
