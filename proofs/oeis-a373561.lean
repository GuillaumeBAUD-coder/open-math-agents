import OMAStatements.S_oeis_a373561
import Mathlib.Tactic

namespace QuadraticDivisorProof

open Finset OMA.S_oeis_a373561

/-- Each signed weight belongs to exactly one of the gcd classes from 1 through n. -/
private lemma one_class {n : ℕ} (hn : 0 < n) (w : ℤ) :
    (∑ k ∈ Icc 1 n, if Int.gcd w n = k then w else 0) = w := by
  have member : Int.gcd w n ∈ Icc 1 n := by
    change w.natAbs.gcd n ∈ Icc 1 n
    exact mem_Icc.mpr ⟨Nat.gcd_pos_of_pos_right _ hn, Nat.gcd_le_right _ hn⟩
  simp [member]

private lemma remove_classes {n : ℕ} (hn : 0 < n) :
    groupedSum n = ∑ z ∈ range n, ∑ y ∈ range n, ∑ x ∈ range n,
      weight (x+1) (y+1) (z+1) := by
  unfold groupedSum
  rw [sum_comm]
  refine sum_congr rfl fun z _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun y _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun x _ => ?_
  exact one_class hn _

/-- Summing the y² and −z² contributions over the same box cancels them. -/
private lemma collapse (n : ℕ) :
    groupedSum n = (n : ℤ)^2 * ∑ x ∈ range n, ((x : ℤ)+1)^2 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [groupedSum]
  rw [remove_classes hn]
  simp only [weight, Nat.cast_add, Nat.cast_one, sum_sub_distrib, sum_add_distrib,
    sum_const, card_range, nsmul_eq_mul]
  simp_rw [← mul_sum]
  ring

private lemma six_times_squares (n : ℕ) :
    6 * (∑ x ∈ range n, ((x : ℤ)+1)^2) = (n : ℤ)*(n+1)*(2*n+1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, mul_add, ih]
    push_cast
    ring

end QuadraticDivisorProof

open Finset QuadraticDivisorProof OMA.S_oeis_a373561 in
theorem OMA.solution : type_of% @OMA.S_oeis_a373561.main := by
  intro n
  have square_sum : (6 : ℚ) * ((∑ x ∈ range n, ((x : ℤ)+1)^2 : ℤ) : ℚ) =
      (n : ℚ)*(n+1)*(2*n+1) := by exact_mod_cast six_times_squares n
  rw [collapse]
  push_cast at square_sum ⊢
  linear_combination -(n : ℚ)^2 / 6 * square_sum
