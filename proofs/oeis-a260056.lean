import OMAStatements.S_oeis_a260056
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace OMA.S_oeis_a260056
open Polynomial

lemma col_diff (r n : ℕ) :
    ((fwdDiff (1 : ℕ))^[r+1] row) n =
      (1 + X + X^2 : ℤ[X])^(n+1) * (X*(1+X))^r := by
  induction r generalizing n with
  | zero =>
    simp [fwdDiff, row, Finset.sum_range_succ]
  | succ r ih =>
    rw [Function.iterate_succ_apply', fwdDiff, ih, ih, pow_succ (1+X+X^2), pow_succ (X*(1+X))]
    ring

lemma column (n k : ℕ) :
    ∑ m ∈ Finset.range (k + 3), (-1 : ℤ)^m * T (n+m) k * ((k+2).choose m : ℤ) = 0 := by
  have h := congrArg (Polynomial.lcoeff ℤ k) (col_diff (k+1) n)
  rw [fwdDiff_iter_eq_sum_shift] at h
  simp only [map_sum, Polynomial.lcoeff_apply, Polynomial.coeff_smul, nsmul_one] at h
  simp only [zsmul_eq_mul, Int.cast_id] at h
  have hr : ((1 + X + X ^ 2 : ℤ[X]) ^ (n + 1) * (X * (1 + X)) ^ (k + 1)).coeff k = 0 := by
    rw [mul_pow, mul_left_comm, Polynomial.coeff_X_pow_mul']
    simp
  rw [hr] at h
  simp only [Nat.cast_id, Nat.add_assoc, Nat.reduceAdd] at h
  calc
    _ = (-1 : ℤ)^(k+2) * (∑ m ∈ Finset.range (k + 3),
        ((-1 : ℤ)^(k+2-m) * ((k+2).choose m : ℤ)) * (row (n+m)).coeff k) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      have hm' : m ≤ k+2 := by simpa [Nat.lt_succ_iff] using hm
      have hsign : ((-1 : ℤ)^(k+2)) * (-1)^(k+2-m) = (-1)^m := by
        rw [← pow_add, show k + 2 + (k + 2 - m) = 2*(k+2-m)+m by omega, pow_add, pow_mul]
        norm_num
      unfold T
      rw [← hsign]
      ring
    _ = 0 := by rw [h, mul_zero]

end OMA.S_oeis_a260056

namespace OMA.S_oeis_a260056
open Polynomial

noncomputable def altD (P : ℕ → ℤ[X]) (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n+1), (-1 : ℤ)^k * (P (n-k)).coeff k

lemma altD_add (P Q : ℕ → ℤ[X]) (n : ℕ) :
    altD (fun i => P i + Q i) n = altD P n + altD Q n := by
  simp [altD, mul_add, Finset.sum_add_distrib]

lemma altD_one (n : ℕ) : altD (fun _ => 1) n = 1 := by
  simp [altD, Polynomial.coeff_one]

lemma altD_X (P : ℕ → ℤ[X]) (n : ℕ) :
    altD (fun i => P i * X) (n+1) = - altD P n := by
  unfold altD
  rw [Finset.sum_range_succ']
  simp only [coeff_mul_X_zero, mul_zero, add_zero, coeff_mul_X, Nat.succ_sub_succ_eq_sub,
    pow_succ, mul_neg_one, neg_mul, Finset.sum_neg_distrib]

lemma altD_row_succ (i : ℕ) : row (i+1) =
    (row i + row i * X + row i * X * X) + 1 := by
  unfold row
  rw [Finset.sum_range_succ']
  simp only [pow_succ, pow_zero]
  rw [← Finset.sum_mul]
  ring

lemma altD_step (n : ℕ) :
    altD row (n+3) = altD row (n+2) - altD row (n+1) + altD row n + 1 := by
  have hs : altD row (n+3) = altD (fun i => row (i+1)) (n+2) := by
    unfold altD
    rw [Finset.sum_range_succ]
    have : (row 0).coeff (n+3) = 0 := by simp [row, Polynomial.coeff_one]
    simp only [Nat.sub_self, this, mul_zero, add_zero]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' := Finset.mem_range.mp hk
    rw [show n + 3 - k = n + 2 - k + 1 by omega]
  rw [hs]
  simp_rw [altD_row_succ]
  rw [altD_add, altD_add, altD_add, altD_one, altD_X, altD_X, altD_X]
  ring

lemma alternating_diagonal_formula (n : ℕ) :
    (∑ k ∈ Finset.range (n+1), (-1 : ℤ)^k * T (n-k) k) =
      (((n+3)/4 + (n+4)/4 : ℕ) : ℤ) := by
  change altD row n = _
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 | 1 | 2 => norm_num [altD, row, Finset.sum_range_succ, pow_two, add_mul, mul_add,
        Polynomial.coeff_mul_X, Polynomial.coeff_X_mul, Polynomial.coeff_one, Polynomial.coeff_X]
    | n+3 =>
      rw [altD_step, ih (n+2) (by omega), ih (n+1) (by omega), ih n (by omega)]
      omega
end OMA.S_oeis_a260056

theorem OMA.solution : type_of% @OMA.S_oeis_a260056.main := by
  exact ⟨OMA.S_oeis_a260056.alternating_diagonal_formula, OMA.S_oeis_a260056.column⟩
