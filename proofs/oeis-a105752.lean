import OMAStatements.S_oeis_a105752
import Mathlib

/-!
# Proof of OEIS A105752 conjecture

Credit: @xor2k

With R n x = Sum_k c(n,k) x^k (unsigned Stirling numbers), R (n+1) x = (x+n) R n x, so
R n 1 = n! and R n (-1) = 0 for n >= 2; the even-index sum is (R n 1 + R n (-1))/2.
-/

namespace A105752Proof

open OMA.S_oeis_a105752

/-- Rising-factorial polynomial evaluated at x. -/
def R (n : ℕ) (x : ℤ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), (Nat.stirlingFirst n k : ℤ) * x ^ k

lemma R_ext (n m : ℕ) (x : ℤ) :
    ∑ k ∈ Finset.range (n + 1 + m), (Nat.stirlingFirst n k : ℤ) * x ^ k = R n x := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [← add_assoc, Finset.sum_range_succ, ih,
      Nat.stirlingFirst_eq_zero_of_lt (by omega)]
    simp

lemma R_succ (n : ℕ) (x : ℤ) : R (n + 1) x = (x + n) * R n x := by
  have h1 : ∑ k ∈ Finset.range (n + 1), (Nat.stirlingFirst n (k + 1) : ℤ) * x ^ (k + 1)
      = R n x - (Nat.stirlingFirst n 0 : ℤ) := by
    have := R_ext n 1 x
    rw [Finset.sum_range_succ'] at this
    simp only [pow_zero, mul_one] at this
    rw [← this]; ring
  have h0 : (n : ℤ) * (Nat.stirlingFirst n 0 : ℤ) = 0 := by
    cases n with
    | zero => simp
    | succ n => simp [Nat.stirlingFirst_succ_zero]
  unfold R
  rw [Finset.sum_range_succ']
  simp only [Nat.stirlingFirst_succ_succ, Nat.stirlingFirst_succ_zero, Nat.cast_add,
    Nat.cast_mul, add_mul, Finset.sum_add_distrib, Nat.cast_zero, zero_mul, add_zero]
  have h2 : ∑ k ∈ Finset.range (n + 1), (n : ℤ) * (Nat.stirlingFirst n (k + 1) : ℤ) * x ^ (k + 1)
      = n * (R n x - (Nat.stirlingFirst n 0 : ℤ)) := by
    rw [← h1, Finset.mul_sum]; congr 1; ext k; ring
  have h3 : ∑ k ∈ Finset.range (n + 1), (Nat.stirlingFirst n k : ℤ) * x ^ (k + 1)
      = x * R n x := by
    unfold R; rw [Finset.mul_sum]; congr 1; ext k; ring
  rw [h2, h3]; unfold R; linear_combination -h0

lemma R_one (n : ℕ) : R n 1 = n.factorial := by
  induction n with
  | zero => simp [R]
  | succ n ih => rw [R_succ, ih, Nat.factorial_succ]; push_cast; ring

lemma R_neg_one (n : ℕ) (hn : 2 ≤ n) : R n (-1) = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  induction m with
  | zero => rw [R_succ]; simp
  | succ m ih => rw [show m + 1 + 2 = m + 2 + 1 by ring, R_succ, ih (by omega)]; ring

lemma sum_two_mul (f : ℕ → ℤ) (m : ℕ) :
    ∑ k ∈ Finset.range (2 * m), f k = ∑ j ∈ Finset.range m, (f (2 * j) + f (2 * j + 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      ih, Finset.sum_range_succ]; ring

lemma even_sum (n : ℕ) :
    2 * ∑ j ∈ Finset.range (n + 1), (Nat.stirlingFirst n (2 * j) : ℤ) = R n 1 + R n (-1) := by
  rw [← R_ext n (n + 1) 1, ← R_ext n (n + 1) (-1), ← Finset.sum_add_distrib,
    show n + 1 + (n + 1) = 2 * (n + 1) by ring, sum_two_mul, Finset.mul_sum]
  congr 1; ext j
  simp only [one_pow, mul_one, pow_succ, pow_mul]
  norm_num; ring

lemma term (n j : ℕ) :
    stirling1 n (2 * j) = (-1) ^ n * (Nat.stirlingFirst n (2 * j) : ℤ) := by
  unfold stirling1
  by_cases h : 2 * j ≤ n
  · congr 1
    obtain ⟨d, rfl⟩ : ∃ d, n = 2 * j + d := ⟨n - 2 * j, by omega⟩
    rw [show 2 * j + d - 2 * j = d by omega, pow_add, pow_mul]; norm_num
  · rw [Nat.stirlingFirst_eq_zero_of_lt (by omega)]; simp

end A105752Proof

open A105752Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a105752.main := by
  intro n
  simp only [term]
  rw [← Finset.mul_sum]
  have he := even_sum n
  rw [R_one] at he
  unfold OMA.S_oeis_a105752.a
  rcases (show n = 0 ∨ n = 1 ∨ 2 ≤ n by omega) with h | h | h
  · subst h; decide
  · subst h; decide
  · rw [R_neg_one n h, add_zero] at he
    rw [if_neg (by omega), zero_add, ← he]
    rw [show (2 * ∑ j ∈ Finset.range (n + 1), (Nat.stirlingFirst n (2 * j) : ℤ)) * (-1) ^ n
      = 2 * ((-1) ^ n * ∑ j ∈ Finset.range (n + 1), (Nat.stirlingFirst n (2 * j) : ℤ)) by ring]
    exact Int.mul_ediv_cancel_left _ (by norm_num)
