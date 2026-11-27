import OMAStatements.S_oeis_a193656
import Mathlib

/-!
For a polynomial `p` with coefficients `c j` (of `x^j`) and degree `n ≥ 1`, the downstep is
`D(p) = c 0 + Σ_{j=1..n} c j * (1 + x + ... + x^(j-1))`, so `D(p)(0) = p(1)` and
`D(p)(2) = p(2) - p(1) + p(0)`. Hence `p(2) + p(0)` is invariant under `D`, the degree drops by
one at each step, and the residue `r` (a constant) satisfies `2 r = p(2) + p(0)`.
For row `n`, `p(2) = Σ 5^k 4^(n-k) = 5^(n+1) - 4^(n+1)` and `p(0) = 5^n`, which gives
`a(n) = 3*5^n - 2*4^n`, and the g.f. follows coefficientwise.
-/

namespace R193656
open OMA.S_oeis_a193656 Polynomial

theorem natDegree_q_le (k : ℕ) : (q k).natDegree ≤ k := by
  unfold q
  apply natDegree_sum_le_of_forall_le
  intro j _
  exact (natDegree_X_pow_le _).trans (Nat.sub_le _ _)

theorem eval_q_zero (k : ℕ) : (q k).eval 0 = 1 := by
  unfold q
  rw [eval_finset_sum, Finset.sum_range_succ, Finset.sum_eq_zero]
  · simp
  · intro j hj
    rw [Finset.mem_range] at hj
    rw [eval_pow, eval_X, zero_pow (by omega)]

theorem geom_aux (k : ℕ) : ∑ j ∈ Finset.range (k + 1), (2 : ℤ) ^ (k - j) = 2 ^ (k + 1) - 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ']
    simp only [Nat.add_sub_add_right, Nat.sub_zero, ih]
    ring

theorem eval_q_two (k : ℕ) : (q k).eval 2 = 2 ^ (k + 1) - 1 := by
  unfold q
  rw [eval_finset_sum]
  simp only [eval_pow, eval_X]
  exact geom_aux k

theorem key_sum (c : ℕ → ℤ) (n : ℕ) :
    (∑ i ∈ Finset.range n, c (n - i) * (2 ^ (n - 1 - i + 1) - 1) + c 0) +
      (∑ i ∈ Finset.range n, c (n - i) * 1 + c 0) =
    ∑ i ∈ Finset.range (n + 1), c i * 2 ^ i + ∑ i ∈ Finset.range (n + 1), c i * 0 ^ i := by
  have h1 : ∑ i ∈ Finset.range n, c (n - i) * (2 ^ (n - 1 - i + 1) - 1) +
      ∑ i ∈ Finset.range n, c (n - i) * 1 =
      ∑ i ∈ Finset.range n, c (n - 1 - i + 1) * 2 ^ (n - 1 - i + 1) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    have e : n - 1 - i + 1 = n - i := by omega
    rw [e]
    ring
  rw [Finset.sum_range_reflect (fun j => c (j + 1) * 2 ^ (j + 1)) n] at h1
  have h2 : ∑ i ∈ Finset.range n, c (i + 1) * (0 : ℤ) ^ (i + 1) = 0 := by simp
  rw [Finset.sum_range_succ' (fun i => c i * 2 ^ i), Finset.sum_range_succ' (fun i => c i * 0 ^ i),
    h2]
  simp only [pow_zero, mul_one] at h1 ⊢
  linarith

theorem inv_down (p : ℤ[X]) : (down p).eval 2 + (down p).eval 0 = p.eval 2 + p.eval 0 := by
  unfold down
  split_ifs with h
  · rfl
  · rw [eval_eq_sum_range (p := p) 2, eval_eq_sum_range (p := p) 0]
    simp only [eval_add, eval_finset_sum, eval_mul, eval_C, eval_q_zero, eval_q_two]
    exact key_sum (fun i => p.coeff i) p.natDegree

theorem deg_down (p : ℤ[X]) : (down p).natDegree ≤ p.natDegree - 1 := by
  unfold down
  split_ifs with h
  · omega
  · apply natDegree_add_le_of_degree_le
    · apply natDegree_sum_le_of_forall_le
      intro i hi
      rw [Finset.mem_range] at hi
      exact (natDegree_C_mul_le _ _).trans ((natDegree_q_le _).trans (by omega))
    · rw [natDegree_C]
      omega

theorem deg_iter (k : ℕ) (p : ℤ[X]) : (down^[k] p).natDegree ≤ p.natDegree - k := by
  induction k generalizing p with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    exact (ih (down p)).trans (by have := deg_down p; omega)

theorem inv_iter (k : ℕ) (p : ℤ[X]) :
    (down^[k] p).eval 2 + (down^[k] p).eval 0 = p.eval 2 + p.eval 0 := by
  induction k generalizing p with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, ih, inv_down]

theorem residue_two (p : ℤ[X]) : 2 * residue p = p.eval 2 + p.eval 0 := by
  rw [← inv_iter p.natDegree p]
  have hd := deg_iter p.natDegree p
  rw [Nat.sub_self] at hd
  unfold residue
  rw [eq_C_of_natDegree_le_zero hd]
  simp only [eval_C, coeff_C_zero]
  ring

theorem eval2_P (n : ℕ) : (P n).eval 2 = 5 ^ (n + 1) - 4 ^ (n + 1) := by
  unfold P
  simp only [eval_finset_sum, eval_mul, eval_C, eval_pow, eval_X]
  have h := geom_sum₂_mul (5 : ℤ) 4 (n + 1)
  rw [show (5 : ℤ) - 4 = 1 by norm_num, mul_one] at h
  rw [← h]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  rw [show n + 1 - 1 - k = n - k by omega, show (4 : ℤ) = 2 * 2 by norm_num, mul_pow]
  ring

theorem eval0_P (n : ℕ) : (P n).eval 0 = 5 ^ n := by
  unfold P
  simp only [eval_finset_sum, eval_mul, eval_C, eval_pow, eval_X]
  rw [Finset.sum_range_succ, Finset.sum_eq_zero]
  · simp
  · intro k hk
    rw [Finset.mem_range] at hk
    rw [zero_pow (by omega), mul_zero]

theorem a_closed (n : ℕ) : a n = 3 * 5 ^ n - 2 * 4 ^ n := by
  have h := residue_two (P n)
  rw [eval2_P, eval0_P, pow_succ, pow_succ] at h
  unfold a
  linarith

end R193656

open OMA.S_oeis_a193656 R193656 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a193656.main := by
  refine ⟨a_closed, ?_⟩
  rw [show ((5 * X - 1) * (4 * X - 1) : PowerSeries ℤ) = C 20 * X ^ 2 - C 9 * X ^ 1 + 1 by
        simp only [map_ofNat]; ring,
      show (1 - 2 * X : PowerSeries ℤ) = 1 - C 2 * X ^ 1 by simp only [map_ofNat]; ring,
      show ∀ p : PowerSeries ℤ, p * (C 20 * X ^ 2 - C 9 * X ^ 1 + 1)
        = C 20 * (p * X ^ 2) - C 9 * (p * X ^ 1) + p from fun p => by ring]
  ext n
  simp only [map_sub, map_add, coeff_C_mul, coeff_mul_X_pow', coeff_X_pow, coeff_one, coeff_C,
    coeff_mk]
  match n with
  | 0 => norm_num [a_closed]
  | 1 => norm_num [a_closed]
  | n + 2 =>
    simp only [show 2 ≤ n + 2 by omega, show 1 ≤ n + 2 by omega, ↓reduceIte,
      show n + 2 - 2 = n by omega, show n + 2 - 1 = n + 1 by omega, show n + 2 ≠ 0 by omega,
      show n + 2 ≠ 1 by omega, show n + 1 ≠ 0 by omega, a_closed]
    ring
