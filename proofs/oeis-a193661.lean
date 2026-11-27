import OMAStatements.S_oeis_a193661
import Mathlib

/-!
For a polynomial `p` with coefficients `c j` (of `x^j`) and degree `n ≥ 1`, the downstep is
`D(p) = c 0 + Σ_{j=1..n} c j * (1 + x + ... + x^(j-1))`, so `D(p)(0) = p(1)` and
`D(p)(2) = p(2) - p(1) + p(0)`. Hence `p(2) + p(0)` is invariant under `D`, the degree drops by
one at each step, and the residue `r` (a constant) satisfies `2 r = p(2) + p(0)`.
Row `n` of A193673 is `((1+3x)^n + (1+x)^n)/2` read from `x^0` up, so `p(2) = (7^n + 3^n)/2` and
`p(0) = 1`, which gives `4 a(n) = 7^n + 3^n + 2`; the g.f. follows coefficientwise.
-/

namespace R193661
open OMA.S_oeis_a193661 Polynomial

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

theorem T_two (n k : ℕ) : 2 * T n k = (n.choose k : ℤ) * (3 ^ (n - k) + 1) := by
  unfold T
  have h3 : (X + 3 : ℤ[X]) = X + C 3 := by simp
  have h1 : (X + 1 : ℤ[X]) = X + C 1 := by simp
  rw [h3, h1, coeff_add, coeff_X_add_C_pow, coeff_X_add_C_pow, one_pow]
  have hd : (2 : ℤ) ∣ 3 ^ (n - k) * (n.choose k : ℤ) + 1 * (n.choose k : ℤ) := by
    have ho : Odd (3 : ℤ) := ⟨1, by norm_num⟩
    have he : Even ((3 : ℤ) ^ (n - k) + 1) := ho.pow.add_one
    obtain ⟨r, hr⟩ := he
    exact ⟨r * n.choose k, by linear_combination (n.choose k : ℤ) * hr⟩
  rw [Int.mul_ediv_cancel' hd]
  ring

theorem eval2_P (n : ℕ) : 2 * (P n).eval 2 = 7 ^ n + 3 ^ n := by
  unfold P
  simp only [eval_finset_sum, eval_mul, eval_C, eval_pow, eval_X]
  rw [Finset.mul_sum]
  have h7 := add_pow (1 : ℤ) 6 n
  have h3 := add_pow (1 : ℤ) 2 n
  rw [show (1 : ℤ) + 6 = 7 by norm_num] at h7
  rw [show (1 : ℤ) + 2 = 3 by norm_num] at h3
  rw [h7, h3, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [← mul_assoc, T_two, show (6 : ℤ) = 3 * 2 by norm_num, mul_pow]
  ring

theorem eval0_P (n : ℕ) : (P n).eval 0 = 1 := by
  unfold P
  simp only [eval_finset_sum, eval_mul, eval_C, eval_pow, eval_X]
  rw [Finset.sum_range_succ, Finset.sum_eq_zero]
  · have h := T_two n n
    simp only [Nat.choose_self, Nat.sub_self, pow_zero, Nat.cast_one] at h
    simp only [Nat.sub_self, pow_zero, mul_one, zero_add]
    linarith
  · intro k hk
    rw [Finset.mem_range] at hk
    rw [zero_pow (by omega), mul_zero]

theorem a_closed (n : ℕ) : 4 * a n = 7 ^ n + 3 ^ n + 2 := by
  have h := residue_two (P n)
  have h2 := eval2_P n
  rw [eval0_P] at h
  unfold a
  linarith

end R193661

open OMA.S_oeis_a193661 R193661 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a193661.main := by
  have e0 : a 0 = 1 := by have := a_closed 0; norm_num at this; linarith
  have e1 : a 1 = 3 := by have := a_closed 1; norm_num at this; linarith
  have e2 : a 2 = 15 := by have := a_closed 2; norm_num at this; linarith
  rw [show ((X - 1) * (3 * X - 1) * (7 * X - 1) : PowerSeries ℤ)
        = C 21 * X ^ 3 - C 31 * X ^ 2 + C 11 * X ^ 1 - 1 by simp only [map_ofNat]; ring,
      show (-1 + 8 * X - 13 * X ^ 2 : PowerSeries ℤ) = C 8 * X ^ 1 - C 13 * X ^ 2 - 1 by
        simp only [map_ofNat]; ring,
      show ∀ p : PowerSeries ℤ, p * (C 21 * X ^ 3 - C 31 * X ^ 2 + C 11 * X ^ 1 - 1)
        = C 21 * (p * X ^ 3) - C 31 * (p * X ^ 2) + C 11 * (p * X ^ 1) - p from fun p => by ring]
  ext n
  simp only [map_sub, map_add, coeff_C_mul, coeff_mul_X_pow', coeff_X_pow, coeff_one, coeff_C,
    coeff_mk]
  match n with
  | 0 => norm_num [e0]
  | 1 => norm_num [e0, e1]
  | 2 => norm_num [e0, e1, e2]
  | n + 3 =>
    have h0 := a_closed n
    have h1 := a_closed (n + 1)
    have h2 := a_closed (n + 2)
    have h3 := a_closed (n + 3)
    have key : 4 * (21 * a n - 31 * a (n + 1) + 11 * a (n + 2) - a (n + 3)) = 0 := by
      linear_combination 21 * h0 - 31 * h1 + 11 * h2 - h3
    simp only [show 3 ≤ n + 3 by omega, show 2 ≤ n + 3 by omega, show 1 ≤ n + 3 by omega,
      ↓reduceIte, show n + 3 - 3 = n by omega, show n + 3 - 2 = n + 1 by omega,
      show n + 3 - 1 = n + 2 by omega, show n + 3 ≠ 0 by omega, show n + 3 ≠ 1 by omega,
      show n + 3 ≠ 2 by omega, show n + 2 ≠ 0 by omega, show n + 1 ≠ 0 by omega]
    linarith
