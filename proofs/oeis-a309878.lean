import OMAStatements.S_oeis_a309878
import Mathlib

namespace A309878aux

open OMA.S_oeis_a309878 in
lemma b_succ (n : ℕ) : b (n + 1) = (((n : ℂ) + 1) + b n) * (1 + Complex.I) := rfl

open OMA.S_oeis_a309878 in
lemma b_closed (n : ℕ) :
    b n = -2 * Complex.I * (1 + Complex.I) ^ n + (-1 + Complex.I) * (n : ℂ) + 2 * Complex.I := by
  induction n with
  | zero => simp [b]
  | succ k ih =>
    rw [b_succ, ih]
    push_cast
    linear_combination ((k : ℂ) + 2) * Complex.I_sq

open OMA.S_oeis_a309878 in
lemma b_rec (m : ℕ) :
    b (m + 4) = 4 * b (m + 3) - 7 * b (m + 2) + 6 * b (m + 1) - 2 * b m := by
  rw [b_closed (m + 4), b_closed (m + 3), b_closed (m + 2), b_closed (m + 1), b_closed m]
  push_cast
  linear_combination (-2 * Complex.I * (1 + Complex.I) ^ m * Complex.I ^ 2) * Complex.I_sq

open OMA.S_oeis_a309878 in
lemma a_rec (m : ℕ) :
    a (m + 4) = 4 * a (m + 3) - 7 * a (m + 2) + 6 * a (m + 1) - 2 * a m := by
  have h := congrArg Complex.re (b_rec m)
  simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.re_ofNat,
    Complex.im_ofNat, zero_mul, sub_zero] at h
  unfold a
  linarith

open OMA.S_oeis_a309878 in
lemma a_closed (n : ℕ) : ((a n : ℝ) : ℂ) =
    Complex.I * ((1 - Complex.I) ^ n - (1 + Complex.I) ^ n + Complex.I * (n : ℂ)) := by
  unfold a
  rw [Complex.re_eq_add_conj, b_closed]
  simp only [map_add, map_mul, map_neg, map_pow, map_one, Complex.conj_I, Complex.conj_natCast,
    Complex.conj_ofNat]
  linear_combination (-(n : ℂ)) * Complex.I_sq

end A309878aux

theorem OMA.solution : type_of% @OMA.S_oeis_a309878.main := by
  refine ⟨?_, A309878aux.a_closed⟩
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  rw [show m + 4 - 1 = m + 3 by omega, show m + 4 - 2 = m + 2 by omega,
    show m + 4 - 3 = m + 1 by omega, show m + 4 - 4 = m by omega]
  exact A309878aux.a_rec m
