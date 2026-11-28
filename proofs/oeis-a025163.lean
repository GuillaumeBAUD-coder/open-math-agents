import OMAStatements.S_oeis_a025163
import Mathlib

/-!
# A025163: recurrence for the order one associated Legendre values at 2^(-1/2)

After removing the powers of two the claim is the polynomial identity
`(k+1) P_{k+2}' - (2k+3) X P_{k+1}' + (k+2) P_k' = 0`, proved pointwise by a joint
induction from the Bonnet recurrence.
-/

namespace OMA.A025163

open Polynomial OMA.S_oeis_a025163

/-- value of the Legendre polynomial -/
noncomputable def p (n : ℕ) (x : ℝ) : ℝ := (legendrePoly n).eval x

/-- value of the derivative of the Legendre polynomial -/
noncomputable def d (n : ℕ) (x : ℝ) : ℝ := (derivative (legendrePoly n)).eval x

theorem p_succ (n : ℕ) (x : ℝ) :
    ((n : ℝ) + 2) * p (n + 2) x = (2 * (n : ℝ) + 3) * (x * p (n + 1) x) - ((n : ℝ) + 1) * p n x := by
  have h : ((n : ℝ) + 2) ≠ 0 := by positivity
  simp only [p, legendrePoly, eval_sub, eval_smul, eval_mul, eval_X, smul_eq_mul]
  field_simp

theorem d_succ (n : ℕ) (x : ℝ) :
    ((n : ℝ) + 2) * d (n + 2) x =
      (2 * (n : ℝ) + 3) * (p (n + 1) x + x * d (n + 1) x) - ((n : ℝ) + 1) * d n x := by
  have h : ((n : ℝ) + 2) ≠ 0 := by positivity
  simp only [p, d, legendrePoly, derivative_sub, derivative_smul, derivative_mul, derivative_X,
    eval_sub, eval_smul, eval_mul, eval_add, eval_X, eval_one, smul_eq_mul, one_mul]
  field_simp

theorem key (x : ℝ) (n : ℕ) :
    d (n + 1) x = x * d n x + ((n : ℝ) + 1) * p n x ∧
    x * d (n + 1) x - d n x = ((n : ℝ) + 1) * p (n + 1) x ∧
    (x ^ 2 - 1) * d (n + 1) x = ((n : ℝ) + 1) * (x * p (n + 1) x - p n x) := by
  induction n with
  | zero =>
    simp [p, d, legendrePoly]
    ring
  | succ n ih =>
    obtain ⟨hA, hB, hE⟩ := ih
    have hp := p_succ n x
    have hd := d_succ n x
    have h : ((n : ℝ) + 2) ≠ 0 := by positivity
    have hA' : d (n + 2) x = x * d (n + 1) x + ((n : ℝ) + 2) * p (n + 1) x := by
      apply mul_left_cancel₀ h
      linear_combination hd + ((n : ℝ) + 1) * hB
    have e : (((n + 1 : ℕ) : ℝ)) = (n : ℝ) + 1 := by push_cast; ring
    rw [show n + 1 + 1 = n + 2 from rfl, e]
    refine ⟨by linear_combination hA', ?_, ?_⟩
    · linear_combination x * hA' + hE - hp
    · linear_combination (x ^ 2 - 1) * hA' + x * hE - x * hp

theorem poly_id (x : ℝ) (k : ℕ) :
    ((k : ℝ) + 1) * d (k + 2) x - (2 * (k : ℝ) + 3) * x * d (k + 1) x
      + ((k : ℝ) + 2) * d k x = 0 := by
  obtain ⟨hA, -, -⟩ := key x (k + 1)
  obtain ⟨-, hB, -⟩ := key x k
  have e : (((k + 1 : ℕ) : ℝ)) = (k : ℝ) + 1 := by push_cast; ring
  rw [show k + 1 + 1 = k + 2 from rfl, e] at hA
  linear_combination ((k : ℝ) + 1) * hA - ((k : ℝ) + 2) * hB

end OMA.A025163

open OMA.A025163 in
theorem OMA.solution : type_of% @OMA.S_oeis_a025163.main := by
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [show 2 + k - 1 = k + 1 by omega, show 2 + k - 2 = k by omega, show 2 + k = k + 2 by omega]
  have h2 : (0 : ℝ) < 2 := by norm_num
  set c : ℝ := (2 : ℝ) ^ (-(1 / 2 : ℝ)) with hc
  set t : ℝ := (2 : ℝ) ^ ((3 * (k : ℝ)) / 2 - 1) with ht
  have hc2 : c * c = 1 / 2 := by
    rw [hc, ← Real.rpow_add h2]
    norm_num
  have e2 : (2 : ℝ) ^ ((3 * ((k + 2 : ℕ) : ℝ)) / 2 - 1) = t * 8 := by
    rw [ht, show (3 * ((k + 2 : ℕ) : ℝ)) / 2 - 1 = ((3 * (k : ℝ)) / 2 - 1) + (3 : ℕ) by
      push_cast; ring, Real.rpow_add h2, Real.rpow_natCast]
    norm_num
  have e1 : (2 : ℝ) ^ ((3 * ((k + 1 : ℕ) : ℝ)) / 2 - 1) = t * (4 * c) := by
    rw [ht, show (3 * ((k + 1 : ℕ) : ℝ)) / 2 - 1 = ((3 * (k : ℝ)) / 2 - 1) + (3 / 2 : ℝ) by
      push_cast; ring, Real.rpow_add h2]
    congr 1
    rw [show (3 / 2 : ℝ) = (2 : ℕ) + (-(1 / 2 : ℝ)) by norm_num, Real.rpow_add h2,
      Real.rpow_natCast]
    norm_num
    first | exact hc.symm | rfl | simp [hc]
  have hid := poly_id c k
  simp only [d] at hid
  simp only [OMA.S_oeis_a025163.a]
  rw [e2, e1]
  push_cast
  linear_combination (8 * t * c) * hid
