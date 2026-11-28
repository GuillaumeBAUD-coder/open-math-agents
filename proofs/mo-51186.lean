import OMAStatements.S_mo_51186
import Mathlib

/-!
# A negative coefficient hidden by Gaussian factors

Take the sequence supported at zero and one, with values X and 1−X+X².
Multiplying the latter polynomial by 1+X gives 1+X³.
More generally its product with the Gaussian integer of length m≥2
equals one plus X² times the Gaussian integer of length m−2 plus X^(m+1).
These expressions have nonnegative coefficients, although the original linear coefficient is negative.
-/

namespace OMA.S_mo_51186

open Polynomial

/-- A polynomial with negative linear coefficient. -/
noncomputable def B : ℝ[X] := 1 - X + X^2

/-- Only the first two entries contribute to the transform. -/
noncomputable def seq (s : ℕ) : ℝ[X] := if s = 0 then X else if s = 1 then B else 0

/-- The Gaussian coefficient of index zero is one. -/
lemma gzero (i : ℕ) : gauss i 0 = 1 := by cases i <;> simp [gauss]

/-- Recurrence for a Gaussian integer. -/
lemma gstep (i : ℕ) : gauss (i+1) 1 = 1 + X * gauss i 1 := by simp [gauss, gzero]

/-- The product with a Gaussian integer of length at least two. -/
lemma product_form (m : ℕ) :
    B * gauss (m+2) 1 = 1 + X^2 * gauss m 1 + X^(m+3) := by
  induction m with
  | zero => simp [gauss, B]; ring
  | succ m ih =>
    rw [gstep (m+2), mul_add, mul_one, mul_left_comm B, ih, gstep m, pow_succ X (m+3)]
    unfold B
    ring

/-- Nonnegative coefficients are closed under addition. -/
lemma add_pos {p q : ℝ[X]} (hp : CoeffNonneg p) (hq : CoeffNonneg q) : CoeffNonneg (p+q) :=
  fun k => by rw [coeff_add]; exact add_nonneg (hp k) (hq k)

/-- Nonnegative coefficients are closed under multiplication. -/
lemma mul_pos {p q : ℝ[X]} (hp : CoeffNonneg p) (hq : CoeffNonneg q) : CoeffNonneg (p*q) :=
  fun k => by rw [coeff_mul]; exact Finset.sum_nonneg fun i _ => mul_nonneg (hp _) (hq _)

/-- Every monomial with unit coefficient is nonnegative. -/
lemma mon_pos (d : ℕ) : CoeffNonneg (X^d) := fun k => by simp [coeff_X_pow]; positivity

/-- Gaussian integers have nonnegative coefficients. -/
lemma gp (i : ℕ) : CoeffNonneg (gauss i 1) := by
  induction i with
  | zero => intro k; simp [gauss]
  | succ i ih =>
    rw [gstep]
    exact add_pos (by simpa using mon_pos 0) (mul_pos (by simpa using mon_pos 1) ih)

/-- Multiplication hides the negative coefficient for lengths at least two. -/
lemma bgp (m : ℕ) : CoeffNonneg (B * gauss (m+2) 1) := by
  rw [product_form]
  exact add_pos (add_pos (by simpa using mon_pos 0) (mul_pos (mon_pos 2) (gp m))) (mon_pos _)

/-- Evaluate the transform by separating its two supported indices. -/
lemma transform (i j : ℕ) :
    T seq i j = X + (if 0 < min i j then B * gauss i 1 * gauss j 1 else 0) := by
  unfold T
  rw [Finset.sum_range_succ']
  simp [seq, gzero, ite_mul, Finset.sum_ite_eq', add_comm]

end OMA.S_mo_51186

open Polynomial OMA.S_mo_51186 in
theorem OMA.solution : type_of% @OMA.S_mo_51186.main := by
  intro h
  have bad := (h seq).mpr (by
    intro i j
    rw [transform]
    have hx : CoeffNonneg X := by simpa using mon_pos 1
    split_ifs with hij
    · match i, j with
      | m+2, j => exact add_pos hx (mul_pos (bgp m) (gp j))
      | i, m+2 => rw [mul_right_comm B]; exact add_pos hx (mul_pos (bgp m) (gp i))
      | 0, j | i, 0 => simp at hij
      | 1, 1 =>
        have he : X + B * gauss 1 1 * gauss 1 1 = 1 + X^2 := by simp [gauss, B]; ring
        rw [he]
        exact add_pos (by simpa using mon_pos 0) (mon_pos 2)
    · simpa using hx) 1 1
  norm_num [seq, B, coeff_sub, coeff_add, coeff_X, coeff_X_pow, coeff_one] at bad
