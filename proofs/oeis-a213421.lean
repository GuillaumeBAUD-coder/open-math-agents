import OMAStatements.S_oeis_a213421
import Mathlib

/-!
# OEIS A213421: the real part of `Q^n` for `Q = 2 + i + j + k`

`Q` has trace `4` and norm `7`, so `Q² = 4Q - 7`. Multiplying by `Q^n` and taking real parts,
`a(n+2) = 4 a(n+1) - 7 a(n)` with `a(0) = 1`, `a(1) = 2`.

* Comparing coefficients, this is exactly `(1 - 4x + 7x²) · ∑ a(n) xⁿ = 1 - 2x`.
* Let `R = 1/(1 - 4x + 7x²)`. Multiplying the identity above by `R` gives
  `∑ a(n) xⁿ = (1 - 2x) R`, and the coefficient of `xⁿ` (`n ≥ 1`) on the right is
  `A168175(n) - 2 A168175(n-1)`.
-/

open PowerSeries OMA.S_oeis_a213421

namespace OMA.A213421

/-- The coefficient of `xⁿ` in `c xⁱ φ`. -/
lemma coeff_term (c : ℤ) (i n : ℕ) (φ : ℤ⟦X⟧) :
    coeff n (((c : ℤ) : ℤ⟦X⟧) * X ^ i * φ) = if i ≤ n then c * coeff (n - i) φ else 0 := by
  rw [mul_assoc, ← eq_intCast (C : ℤ →+* ℤ⟦X⟧) c, coeff_C_mul, coeff_X_pow_mul']
  split_ifs <;> simp

/-- `Q² = 4Q - 7`. -/
lemma Q_sq : Q * Q = (4 : ℤ) • Q - (7 : ℤ) • (1 : Quaternion ℤ) := by
  ext <;> rfl

/-- The recurrence `a(n+2) = 4 a(n+1) - 7 a(n)`. -/
lemma a_rec (n : ℕ) : a (n + 2) = 4 * a (n + 1) - 7 * a n := by
  have h : Q ^ (n + 2) = (4 : ℤ) • Q ^ (n + 1) - (7 : ℤ) • Q ^ n := by
    rw [pow_add, pow_two, Q_sq, mul_sub, mul_smul_comm, mul_smul_comm, mul_one, pow_succ]
  unfold a
  rw [h, Quaternion.re_sub, Quaternion.re_smul, Quaternion.re_smul, smul_eq_mul, smul_eq_mul]

lemma a_zero : a 0 = 1 := by
  unfold a
  rw [pow_zero]
  rfl

lemma a_one : a 1 = 2 := by
  unfold a
  rw [pow_one]
  rfl

/-- The generating function identity. -/
lemma gf : (1 - 4 * X + 7 * X ^ 2 : ℤ⟦X⟧) * PowerSeries.mk a = 1 - 2 * X := by
  have e1 : (1 - 4 * X + 7 * X ^ 2 : ℤ⟦X⟧) * PowerSeries.mk a
      = ((1 : ℤ) : ℤ⟦X⟧) * X ^ 0 * PowerSeries.mk a
        + (((-4) : ℤ) : ℤ⟦X⟧) * X ^ 1 * PowerSeries.mk a
        + ((7 : ℤ) : ℤ⟦X⟧) * X ^ 2 * PowerSeries.mk a := by
    push_cast; ring
  have e2 : (1 - 2 * X : ℤ⟦X⟧)
      = ((1 : ℤ) : ℤ⟦X⟧) * X ^ 0 * 1 + (((-2) : ℤ) : ℤ⟦X⟧) * X ^ 1 * 1 := by
    push_cast; ring
  rw [e1, e2]
  ext n
  simp only [map_add, coeff_term, coeff_mk, coeff_one]
  rcases n with _ | _ | n
  · simp [a_zero]
  · simp [a_zero, a_one]
  · have h := a_rec n
    simp
    linarith

end OMA.A213421

open OMA.A213421 in
theorem OMA.solution : type_of% @OMA.S_oeis_a213421.main := by
  refine ⟨gf, fun n hn => ?_⟩
  -- `R = 1/(1 - 4x + 7x²)`
  obtain ⟨R, hR⟩ : ∃ R : ℤ⟦X⟧,
      R = PowerSeries.invOfUnit (1 - 4 * X + 7 * X ^ 2 : ℤ⟦X⟧) 1 := ⟨_, rfl⟩
  have hPR : (1 - 4 * X + 7 * X ^ 2 : ℤ⟦X⟧) * R = 1 := by
    rw [hR]
    exact PowerSeries.mul_invOfUnit _ _ (by simp)
  -- `∑ a(n) xⁿ = (1 - 2x) R`
  have hA : PowerSeries.mk a
      = ((1 : ℤ) : ℤ⟦X⟧) * X ^ 0 * R + (((-2) : ℤ) : ℤ⟦X⟧) * X ^ 1 * R := by
    linear_combination (norm := (push_cast; ring)) R * gf - PowerSeries.mk a * hPR
  have h := congrArg (coeff n) hA
  simp only [map_add, coeff_term, coeff_mk] at h
  rw [if_pos (Nat.zero_le n), if_pos hn] at h
  unfold A168175
  rw [← hR, h]
  simp
  ring
