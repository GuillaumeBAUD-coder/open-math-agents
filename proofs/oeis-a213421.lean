import OMAStatements.S_oeis_a213421
import Mathlib

/-!
# A213421: the real part of (2+i+j+k)^n has g.f. (1-2x)/(1-4x+7x^2)

Q = 2 + u with u = i + j + k, and u^2 = -3, so Q^2 = 4Q - 7 (checked by computation).
Hence Q^(n+2) = 4 Q^(n+1) - 7 Q^n, and taking real parts a(n+2) = 4 a(n+1) - 7 a(n) with
a(0) = 1, a(1) = 2. Comparing coefficients gives (1 - 4x + 7x^2) A(x) = 1 - 2x. Multiplying by
the inverse series B(x) = 1/(1 - 4x + 7x^2) gives A(x) = (1 - 2x) B(x), whose coefficient of x^n
is A168175(n) - 2*A168175(n-1) for n ≥ 1.
-/

namespace OMA.P213421

open OMA.S_oeis_a213421 PowerSeries

/-- Q^2 = 4Q - 7, by computation. -/
lemma Q_sq : Q ^ 2 = (4 : ℤ) • Q - (7 : ℤ) • (1 : Quaternion ℤ) := by rfl

/-- The linear recurrence a(n+2) = 4 a(n+1) - 7 a(n). -/
lemma a_rec (n : ℕ) : a (n + 2) = 4 * a (n + 1) - 7 * a n := by
  have h : Q ^ (n + 2) = (4 : ℤ) • Q ^ (n + 1) - (7 : ℤ) • Q ^ n := by
    rw [pow_add, Q_sq, mul_sub, mul_smul_comm, mul_smul_comm, mul_one, pow_succ]
  unfold a
  rw [h, Quaternion.re_sub, Quaternion.re_smul, Quaternion.re_smul, smul_eq_mul, smul_eq_mul]

lemma a_zero : a 0 = 1 := by rfl

lemma a_one : a 1 = 2 := by rfl

/-- The g.f. identity (1 - 4x + 7x^2) A(x) = 1 - 2x. -/
lemma gf : (1 - 4 * X + 7 * X ^ 2 : PowerSeries ℤ) * PowerSeries.mk a = 1 - 2 * X := by
  ext n
  have h4 : (4 : PowerSeries ℤ) = C 4 := (map_ofNat C 4).symm
  have h7 : (7 : PowerSeries ℤ) = C 7 := (map_ofNat C 7).symm
  have h2 : (2 : PowerSeries ℤ) = C 2 := (map_ofNat C 2).symm
  rw [h4, h7, h2, add_mul, sub_mul, one_mul, mul_assoc, mul_assoc, map_add, map_sub,
    coeff_C_mul, coeff_C_mul, map_sub, coeff_C_mul, coeff_mk]
  rcases n with _ | _ | n
  · simp [a_zero]
  · simp [a_zero, a_one, coeff_X_pow_mul', coeff_one, coeff_X]
  · rw [coeff_X_pow_mul', if_pos (by omega), coeff_succ_X_mul, coeff_mk, coeff_mk]
    simp [coeff_one, coeff_X, a_rec]

/-- The inverse series B(x) = 1/(1 - 4x + 7x^2). -/
noncomputable def B : PowerSeries ℤ := PowerSeries.invOfUnit (1 - 4 * X + 7 * X ^ 2) 1

lemma DB : (1 - 4 * X + 7 * X ^ 2 : PowerSeries ℤ) * B = 1 :=
  PowerSeries.mul_invOfUnit _ 1 (by simp)

/-- A(x) = (1 - 2x) B(x). -/
lemma A_eq : PowerSeries.mk a = (1 - 2 * X) * B := by
  calc PowerSeries.mk a = (B * (1 - 4 * X + 7 * X ^ 2)) * PowerSeries.mk a := by
        rw [mul_comm B, DB, one_mul]
    _ = B * (1 - 2 * X) := by rw [mul_assoc, gf]
    _ = (1 - 2 * X) * B := mul_comm _ _

theorem sol : type_of% @OMA.S_oeis_a213421.main := by
  refine ⟨gf, ?_⟩
  have hA := A_eq
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h2 : (2 : PowerSeries ℤ) = C 2 := (map_ofNat C 2).symm
  have e := congrArg (coeff (m + 1)) hA
  rw [coeff_mk, sub_mul, one_mul, h2, mul_assoc, map_sub, coeff_C_mul, coeff_succ_X_mul] at e
  rw [e]
  rfl

end OMA.P213421

theorem OMA.solution : type_of% @OMA.S_oeis_a213421.main := OMA.P213421.sol
