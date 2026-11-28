import OMAStatements.S_oeis_a192031
import Mathlib

-- Problem: oeis-a192031 (Barker's g.f. and recurrence for the helm graph Wiener polynomial rows)
-- Credit: @Aijy0264561
-- a is an explicit period-4 quasi-polynomial (quadratic in (n-6)/4) from n = 6 on: write n = 17 + r + 4q,
-- evaluate every a(n - j) on its residue class and check each polynomial identity (ring); the g.f.
-- identity follows coefficientwise from this recurrence and finitely many small coefficients.

namespace OMA.A192031proof

open OMA.S_oeis_a192031 PowerSeries

lemma a_gen (c q : ℕ) : a (6 + c + 4 * q) = row (4 + ((c / 4 + q : ℕ) : ℚ)) (c % 4) := by
  unfold a
  rw [if_neg (by omega), if_neg (by omega), show 6 + c + 4 * q - 6 = c + 4 * q by omega,
    Nat.add_mul_div_left _ _ (by norm_num), Nat.add_mul_mod_self_left]

/-- The recurrence in the form `∑ p_j a(n-j) = 0`, for `n ≥ 17`. -/
lemma rec0 (n : ℕ) (hn : 17 ≤ n) :
    a n - a (n-1) + a (n-2) - a (n-3) - 2*a (n-4) + 2*a (n-5) - 2*a (n-6) + 2*a (n-7) +
      a (n-8) - a (n-9) + a (n-10) - a (n-11) = 0 := by
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 4 ∧ n = 6 + (11 + r) + 4 * q :=
    ⟨(n - 17) / 4, (n - 17) % 4, Nat.mod_lt _ (by norm_num), by omega⟩
  have s : ∀ j, j ≤ 11 → 6 + (11 + r) + 4 * q - j = 6 + (11 + r - j) + 4 * q :=
    fun j hj => by omega
  rw [s 1 (by norm_num), s 2 (by norm_num), s 3 (by norm_num), s 4 (by norm_num),
    s 5 (by norm_num), s 6 (by norm_num), s 7 (by norm_num), s 8 (by norm_num),
    s 9 (by norm_num), s 10 (by norm_num), s 11 (by norm_num)]
  simp only [a_gen]
  interval_cases r <;> simp [row] <;> push_cast <;> ring

lemma denom_eq : ((1-X)^3 * (1+X)^2 * (1+X^2)^3 : PowerSeries ℚ) =
    1 - X + X^2 - X^3 - C 2 * X^4 + C 2 * X^5 - C 2 * X^6 + C 2 * X^7 + X^8 - X^9 +
      X^10 - X^11 := by
  rw [show (C (2 : ℚ) : PowerSeries ℚ) = 2 from map_ofNat C 2]
  ring

lemma numer_eq : (X^3 * (9 + 3*X^2 + 9*X^3 - 22*X^4 + 3*X^5 - 10*X^6 - 11*X^7 +
        16*X^8 + 2*X^9 + 6*X^10 + 3*X^11 - 3*X^12 - 3*X^13) : PowerSeries ℚ) =
    C 9 * X^3 + C 3 * X^5 + C 9 * X^6 - C 22 * X^7 + C 3 * X^8 - C 10 * X^9 - C 11 * X^10 +
      C 16 * X^11 + C 2 * X^12 + C 6 * X^13 + C 3 * X^14 - C 3 * X^15 - C 3 * X^16 := by
  simp only [map_ofNat]
  ring

lemma coeff_mul_X1 (φ : PowerSeries ℚ) (n : ℕ) :
    coeff n (φ * X) = if 1 ≤ n then coeff (n - 1) φ else 0 := by
  simpa using coeff_mul_X_pow' φ 1 n

theorem a192031 :
    mk a * ((1-X)^3 * (1+X)^2 * (1+X^2)^3) =
      X^3 * (9 + 3*X^2 + 9*X^3 - 22*X^4 + 3*X^5 - 10*X^6 - 11*X^7 +
        16*X^8 + 2*X^9 + 6*X^10 + 3*X^11 - 3*X^12 - 3*X^13) ∧
    ∀ n : ℕ, 16 < n →
      a n = a (n-1) - a (n-2) + a (n-3) + 2*a (n-4) - 2*a (n-5) +
        2*a (n-6) - 2*a (n-7) - a (n-8) + a (n-9) - a (n-10) + a (n-11) := by
  refine ⟨?_, fun n hn => by linarith [rec0 n (by omega)]⟩
  rw [denom_eq, numer_eq]
  ext n
  simp only [mul_sub, mul_add, mul_one, map_sub, map_add, mul_left_comm (mk a) (C _),
    coeff_C_mul, coeff_mul_X_pow', coeff_mul_X1, coeff_mk, coeff_C]
  rcases Nat.lt_or_ge n 17 with h | h
  · interval_cases n <;> simp [a, row] <;> norm_num
  · have := rec0 n h
    have l : ∀ j, j ≤ 16 → ¬ n ≤ j := fun j hj => by omega
    simp only [show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega,
      show 4 ≤ n by omega, show 5 ≤ n by omega, show 6 ≤ n by omega, show 7 ≤ n by omega,
      show 8 ≤ n by omega, show 9 ≤ n by omega, show 10 ≤ n by omega, show 11 ≤ n by omega,
      show 12 ≤ n by omega, show 13 ≤ n by omega, show 14 ≤ n by omega,
      show 15 ≤ n by omega, show 16 ≤ n by omega, if_true, Nat.sub_eq_zero_iff_le,
      l 3 (by norm_num), l 5 (by norm_num), l 6 (by norm_num), l 7 (by norm_num),
      l 8 (by norm_num), l 9 (by norm_num), l 10 (by norm_num), l 11 (by norm_num),
      l 12 (by norm_num), l 13 (by norm_num), l 14 (by norm_num), l 15 (by norm_num),
      l 16 (by norm_num), if_false]
    linarith

end OMA.A192031proof

theorem OMA.solution : type_of% @OMA.S_oeis_a192031.main := OMA.A192031proof.a192031
