import OMAStatements.S_oeis_a057870
import Mathlib

-- Problem: oeis-a057870
-- Credit: @Aijy0264561
-- a is an explicit period-6 cubic quasi-polynomial: write n = 13 + r + 6q, evaluate every a(n - j) on its residue class and check each of the six polynomial identities (ring); the g.f. identity follows coefficientwise from this recurrence and finitely many small coefficients.

namespace OMA.A057870proof

open OMA.S_oeis_a057870 PowerSeries

/-- The six cubic pieces of `a`. -/
def F (r : ℕ) (d : ℚ) : ℚ :=
  (match r with
  | 0 => 5*d^3 - 13*d^2 + 12*d
  | 2 | 4 => 5*d^3 - 13*d^2 + 16*d - 8
  | 3 => 5*d^3 - 14*d^2 + 9*d
  | _ => 5*d^3 - 14*d^2 + 13*d - 4) / 12

lemma a_eq (n : ℕ) : a n = F (n % 6) (n : ℚ) := rfl

lemma a_add (c q : ℕ) : a (c + 6 * q) = F (c % 6) ((c + 6 * q : ℕ) : ℚ) := by
  rw [a_eq, Nat.add_mul_mod_self_left]

/-- The recurrence in the form `∑ p_j a(n-j) = 0`, for `n ≥ 13`. -/
lemma rec0 (n : ℕ) (hn : 13 ≤ n) :
    a n - 2*a (n-2) - a (n-3) + a (n-4) + 2*a (n-5) - a (n-6) - a (n-7) + 2*a (n-8) +
      a (n-9) - a (n-10) - 2*a (n-11) + a (n-13) = 0 := by
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 6 ∧ n = (13 + r) + 6 * q :=
    ⟨(n - 13) / 6, (n - 13) % 6, Nat.mod_lt _ (by norm_num), by omega⟩
  have s : ∀ j, j ≤ 13 → (13 + r) + 6 * q - j = (13 + r - j) + 6 * q := fun j hj => by omega
  rw [s 2 (by norm_num), s 3 (by norm_num), s 4 (by norm_num), s 5 (by norm_num),
    s 6 (by norm_num), s 7 (by norm_num), s 8 (by norm_num), s 9 (by norm_num),
    s 10 (by norm_num), s 11 (by norm_num), s 13 (by norm_num)]
  simp only [a_add]
  interval_cases r <;> simp [F] <;> push_cast <;> ring

lemma denom_eq : ((1-X)^4*(1+X)^3*(1-X+X^2)*(1+X+X^2)^2 : PowerSeries ℚ) =
    1 - C 2 * X^2 - X^3 + X^4 + C 2 * X^5 - X^6 - X^7 + C 2 * X^8 + X^9 - X^10 -
      C 2 * X^11 + X^13 := by
  rw [show (C (2 : ℚ) : PowerSeries ℚ) = 2 from map_ofNat C 2]
  ring

lemma numer_eq : (X^2*(1+3*X+12*X^2+21*X^3+27*X^4+28*X^5+31*X^6+25*X^7+
        18*X^8+11*X^9+3*X^10) : PowerSeries ℚ) =
    X^2 + C 3 * X^3 + C 12 * X^4 + C 21 * X^5 + C 27 * X^6 + C 28 * X^7 + C 31 * X^8 +
      C 25 * X^9 + C 18 * X^10 + C 11 * X^11 + C 3 * X^12 := by
  simp only [map_ofNat]
  ring

theorem a057870 :
    mk a * ((1-X)^4*(1+X)^3*(1-X+X^2)*(1+X+X^2)^2) =
      X^2*(1+3*X+12*X^2+21*X^3+27*X^4+28*X^5+31*X^6+25*X^7+
        18*X^8+11*X^9+3*X^10) ∧
    ∀ n : ℕ, 13 < n →
      a n = 2*a (n-2) + a (n-3) - a (n-4) - 2*a (n-5) + a (n-6) +
        a (n-7) - 2*a (n-8) - a (n-9) + a (n-10) + 2*a (n-11) - a (n-13) := by
  refine ⟨?_, fun n hn => by linarith [rec0 n (by omega)]⟩
  rw [denom_eq, numer_eq]
  ext n
  simp only [mul_sub, mul_add, mul_one, map_sub, map_add, mul_left_comm (mk a) (C _),
    coeff_C_mul, coeff_mul_X_pow', coeff_mk, coeff_X_pow, coeff_C]
  rcases Nat.lt_or_ge n 13 with h | h
  · interval_cases n <;> simp [a_eq, F] <;> norm_num
  · have := rec0 n h
    have l : ∀ j, j ≤ 12 → ¬ n ≤ j := fun j hj => by omega
    simp only [show 2 ≤ n by omega, show 3 ≤ n by omega, show 4 ≤ n by omega,
      show 5 ≤ n by omega, show 6 ≤ n by omega, show 7 ≤ n by omega, show 8 ≤ n by omega,
      show 9 ≤ n by omega, show 10 ≤ n by omega, show 11 ≤ n by omega, show 12 ≤ n by omega,
      show 13 ≤ n by omega, if_true, show n ≠ 2 by omega, Nat.sub_eq_zero_iff_le,
      l 2 (by norm_num), l 3 (by norm_num), l 4 (by norm_num), l 5 (by norm_num),
      l 6 (by norm_num), l 7 (by norm_num), l 8 (by norm_num), l 9 (by norm_num),
      l 10 (by norm_num), l 11 (by norm_num), l 12 (by norm_num), if_false]
    linarith

end OMA.A057870proof

theorem OMA.solution : type_of% @OMA.S_oeis_a057870.main := OMA.A057870proof.a057870
