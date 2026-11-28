import OMAStatements.S_oeis_a168222
import Mathlib

/-!
A006369 is f(3k) = 2k, f(3k+1) = 4k+1, f(3k+2) = 4k+3, so 3 f(n) is 2n, 4n - 1 or 4n + 1
according to n mod 3. Then f(n + 9) - f(n) and f(n + 18) - f(n + 9) are the same multiple of 3,
f(n + 9) = f(n) mod 3, and omega gives a(n + 18) + a(n) = 2 a(n + 9).
The g.f. denominator is (1 - x^9)^2, so the coefficients of x^n, n >= 18, vanish by the
recurrence, and those for n < 18 are a finite check.
-/

namespace R168222
open OMA.S_oeis_a168222 PowerSeries

theorem round_aux (k : ℕ) (x : ℚ) (h1 : (k : ℚ) - 1 / 2 ≤ x) (h2 : x < k + 1 / 2) :
    (round x).toNat = k := by
  have h : round x = (k : ℤ) := by
    rw [round_eq, Int.floor_eq_iff]
    push_cast
    constructor <;> linarith
  rw [h]
  simp

theorem f0 (k : ℕ) : A006369 (3 * k) = 2 * k := by
  unfold A006369
  have h : (3 * k) % 3 = 0 := by omega
  rw [if_pos h]
  omega

theorem f1 (k : ℕ) : A006369 (3 * k + 1) = 4 * k + 1 := by
  unfold A006369
  have h : (3 * k + 1) % 3 ≠ 0 := by omega
  rw [if_neg h]
  apply round_aux
  · push_cast
    linarith
  · push_cast
    linarith

theorem f2 (k : ℕ) : A006369 (3 * k + 2) = 4 * k + 3 := by
  unfold A006369
  have h : (3 * k + 2) % 3 ≠ 0 := by omega
  rw [if_neg h]
  apply round_aux
  · push_cast
    linarith
  · push_cast
    linarith

theorem fchar (n : ℕ) : (n % 3 = 0 ∧ 3 * A006369 n = 2 * n) ∨
    (n % 3 = 1 ∧ 3 * A006369 n + 1 = 4 * n) ∨ (n % 3 = 2 ∧ 3 * A006369 n = 4 * n + 1) := by
  rcases (show n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 by omega) with h | h | h
  · have e : n = 3 * (n / 3) := by omega
    rw [e, f0]
    omega
  · have e : n = 3 * (n / 3) + 1 := by omega
    rw [e, f1]
    omega
  · have e : n = 3 * (n / 3) + 2 := by omega
    rw [e, f2]
    omega

theorem rec9 (n : ℕ) : (a (n + 18) : ℤ) = 2 * a (n + 9) - a n := by
  have h1 := fchar n
  have h2 := fchar (n + 9)
  have h3 := fchar (n + 18)
  have h4 := fchar (A006369 n)
  have h5 := fchar (A006369 (n + 9))
  have h6 := fchar (A006369 (n + 18))
  simp only [a]
  omega

theorem vals : a 0 = 0 ∧ a 1 = 1 ∧ a 2 = 2 ∧ a 3 = 3 ∧ a 4 = 7 ∧ a 5 = 9 ∧ a 6 = 5 ∧
    a 7 = 6 ∧ a 8 = 15 ∧ a 9 = 4 ∧ a 10 = 17 ∧ a 11 = 10 ∧ a 12 = 11 ∧ a 13 = 23 ∧
    a 14 = 25 ∧ a 15 = 13 ∧ a 16 = 14 ∧ a 17 = 31 := by
  simp only [a]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    first
    | (have g1 := fchar 0; have g2 := fchar (A006369 0); omega)
    | (have g1 := fchar 1; have g2 := fchar (A006369 1); omega)
    | (have g1 := fchar 2; have g2 := fchar (A006369 2); omega)
    | (have g1 := fchar 3; have g2 := fchar (A006369 3); omega)
    | (have g1 := fchar 4; have g2 := fchar (A006369 4); omega)
    | (have g1 := fchar 5; have g2 := fchar (A006369 5); omega)
    | (have g1 := fchar 6; have g2 := fchar (A006369 6); omega)
    | (have g1 := fchar 7; have g2 := fchar (A006369 7); omega)
    | (have g1 := fchar 8; have g2 := fchar (A006369 8); omega)
    | (have g1 := fchar 9; have g2 := fchar (A006369 9); omega)
    | (have g1 := fchar 10; have g2 := fchar (A006369 10); omega)
    | (have g1 := fchar 11; have g2 := fchar (A006369 11); omega)
    | (have g1 := fchar 12; have g2 := fchar (A006369 12); omega)
    | (have g1 := fchar 13; have g2 := fchar (A006369 13); omega)
    | (have g1 := fchar 14; have g2 := fchar (A006369 14); omega)
    | (have g1 := fchar 15; have g2 := fchar (A006369 15); omega)
    | (have g1 := fchar 16; have g2 := fchar (A006369 16); omega)
    | (have g1 := fchar 17; have g2 := fchar (A006369 17); omega)

end R168222

open OMA.S_oeis_a168222 R168222 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a168222.main := by
  refine ⟨?_, fun n hn => ?_⟩
  · rw [show ((1 - X) ^ 2 * (1 + X + X ^ 2) ^ 2 * (1 + X ^ 3 + X ^ 6) ^ 2 : ℤ⟦X⟧) =
        1 - C 2 * X ^ 9 + X ^ 18 by simp only [map_ofNat]; ring,
      show ∀ p : ℤ⟦X⟧, p * (1 - C 2 * X ^ 9 + X ^ 18) = p - C 2 * (p * X ^ 9) + p * X ^ 18
        from fun p => by ring,
      show (X * (1 + 2 * X + 3 * X ^ 2 + 7 * X ^ 3 + 9 * X ^ 4 + 5 * X ^ 5 + 6 * X ^ 6 +
        15 * X ^ 7 + 4 * X ^ 8 + 15 * X ^ 9 + 6 * X ^ 10 + 5 * X ^ 11 + 9 * X ^ 12 +
        7 * X ^ 13 + 3 * X ^ 14 + 2 * X ^ 15 + X ^ 16) : ℤ⟦X⟧) =
        X ^ 1 + C 2 * X ^ 2 + C 3 * X ^ 3 + C 7 * X ^ 4 + C 9 * X ^ 5 + C 5 * X ^ 6 +
        C 6 * X ^ 7 + C 15 * X ^ 8 + C 4 * X ^ 9 + C 15 * X ^ 10 + C 6 * X ^ 11 +
        C 5 * X ^ 12 + C 9 * X ^ 13 + C 7 * X ^ 14 + C 3 * X ^ 15 + C 2 * X ^ 16 + X ^ 17 by
        simp only [map_ofNat]; ring]
    ext n
    simp only [map_add, map_sub, coeff_C_mul, coeff_mul_X_pow', coeff_mk, coeff_C, coeff_X_pow]
    by_cases hn : 18 ≤ n
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 18 := ⟨n - 18, by omega⟩
      have e1 : m + 18 - 9 = m + 9 := by omega
      have e2 : m + 18 - 18 = m := by omega
      have r := rec9 m
      simp [e1, e2]
      linarith
    · interval_cases n <;> simp [vals]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 18 := ⟨n - 18, by omega⟩
    rw [show m + 18 - 9 = m + 9 by omega, show m + 18 - 18 = m by omega]
    exact rec9 m
