import OMAStatements.S_oeis_a023365
import Mathlib

/-!
By induction b(n) = N / 2^(3^n) with N odd: writing 3^n = j + 1,
b(n+1) = N (3 * 2^(2j+1) - N^2) / 2^(3^(n+1)), and 3 * 2^(2j+1) - N^2 is odd.
An odd numerator is coprime to a power of 2, so the reduced denominator is 2^(3^n).
-/

namespace R023365
open OMA.S_oeis_a023365

theorem form : ∀ n : ℕ, ∃ N : ℤ, Odd N ∧ b n = (N : ℚ) / (2 : ℚ) ^ (3 ^ n) := by
  intro n
  induction n with
  | zero => exact ⟨1, odd_one, by rw [show b 0 = 1 / 2 from rfl]; norm_num⟩
  | succ n ih =>
    obtain ⟨N, hN, hb⟩ := ih
    obtain ⟨j, hj⟩ : ∃ j, 3 ^ n = j + 1 :=
      ⟨3 ^ n - 1, by have := Nat.one_le_pow n 3 (by norm_num); omega⟩
    refine ⟨N * (3 * 2 ^ (2 * j + 1) - N ^ 2), ?_, ?_⟩
    · apply Odd.mul hN
      have he : Even ((3 : ℤ) * 2 ^ (2 * j + 1)) := by
        apply Even.mul_left
        exact Int.even_pow.mpr ⟨even_two, by omega⟩
      exact Even.sub_odd he hN.pow
    · rw [show b (n + 1) = b n * (3 / 2 - b n ^ 2) from rfl, hb,
        show (3 : ℕ) ^ (n + 1) = 3 * j + 3 by rw [pow_succ, hj]; ring, hj]
      push_cast
      field_simp
      ring

theorem den_odd (N : ℤ) (hN : Odd N) (k : ℕ) : ((N : ℚ) / (2 : ℚ) ^ k).den = 2 ^ k := by
  have hc : Nat.Coprime N.natAbs ((2 : ℤ) ^ k).natAbs := by
    rw [Int.natAbs_pow, show (2 : ℤ).natAbs = 2 from rfl]
    exact Nat.Coprime.pow_right k (Int.natAbs_odd.mpr hN).coprime_two_right
  have h := Rat.den_div_eq_of_coprime (by positivity : (0 : ℤ) < 2 ^ k) hc
  push_cast at h
  exact_mod_cast h

theorem solve : ∀ n : ℕ, ((b n).den : ℕ) = a (n + 1) := by
  intro n
  obtain ⟨N, hN, hb⟩ := form n
  rw [hb, den_odd N hN]
  simp only [a, Nat.add_sub_cancel]

end R023365

theorem OMA.solution : type_of% @OMA.S_oeis_a023365.main := R023365.solve
