import OMAStatements.S_oeis_a023365
import Mathlib

/-!
Credit: @ivillar
Proof: by induction b(n) = N/2^(3^n) with N an odd integer: writing 3^n = f + 1,
b(n+1) = N (3*2^(2f+1) - N^2) / 2^(3f+3), and N (3*2^(2f+1) - N^2) is odd (an odd number
times an even number minus an odd square). An odd integer over a power of two is in lowest
terms, so the denominator of b(n) is 2^(3^n) = a(n+1).
-/

namespace OMAA023365Helpers
open OMA.S_oeis_a023365

theorem inv (n : ℕ) : ∃ N : ℤ, Odd N ∧ b n = (N : ℚ) / 2 ^ (3 ^ n) := by
  induction n with
  | zero => exact ⟨1, odd_one, by simp [b]⟩
  | succ n ih =>
    obtain ⟨N, hN, hb⟩ := ih
    have hpos : 0 < 3 ^ n := by positivity
    obtain ⟨f, hf⟩ : ∃ f, 3 ^ n = f + 1 := ⟨3 ^ n - 1, by omega⟩
    refine ⟨N * (3 * 2 ^ (2 * f + 1) - N ^ 2), ?_, ?_⟩
    · apply hN.mul
      apply Even.sub_odd _ hN.pow
      exact (Int.even_pow.mpr ⟨even_two, by omega⟩).mul_left 3
    · have h3 : 3 ^ (n + 1) = 3 * f + 3 := by rw [pow_succ, hf]; ring
      show b n * (3 / 2 - b n ^ 2) = _
      rw [hb, hf, h3]
      push_cast
      field_simp
      ring

theorem den_odd (N : ℤ) (hN : Odd N) (k : ℕ) : ((N : ℚ) / 2 ^ k).den = 2 ^ k := by
  have hc : Nat.Coprime N.natAbs ((2 : ℤ) ^ k).natAbs := by
    rw [Int.natAbs_pow]
    exact Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr (Int.natAbs_odd.mpr hN))
  have h := Rat.den_div_eq_of_coprime (a := N) (b := 2 ^ k) (by positivity) hc
  push_cast at h
  exact_mod_cast h

end OMAA023365Helpers

open OMAA023365Helpers in
theorem OMA.solution : type_of% @OMA.S_oeis_a023365.main := by
  intro n
  obtain ⟨N, hN, hb⟩ := inv n
  rw [hb, den_odd N hN]
  unfold OMA.S_oeis_a023365.a
  simp
