import OMAStatements.S_oeis_a328959
import Mathlib

open OMA.S_oeis_a328959

namespace P328959

open ArithmeticFunction

theorem inv (n : ℕ) : n ≠ 0 → ∃ f, cardFactors n = cardDistinctFactors n + f ∧
    2 ^ cardDistinctFactors n * (2 + f) ≤ 2 * n.divisors.card := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | zero => intro h; exact absurd rfl h
  | one => intro _; exact ⟨0, by simp, by simp⟩
  | prime_pow p k hp hk =>
    intro _
    refine ⟨k - 1, ?_, ?_⟩
    · rw [cardFactors_apply_prime_pow hp, cardDistinctFactors_apply_prime_pow hp hk.ne']; omega
    · rw [cardDistinctFactors_apply_prime_pow hp hk.ne', ← sigma_zero_apply,
        sigma_zero_apply_prime_pow hp]; omega
  | coprime x y hx hy hxy ihx ihy =>
    intro _
    obtain ⟨fx, hfx, hx2⟩ := ihx (by omega)
    obtain ⟨fy, hfy, hy2⟩ := ihy (by omega)
    refine ⟨fx + fy, ?_, ?_⟩
    · rw [cardFactors_mul (by omega) (by omega), cardDistinctFactors_mul hxy, hfx, hfy]; ring
    · rw [cardDistinctFactors_mul hxy, Nat.Coprime.card_divisors_mul hxy, pow_add]
      have h := Nat.mul_le_mul hx2 hy2
      have h2 : 2 * (2 + (fx + fy)) ≤ (2 + fx) * (2 + fy) := by nlinarith
      have h3 := Nat.mul_le_mul_left (2 ^ cardDistinctFactors x * 2 ^ cardDistinctFactors y) h2
      nlinarith

theorem pow_ge1 (w : ℕ) (hw : 1 ≤ w) : 2 + w * (w - 1) ≤ 2 ^ w := by
  induction w with
  | zero => omega
  | succ w ih =>
    rcases Nat.eq_zero_or_pos w with rfl | hw'
    · simp
    · have := ih hw'
      rw [pow_succ]
      cases w with
      | zero => omega
      | succ w =>
        simp only [Nat.add_sub_cancel] at this ⊢
        have := Nat.le_mul_self w
        nlinarith

theorem pow_ge2 (w : ℕ) : 2 * w ≤ 2 ^ w := by
  induction w with
  | zero => simp
  | succ w ih =>
    rw [pow_succ]
    rcases Nat.eq_zero_or_pos w with rfl | hw
    · simp
    · have : 1 ≤ 2 ^ w := Nat.one_le_two_pow
      omega

end P328959

open ArithmeticFunction in
theorem OMA.solution : type_of% @OMA.S_oeis_a328959.main := by
  refine ⟨by simp [a], ?_⟩
  intro n hn
  obtain ⟨f, hf, h2⟩ := P328959.inv n (by omega)
  have hw : 1 ≤ cardDistinctFactors n := by
    rw [Nat.one_le_iff_ne_zero, Ne, cardDistinctFactors_eq_zero]; omega
  unfold a
  rw [hf]
  obtain ⟨v, hv⟩ : ∃ v, cardDistinctFactors n = v + 1 := ⟨cardDistinctFactors n - 1, by omega⟩
  rw [hv] at h2 ⊢
  have e1 := P328959.pow_ge1 (v + 1) (by omega)
  have e2 := P328959.pow_ge2 (v + 1)
  have e3 : 2 * (v + 1) * f ≤ 2 ^ (v + 1) * f := Nat.mul_le_mul_right f e2
  simp only [Nat.add_sub_cancel] at e1
  push_cast
  have : (2:ℤ) ^ (v+1) * (2 + f) ≤ 2 * (n.divisors.card : ℤ) := by exact_mod_cast h2
  have e1' : (2:ℤ) + (v+1) * v ≤ 2 ^ (v+1) := by exact_mod_cast e1
  have e3' : (2:ℤ) * (v+1) * f ≤ 2 ^ (v+1) * f := by exact_mod_cast e3
  nlinarith
