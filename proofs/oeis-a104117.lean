import OMAStatements.S_oeis_a104117
import Mathlib.Tactic

open OMA.S_oeis_a104117 ArithmeticFunction Finset

namespace PowersOfTwoConvolution

private lemma indicator (n : ℕ) :
    powerIndicator n = if n = 2 ^ n.log2 then 1 else 0 := rfl

private lemma indicator_pow (e : ℕ) : powerIndicator (2 ^ e) = 1 := by
  rw [indicator, Nat.log2_two_pow, if_pos rfl]

private lemma squared_at_power (e : ℕ) :
    (powerIndicator * powerIndicator) (2 ^ e) = (e : ℤ) + 1 := calc
  _ = ∑ p ∈ (2 ^ e : ℕ).divisorsAntidiagonal, (1 : ℤ) := by
    rw [ArithmeticFunction.mul_apply]
    apply sum_congr rfl
    intro p hp
    obtain ⟨a, _, ha⟩ := (Nat.mem_divisors_prime_pow Nat.prime_two e).1
      (Nat.fst_mem_divisors_of_mem_antidiagonal hp)
    obtain ⟨b, _, hb⟩ := (Nat.mem_divisors_prime_pow Nat.prime_two e).1
      (Nat.snd_mem_divisors_of_mem_antidiagonal hp)
    rw [ha, hb, indicator_pow, indicator_pow, one_mul]
  _ = ∑ d ∈ (2 ^ e : ℕ).divisors, (1 : ℤ) :=
    Nat.sum_divisorsAntidiagonal (fun _ _ => (1 : ℤ))
  _ = (e : ℤ) + 1 := by rw [Nat.sum_divisors_prime_pow Nat.prime_two]; simp

private lemma squared_elsewhere (n : ℕ) (hn : n ≠ 2 ^ n.log2) :
    (powerIndicator * powerIndicator) n = 0 := by
  rw [ArithmeticFunction.mul_apply]
  apply sum_eq_zero
  intro p hp
  by_cases ha : p.1 = 2 ^ p.1.log2
  · have hb : p.2 ≠ 2 ^ p.2.log2 := by
      intro hb
      have factor : n = 2 ^ (p.1.log2 + p.2.log2) := calc
        n = p.1 * p.2 := (Nat.mem_divisorsAntidiagonal.mp hp).1.symm
        _ = 2 ^ p.1.log2 * 2 ^ p.2.log2 := congrArg₂ (· * ·) ha hb
        _ = _ := (pow_add _ _ _).symm
      exact hn (by rw [factor, Nat.log2_two_pow])
    rw [indicator p.2, if_neg hb, mul_zero]
  · rw [indicator p.1, if_neg ha, zero_mul]

end PowersOfTwoConvolution

theorem OMA.solution : type_of% @OMA.S_oeis_a104117.main := by
  intro n _
  rw [Nat.sum_div_divisors, ← coe_zeta_mul_apply]
  unfold coefficient
  rw [← mul_assoc, ← mul_assoc, coe_zeta_mul_moebius, one_mul]
  by_cases h : n = 2 ^ n.log2
  · rw [if_pos h]
    calc
      (powerIndicator * powerIndicator) n =
          (powerIndicator * powerIndicator) (2 ^ n.log2) :=
        congrArg (powerIndicator * powerIndicator) h
      _ = _ := PowersOfTwoConvolution.squared_at_power _
  · rw [if_neg h]
    exact PowersOfTwoConvolution.squared_elsewhere n h
