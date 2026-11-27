import OMAReductions.R_Erdos821_erdos_821_variants_erdos_R1

/-!
# A uniform divisor bound

Separating small and large prime factors gives a fixed constant C such that
the fourteenth power of the divisor count of n is at most Cn for positive n.
-/
open Finset Filter
namespace DivisorCap

private lemma local_bound (p e : ℕ) (hp : 2 ≤ p) :
    (e + 1)^14 ≤ (if p < 2^14 then 14^14 else 1) * p^e := by
  split_ifs with hsmall
  · have hquot : e + 1 ≤ 14 * (e / 14 + 1) := by omega
    have hle : e + 1 ≤ 14 * 2^(e/14) :=
      hquot.trans (Nat.mul_le_mul_left 14 (e/14).lt_two_pow_self)
    calc
      (e + 1)^14 ≤ (14 * 2^(e/14))^14 := Nat.pow_le_pow_left hle 14
      _ = 14^14 * 2^(e/14*14) := by rw [mul_pow, ← pow_mul]
      _ ≤ 14^14 * p^e := Nat.mul_le_mul_left _ <|
        (Nat.pow_le_pow_right (by decide) (Nat.div_mul_le_self e 14)).trans
          (Nat.pow_le_pow_left hp e)
  · rw [one_mul]
    calc
      (e + 1)^14 ≤ (2^e)^14 := Nat.pow_le_pow_left e.lt_two_pow_self 14
      _ = (2^14)^e := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
      _ ≤ p^e := Nat.pow_le_pow_left (by omega) e

private lemma divisor_power_le (n : ℕ) (hn : 0 < n) :
    n.divisors.card^14 ≤ (14^14)^(2^14) * n := by
  have hsmall : (n.primeFactors.filter (fun p => p < 2^14)).card ≤ 2^14 := by
    calc
      _ ≤ (Finset.range (2^14)).card := Finset.card_le_card (fun _ hp =>
        Finset.mem_range.mpr (Finset.mem_filter.mp hp).2)
      _ = _ := Finset.card_range _
  have hcoef : (∏ p ∈ n.primeFactors, (if p < 2^14 then (14:ℕ)^14 else 1))
      ≤ (14^14)^(2^14) := by
    rw [Finset.prod_ite]
    simp only [Finset.prod_const, one_pow, mul_one]
    exact pow_le_pow_right₀ (by norm_num) hsmall
  calc
    n.divisors.card^14 = ∏ p ∈ n.primeFactors, (n.factorization p + 1)^14 := by
      rw [Nat.card_divisors hn.ne', Finset.prod_pow]
    _ ≤ ∏ p ∈ n.primeFactors, (if p < 2^14 then 14^14 else 1) * p^(n.factorization p) :=
      Finset.prod_le_prod' (fun p hp => local_bound p _ (Nat.prime_of_mem_primeFactors hp).two_le)
    _ = (∏ p ∈ n.primeFactors, (if p < 2^14 then 14^14 else 1)) * n := by
      rw [Finset.prod_mul_distrib, ← Nat.prod_primeFactors_pow_factorization hn.ne']
    _ ≤ (14^14)^(2^14) * n := Nat.mul_le_mul_right n hcoef

lemma divisor_cap : ∀ᶠ t : ℕ in atTop, ∀ n ∈ Finset.Icc 1 (t^6), n.divisors.card ≤ t.sqrt := by
  filter_upwards [eventually_ge_atTop ((14^14 : ℕ)^(2^14))] with t ht
  intro n hn
  obtain ⟨hn0, hnt⟩ := Finset.mem_Icc.mp hn
  apply Nat.le_sqrt'.mpr
  apply (Nat.pow_le_pow_iff_left (by decide : 7 ≠ 0)).mp
  calc
    (n.divisors.card^2)^7 = n.divisors.card^14 := by rw [← pow_mul]
    _ ≤ (14^14)^(2^14) * n := divisor_power_le n hn0
    _ ≤ t * t^6 := Nat.mul_le_mul ht hnt
    _ = t^7 := by ring

end DivisorCap

theorem OMA.solution : OMA.R_Erdos821_erdos_821_variants_erdos_R1.H2 := DivisorCap.divisor_cap
