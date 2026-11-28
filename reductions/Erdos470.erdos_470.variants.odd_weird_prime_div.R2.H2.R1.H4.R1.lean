import OMAReductions.R_Erdos470_erdos_470_variants_odd_weird_prime_div_R2_H2_R1

-- Reduction Erdos470.erdos_470.variants.odd_weird_prime_div.R2.H2.R1.H4.R1 of step
-- Erdos470.erdos_470.variants.odd_weird_prime_div.R2.H2.R1.H4
-- Credit: @Ciphore
-- With exactly four distinct primes the exponents must carry the whole abundance budget,
-- while five distinct primes spread it across a wider support: the exponent configurations
-- to enumerate are arithmetically different in the two regimes.

namespace OMA.R_Erdos470_erdos_470_variants_odd_weird_prime_div_R2_H2_R1_H4_R1

/-- The four-prime case of the remaining multiples of 45. -/
def H1 : Prop :=
  ∀ n : ℕ, Odd n → n.Abundant → n.primeFactors.card = 4 →
    (∀ d ∈ n.properDivisors, d.Deficient) → 45 ∣ n → ¬7 ∣ n → ¬11 ∣ n → ¬13 ∣ n →
    (∃ r ∈ ([17,19,23,29,31,37,41,43] : List ℕ), r ∣ n) → n.Pseudoperfect

/-- The five-prime case of the remaining multiples of 45. -/
def H2 : Prop :=
  ∀ n : ℕ, Odd n → n.Abundant → n.primeFactors.card = 5 →
    (∀ d ∈ n.properDivisors, d.Deficient) → 45 ∣ n → ¬7 ∣ n → ¬11 ∣ n → ¬13 ∣ n →
    (∃ r ∈ ([17,19,23,29,31,37,41,43] : List ℕ), r ∣ n) → n.Pseudoperfect

theorem main : H1 → H2 →
    OMA.R_Erdos470_erdos_470_variants_odd_weird_prime_div_R2_H2_R1.H4 := by
  intro hfour hfive n ho ha hc4 hc5 hp h45 h7 h11 h13 hex
  have hc : n.primeFactors.card = 4 ∨ n.primeFactors.card = 5 := by omega
  rcases hc with h | h
  · exact hfour n ho ha h hp h45 h7 h11 h13 hex
  · exact hfive n ho ha h hp h45 h7 h11 h13 hex

end OMA.R_Erdos470_erdos_470_variants_odd_weird_prime_div_R2_H2_R1_H4_R1
