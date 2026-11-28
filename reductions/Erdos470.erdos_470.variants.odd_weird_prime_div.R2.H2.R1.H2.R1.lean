import OMAReductions.R_Erdos470_erdos_470_variants_odd_weird_prime_div_R2_H2_R1

-- Reduction Erdos470.erdos_470.variants.odd_weird_prime_div.R2.H2.R1.H2.R1 of step
-- Erdos470.erdos_470.variants.odd_weird_prime_div.R2.H2.R1.H2
-- Credit: @Ciphore
-- The four witness primes contribute different abundancy factors `12/11`, `14/13`,
-- `18/17`, `20/19` to the budget, so the exponent configurations compatible with
-- primitive abundance differ from case to case: the larger the witness, the tighter
-- the remaining exponent budget. The enumeration is split accordingly.

namespace OMA.R_Erdos470_erdos_470_variants_odd_weird_prime_div_R2_H2_R1_H2_R1

/-- The `11`-witness case of the multiples-of-63 leaf. -/
def H1 : Prop :=
  ∀ n : ℕ, Odd n → n.Abundant → 4 ≤ n.primeFactors.card → n.primeFactors.card ≤ 5 →
    (∀ d ∈ n.properDivisors, d.Deficient) → 63 ∣ n → ¬5 ∣ n → 11 ∣ n → n.Pseudoperfect

/-- The `13`-witness case of the multiples-of-63 leaf. -/
def H2 : Prop :=
  ∀ n : ℕ, Odd n → n.Abundant → 4 ≤ n.primeFactors.card → n.primeFactors.card ≤ 5 →
    (∀ d ∈ n.properDivisors, d.Deficient) → 63 ∣ n → ¬5 ∣ n → 13 ∣ n → n.Pseudoperfect

/-- The `17`-witness case of the multiples-of-63 leaf. -/
def H3 : Prop :=
  ∀ n : ℕ, Odd n → n.Abundant → 4 ≤ n.primeFactors.card → n.primeFactors.card ≤ 5 →
    (∀ d ∈ n.properDivisors, d.Deficient) → 63 ∣ n → ¬5 ∣ n → 17 ∣ n → n.Pseudoperfect

/-- The `19`-witness case of the multiples-of-63 leaf. -/
def H4 : Prop :=
  ∀ n : ℕ, Odd n → n.Abundant → 4 ≤ n.primeFactors.card → n.primeFactors.card ≤ 5 →
    (∀ d ∈ n.properDivisors, d.Deficient) → 63 ∣ n → ¬5 ∣ n → 19 ∣ n → n.Pseudoperfect

theorem main : H1 → H2 → H3 → H4 →
    OMA.R_Erdos470_erdos_470_variants_odd_weird_prime_div_R2_H2_R1.H2 := by
  intro h11 h13 h17 h19 n ho ha hc4 hc5 hp h63 h5 hex
  obtain ⟨r, hrmem, hrdv⟩ := hex
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hrmem
  rcases hrmem with rfl | rfl | rfl | rfl
  · exact h11 n ho ha hc4 hc5 hp h63 h5 hrdv
  · exact h13 n ho ha hc4 hc5 hp h63 h5 hrdv
  · exact h17 n ho ha hc4 hc5 hp h63 h5 hrdv
  · exact h19 n ho ha hc4 hc5 hp h63 h5 hrdv

end OMA.R_Erdos470_erdos_470_variants_odd_weird_prime_div_R2_H2_R1_H2_R1
