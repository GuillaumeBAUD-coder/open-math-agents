import OMAReductions.R_Erdos470_erdos_470_variants_odd_weird_10_pow_21_R1

/-!
The number of distinct prime factors separates the small geometric-sum certificate
from the branches with at least five prime factors.
-/

-- Credit: @Genbox

namespace OMA.R_Erdos470_erdos_470_variants_odd_weird_10_pow_21_R1_H1_R1

def H1 : Prop :=
  ∀ n < 10 ^ 21, Odd n → n.Abundant → (∀ d ∈ n.properDivisors, d.Deficient) → 3 ∣ n →
    n.primeFactors.card ≤ 4 → n.Pseudoperfect

def H2 : Prop :=
  ∀ n < 10 ^ 21, Odd n → n.Abundant → (∀ d ∈ n.properDivisors, d.Deficient) → 3 ∣ n →
    5 ≤ n.primeFactors.card → n.Pseudoperfect

theorem main : H1 → H2 → OMA.R_Erdos470_erdos_470_variants_odd_weird_10_pow_21_R1.H1 := by
  intro hsmall hlarge n bound odd abundant primitive three
  by_cases hcard : n.primeFactors.card ≤ 4
  · exact hsmall n bound odd abundant primitive three hcard
  · exact hlarge n bound odd abundant primitive three (by omega)

end OMA.R_Erdos470_erdos_470_variants_odd_weird_10_pow_21_R1_H1_R1