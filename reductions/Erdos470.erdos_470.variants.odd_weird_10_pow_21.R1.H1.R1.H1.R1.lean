import OMAReductions.R_Erdos470_erdos_470_variants_odd_weird_10_pow_21_R1_H1_R1
import Mathlib

namespace OddWeirdMerged

open Finset ArithmeticFunction

theorem excess_of_pseudoperfect {n : ℕ} (certificate : n.Pseudoperfect) :
    let E : ℤ := (sigma 1 n : ℤ) - 2 * (n : ℤ)
    ∃ s ⊆ n.properDivisors.filter (fun d : ℕ => (d : ℤ) ≤ E),
      (∑ d ∈ s, (d : ℤ)) = E := by
  classical
  let E : ℤ := (sigma 1 n : ℤ) - 2 * (n : ℤ)
  obtain ⟨_, chosen, represented, amount⟩ := certificate
  let rest := n.properDivisors \ chosen
  have chosen_sum : (∑ d ∈ chosen, (d : ℤ)) = (n : ℤ) := by
    simpa only [Nat.cast_sum] using congrArg (fun x : ℕ => (x : ℤ)) amount
  have total : (sigma 1 n : ℤ) = (∑ d ∈ n.properDivisors, (d : ℤ)) + n := by
    rw [ArithmeticFunction.sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self]
    simp
  have split := Finset.sum_sdiff represented (f := fun d : ℕ => (d : ℤ))
  have rest_sum : (∑ d ∈ rest, (d : ℤ)) = E := by
    dsimp [E,rest]
    linarith only [chosen_sum,total,split]
  change ∃ s ⊆ n.properDivisors.filter (fun d : ℕ => (d : ℤ) ≤ E),
    (∑ d ∈ s, (d : ℤ)) = E
  refine ⟨rest, ?_, rest_sum⟩
  intro d hd
  have le : (d : ℤ) ≤ ∑ x ∈ rest, (x : ℤ) :=
    Finset.single_le_sum (fun x _ => Int.natCast_nonneg x) hd
  rw [rest_sum] at le
  exact Finset.mem_filter.mpr ⟨Finset.sdiff_subset hd,le⟩

end OddWeirdMerged

namespace OMA.R_Erdos470_erdos_470_variants_odd_weird_10_pow_21_R1_H1_R1_H1_R1

open Finset ArithmeticFunction

def H1 : Prop :=
  ∀ b q : ℕ, q.Prime →
    let n := b*q
    n < 10^21 → Odd n → n.Abundant → (∀ d ∈ n.properDivisors, d.Deficient) → 3 ∣ n →
    (n.primeFactors.card ≤ 4 ∨
      (1000000 ≤ q ∧ ∃ u v w x : ℕ, 0 < u ∧ 0 < v ∧ 0 < w ∧ 0 < x ∧
        b = 3^u * 5^v * 17^w * 233^x)) →
    n.Pseudoperfect

def H2 : Prop :=
  ∀ b q : ℕ, 1 < b → q.Prime → 3 ≤ q → b.Coprime q →
    (∀ p ∈ b.primeFactors, p < q) →
    let n := b*q
    n < 10^21 → Odd n → n.Abundant → (∀ d ∈ n.properDivisors, d.Deficient) → 3 ∣ n →
    (¬ (n.primeFactors.card ≤ 4 ∨
      (1000000 ≤ q ∧ ∃ u v w x : ℕ, 0 < u ∧ 0 < v ∧ 0 < w ∧ 0 < x ∧
        b = 3^u * 5^v * 17^w * 233^x))) →
    let E : ℤ := (sigma 1 n : ℤ) - 2*(n : ℤ)
    let P := ∑ d ∈ b.properDivisors, (d : ℤ)
    let R := fun x : ℤ => ∃ s ⊆ b.properDivisors, (∑ d ∈ s, (d : ℤ)) = x
    let G : ℤ := Nat.gcd (sigma 1 b) (2*b)
    (¬ ∃ s ⊆ b.divisors, (∑ d ∈ s, (d : ℤ)) = E) →
    G ∣ E → 0 < E →
    (∀ L g : ℤ, 1 ≤ L → 1 ≤ g → (2*g+1)*(2*L+8*g+8) ≤ P →
    2 ≤ (b : ℤ)-P →
      (∀ y : ℤ, L ≤ y → y ≤ P-L → R y) →
      (∀ k : ℤ, 0 ≤ k → k < P → ∃ i : ℤ, R i ∧ k-g < i ∧ i ≤ k) →
      E < L ∧ G < L) →
    ∃ s ⊆ n.properDivisors.filter (fun d : ℕ => (d : ℤ) ≤ E), (∑ d ∈ s, (d : ℤ)) = E

theorem main : H1 → H2 → OMA.R_Erdos470_erdos_470_variants_odd_weird_10_pow_21_R1_H1_R1.H1 := by
  intro solvedCases otherCases b q bp hp q3 cop largest
  dsimp only
  intro size odd abundant primitive three missing divides positive noInterval
  by_cases covered : (b*q).primeFactors.card ≤ 4 ∨
      (1000000 ≤ q ∧ ∃ u v w x : ℕ, 0 < u ∧ 0 < v ∧ 0 < w ∧ 0 < x ∧
        b = 3^u * 5^v * 17^w * 233^x)
  · exact OddWeirdMerged.excess_of_pseudoperfect
      (solvedCases b q hp size odd abundant primitive three covered)
  · exact otherCases b q bp hp q3 cop largest size odd abundant primitive three
      covered missing divides positive noInterval

end OMA.R_Erdos470_erdos_470_variants_odd_weird_10_pow_21_R1_H1_R1_H1_R1