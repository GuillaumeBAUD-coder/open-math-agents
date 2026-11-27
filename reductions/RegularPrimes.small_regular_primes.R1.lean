import FormalConjectures.Wikipedia.RegularPrimes

/-!
# Certify the Bernoulli test for the odd primes through 31

The finite rational table is checked against the defining recurrence for
the Mathlib Bernoulli numbers. This leaves only the odd-prime implication of
Kummer's criterion and the separate quadratic cyclotomic-field case.
See https://github.com/riccardobrasca/KummerCriterion.
-/

namespace OMA.R_RegularPrimes_small_regular_primes_R1

set_option maxRecDepth 10000 in
private theorem verified_numerators (p : ℕ) (hp : p.Prime) (hmax : p ≤ 31) :
    ∀ k ∈ Finset.Icc 2 (p - 3), Even k → ¬ (p : ℤ) ∣ (bernoulli' k).num := by
  let B (n : ℕ) : ℚ := ([1, 1/2, 1/6, 0, -1/30, 0, 1/42, 0, -1/30, 0, 5/66, 0, -691/2730, 0, 7/6, 0, -3617/510, 0, 43867/798, 0, -174611/330, 0, 854513/138, 0, -236364091/2730, 0, 8553103/6, 0, -23749461029/870] : List ℚ)[n]?.getD 0
  have recurrence : ∀ i : Fin 29, B i.val = 1 -
      ∑ k ∈ Finset.range i.val, i.val.choose k / (i.val - k + 1) * B k := by
    decide +kernel
  have certified (n : ℕ) (hn : n < 29) : bernoulli' n = B n := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      calc
        _ = 1 - ∑ k ∈ Finset.range n, n.choose k / (n - k + 1) * bernoulli' k :=
          bernoulli'_def n
        _ = 1 - ∑ k ∈ Finset.range n, n.choose k / (n - k + 1) * B k := by
          congr 1
          refine Finset.sum_congr rfl fun k hk => ?_
          have hklt := Finset.mem_range.mp hk
          rw [ih k hklt (hklt.trans hn)]
        _ = _ := (recurrence ⟨n, hn⟩).symm
  have certificate : ∀ (q : Fin 32) (k : Fin 29),
      q.val.Prime → 2 ≤ k.val → k.val ≤ q.val - 3 → Even k.val →
      ¬ (q.val : ℤ) ∣ (B k.val).num := by
    decide +kernel
  intro k hk he
  obtain ⟨hk₀, hk₁⟩ := Finset.mem_Icc.mp hk
  have hkl : k < 29 := by omega
  rw [certified k hkl]
  exact certificate ⟨p, by omega⟩ ⟨k, hkl⟩ hp hk₀ hk₁ he

/-- Kummer's criterion in the sufficient direction for the specified odd primes. -/
def H1 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → p ≤ 31 →
    (∀ k ∈ Finset.Icc 2 (p - 3), Even k → ¬ (p : ℤ) ∣ (bernoulli' k).num) →
    RegularPrimes.IsRegularPrime p

/-- The cyclotomic class number test at the prime two. -/
def H2 : Prop := @RegularPrimes.IsRegularPrime 2 ⟨Nat.prime_two⟩

theorem main : H1 → H2 → type_of% @RegularPrimes.small_regular_primes := by
  intro hOdd hTwo p hp
  have hp' : p.Prime ∧ p ≤ 31 := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  refine ⟨hp'.1, ?_⟩
  by_cases h : p = 2
  · subst p
    exact hTwo
  · exact @hOdd p ⟨hp'.1⟩ h hp'.2 (verified_numerators p hp'.1 hp'.2)

end OMA.R_RegularPrimes_small_regular_primes_R1
