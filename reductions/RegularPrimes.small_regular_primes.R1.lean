import FormalConjectures.Wikipedia.RegularPrimes

-- Reduction RegularPrimes.small_regular_primes.R1 of Infinite Regular Primes — small regular primes
-- Credit: @ihateSAS
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# The eleven small regular primes

That `2, 3, 5, …, 31` are regular is a finite verification, and it factors into two independent
inputs.

* `H1` is Kummer's criterion in general form: regularity of `p` is equivalent to `p` dividing the
  numerator of none of `B 2, B 4, …, B (p - 3)`.  This is the deep input (it is the statement
  `RegularPrimes.isRegularPrime_iff_Bernoulli` of the same file); it is used once per prime, at
  `p = 2, 3, …, 31`.
* `H2` is the concrete arithmetic: for each of the eleven primes and each even `k ≤ p - 3`, the
  numerator of `B k` is not divisible by `p`.  Only two Bernoulli numerators are involved, those of
  `B 2 = 1/6` and `B 4 = -1/30`, together with `B 6 = 1/42, …, B 28`, so `H2` is a finite
  computation with `decide`-style content, but it is genuinely separate from `H1`.

The reduction's content is the assembly: for each of the eleven primes, exhibit the primality
witness and rewrite regularity through `H1`, then discharge the Bernoulli side condition with `H2`.
-/

namespace OMA.R_RegularPrimes_small_regular_primes_R1

open scoped NumberField

/-- Kummer's criterion: `p` is regular exactly when it divides no numerator among
`B 2, B 4, …, B (p - 3)`. -/
def H1 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], RegularPrimes.IsRegularPrime p ↔
    ∀ k ∈ Finset.Icc 2 (p - 3), Even k → ¬ (p : ℤ) ∣ (bernoulli' k).num

/-- The Bernoulli numerators for the eleven primes below `37` are not divisible by the prime. -/
def H2 : Prop :=
  ∀ p ∈ ({2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31} : Finset ℕ),
    ∀ k ∈ Finset.Icc 2 (p - 3), Even k → ¬ (p : ℤ) ∣ (bernoulli' k).num

theorem main : H1 → H2 → type_of% @RegularPrimes.small_regular_primes := by
  intro h1 h2 p hp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    refine ⟨by norm_num, ?_⟩
    exact (@h1 _ ⟨by norm_num⟩).2 (h2 _ (by decide))

end OMA.R_RegularPrimes_small_regular_primes_R1
