import Mathlib

/-!
# A000928: the density of regular primes

Source: https://oeis.org/A000928
Credit: @jagraj28

A000928 lists the irregular primes: primes `p` such that at least one of the numerators of the
Bernoulli numbers `B_2, B_4, ..., B_{p-3}` is divisible by `p`. A prime that is not irregular is
regular. The entry quotes Ribenboim: it is a plausible conjecture that only an asymptotic fraction
`1/sqrt(e)` (about 0.6) of all primes are regular.

`main` states this conjecture: the number of regular primes `p ≤ x`, divided by the number of
primes `p ≤ x`, tends to `1 / sqrt e` as `x → ∞`.

Conventions:
* Mathlib's `bernoulli` has `B_1 = -1/2`, but only even indices `k ≥ 2` are used here, where it
  agrees with every other convention.
* For `p = 2` and `p = 3` the range `B_2, ..., B_{p-3}` is empty, so 2 and 3 are regular. This is
  the standard convention (Kummer's criterion for odd primes, and 2 is regular). It changes no
  limit, since it concerns only finitely many primes.
* The numerator of a rational number is taken in lowest terms (`Rat.num`), as in A000367.
-/

namespace OMA.S_oeis_a000928

open Filter Topology

/-- `p` is an irregular prime (OEIS A000928): `p` is prime and `p` divides the numerator of
`B_k` for some even `k` with `2 ≤ k ≤ p - 3`. -/
def IsIrregularPrime (p : ℕ) : Prop :=
  p.Prime ∧ ∃ k : ℕ, 2 ≤ k ∧ k ≤ p - 3 ∧ Even k ∧ (p : ℤ) ∣ (bernoulli k).num

/-- `p` is a regular prime: a prime that is not irregular. -/
def IsRegularPrime (p : ℕ) : Prop :=
  p.Prime ∧ ¬ IsIrregularPrime p

/-- The number of regular primes `p ≤ x`. -/
noncomputable def regularCount (x : ℕ) : ℕ :=
  {p : ℕ | p ≤ x ∧ IsRegularPrime p}.ncard

/-- Ribenboim's conjecture quoted in OEIS A000928: the proportion of regular primes among the
primes up to `x` tends to `1 / sqrt e`. -/
theorem main :
    Tendsto (fun x : ℕ => (regularCount x : ℝ) / (Nat.primeCounting x : ℝ)) atTop
      (𝓝 (1 / Real.sqrt (Real.exp 1))) := by
  sorry

end OMA.S_oeis_a000928
