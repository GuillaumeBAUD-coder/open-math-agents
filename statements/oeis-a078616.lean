import Mathlib

/-!
# A078616: a(n) = Sum_{k=0..n} A010815(k).

Source: https://oeis.org/A078616
Credit: @Mapika (AI-assisted: Claude Code, model claude-opus-5-5).

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.

## The conjecture

OEIS A078616, offset 0, COMMENTS line:

> From George Beck, May 05 2017: (Start)
> a(n) = (Number of ones in the distinct partitions of n with an odd number of parts) -
> (number of ones in the distinct partitions of n with an even number of parts) (conjectured).
> The partial sums give A246575. (End) [corrected by Ilya Gutkovskiy, Aug 18 2018]

## Modelling choices

* A010815(k) is the coefficient of `q^k` in `Product_{m>=1} (1 - q^m)` (Euler's pentagonal
  number theorem; offset 0). Factors with `m > k` do not change that coefficient, so
  `A010815 k` is computed as the coefficient of `X^k` in `Product_{m=1..k} (1 - X^m)` in
  `Polynomial ℤ`. Then `a n = Sum_{k=0..n} A010815 k` reproduces the DATA line
  (`1, 0, -1, -1, -1, 0, 0, 1, 1, 1, 1, 1, 0, ...`).
* A distinct partition of `n` is a `p : Nat.Partition n` with `p.parts.Nodup`; its number of
  parts is `Multiset.card p.parts` and its number of ones is `p.parts.count 1` (0 or 1 for a
  distinct partition). The two counts are natural numbers and their difference is taken in `ℤ`.
* The source gives no range; the identity is stated for every `n` in the offset of the entry
  (`n ≥ 0`).
-/

namespace OMA.S_oeis_a078616

open Polynomial

/-- A010815: coefficient of `q^k` in `Product_{m>=1} (1 - q^m)`. -/
noncomputable def A010815 (k : ℕ) : ℤ :=
  (∏ m ∈ Finset.range k, (1 - (X : ℤ[X]) ^ (m + 1))).coeff k

/-- A078616. -/
noncomputable def a (n : ℕ) : ℤ := ∑ k ∈ Finset.range (n + 1), A010815 k

/-- Number of ones in the distinct partitions of `n` with an odd number of parts. -/
def onesOdd (n : ℕ) : ℕ :=
  ∑ p ∈ Finset.univ.filter (fun p : Nat.Partition n =>
    p.parts.Nodup ∧ Odd (Multiset.card p.parts)), p.parts.count 1

/-- Number of ones in the distinct partitions of `n` with an even number of parts. -/
def onesEven (n : ℕ) : ℕ :=
  ∑ p ∈ Finset.univ.filter (fun p : Nat.Partition n =>
    p.parts.Nodup ∧ Even (Multiset.card p.parts)), p.parts.count 1

/-- George Beck's conjecture (May 05 2017, as corrected Aug 18 2018). -/
theorem main : ∀ n : ℕ, a n = (onesOdd n : ℤ) - onesEven n := by
  sorry

end OMA.S_oeis_a078616
