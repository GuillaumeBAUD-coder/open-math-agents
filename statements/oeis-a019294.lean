import Mathlib

/-!
# A019294: iterating sigma until a multiple of the start

Source: https://oeis.org/A019294
Credit: @jagraj28

A019294: `a(n)` is the number (`> 0`) of iterations of `sigma` (the sum of divisors) required to
reach a multiple of `n` when starting with `n` (1, 2, 4, 2, 5, 1, 5, 2, 7, 4, ...). The entry
records two conjectures:
1. the sequence is finite for all `n`, that is, `a(n)` exists: for every `n ≥ 1` some iterate
   `sigma^k(n)` with `k ≥ 1` is a multiple of `n`;
2. (Benoit Cloitre, 2002) `lim_{n → ∞} log(Sum_{k=1..n} a(k)) / log(n) = C = 1.6...`.

`main` is the conjunction of the two.

Conventions:
* `a(n)` is the least `k ≥ 1` with `n ∣ sigma^k(n)`; it is used in conjecture 2, where
  conjecture 1 makes it well defined. This reproduces the listed terms.
* `C = 1.6...` is read as: the limit `C` exists and its decimal expansion begins `1.6`, that is
  `1.6 ≤ C < 1.7`.
-/

namespace OMA.S_oeis_a019294

open Filter Topology

/-- `sigma n`: the sum of the divisors of `n` (OEIS A000203). -/
def sigma (n : ℕ) : ℕ := ∑ d ∈ n.divisors, d

/-- `a n`, OEIS A019294: the least `k ≥ 1` such that `n` divides the `k`-th iterate of `sigma`
at `n`. -/
noncomputable def a (n : ℕ) : ℕ := sInf {k : ℕ | 1 ≤ k ∧ n ∣ sigma^[k] n}

/-- The two conjectures of OEIS A019294. -/
theorem main :
    (∀ n : ℕ, 1 ≤ n → ∃ k : ℕ, 1 ≤ k ∧ n ∣ sigma^[k] n) ∧
    (∃ C : ℝ, 1.6 ≤ C ∧ C < 1.7 ∧
      Tendsto (fun n : ℕ => Real.log (∑ k ∈ Finset.Icc 1 n, (a k : ℝ)) / Real.log n) atTop
        (𝓝 C)) := by
  sorry

end OMA.S_oeis_a019294
