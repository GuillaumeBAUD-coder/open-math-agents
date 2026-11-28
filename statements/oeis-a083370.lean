import Mathlib

/-!
# A083370: Primes satisfying f(2p)=p when f(1)=5 (see comment).

Source: https://oeis.org/A083370
Credit: @gblacher2

The comment of A083370 reads: "Start from any initial value f(1) >= 2 and define f(n) to be the
largest prime factor of f(1)+f(2)+...+f(n-1). Conjecture: f(n) = n/2 + O(log(n)) and there are
infinitely many primes p such that f(2p)=p." The sequence itself lists the primes `p` with
`f(2p) = p` for the start `f(1) = 5`.

Formalization notes:
* Since the comment defines `f` for any initial value `f(1) = m ≥ 2` and states the conjecture
  for that `f`, the statement quantifies over all `m ≥ 2` (the case `m = 5` is A083370; the same
  conjecture is stated for every start in A076973).
* `f m n` is the `n`-th term (indexed from 1) of the sequence started at `f(1) = m`; the value
  `f m 0` is an unused junk value.
* `n/2 + O(log n)` is read as `(f(n) - n/2) =O[atTop] log n` over the reals.
* With this definition and `m = 5`, the primes `p ≤ 25771` with `f(2p) = p` are exactly the 2000
  terms of the b-file of A083370 (computed by direct iteration).
-/

namespace OMA.S_oeis_a083370

/-- The largest prime factor of `k` (`0` when `k` has no prime factor). -/
def largestPrimeFactor (k : ℕ) : ℕ :=
  k.primeFactors.sup id

/-- `termAndSum m n = (f(n+1), f(1) + ⋯ + f(n+1))` for the sequence with `f(1) = m`. -/
def termAndSum (m : ℕ) : ℕ → ℕ × ℕ
  | 0 => (m, m)
  | n + 1 =>
    let s := (termAndSum m n).2
    (largestPrimeFactor s, s + largestPrimeFactor s)

/-- `f m n` is the `n`-th term (`n ≥ 1`) of the sequence with `f(1) = m` and `f(n)` the
largest prime factor of `f(1) + ⋯ + f(n-1)`. -/
def f (m n : ℕ) : ℕ :=
  (termAndSum m (n - 1)).1

/-- The conjecture stated in A083370: for every start `f(1) = m ≥ 2`, `f(n) = n/2 + O(log n)`
and there are infinitely many primes `p` with `f(2p) = p`. -/
theorem main : ∀ m : ℕ, 2 ≤ m →
    ((fun n : ℕ => (f m n : ℝ) - (n : ℝ) / 2) =O[Filter.atTop] fun n : ℕ => Real.log n) ∧
      {p : ℕ | p.Prime ∧ f m (2 * p) = p}.Infinite := by
  sorry

end OMA.S_oeis_a083370
