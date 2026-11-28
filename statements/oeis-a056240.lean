import Mathlib

/-!
# A056240: Smallest number whose prime divisors (taken with multiplicity) add to n.

Source: https://oeis.org/A056240
Credit: @<your GitHub handle>

The entry records (David James Sycamore and Michel Marcus, Jun 16 2017, Jun 28 2017):
"Recursive calculation of a(n): For prime p, a(p) = p. For even composite n, let P_n denote the
largest prime < n-1 such that n-P_n is prime (except if n = 6). For odd composite n, let P_n denote
the largest prime < n-1 such that n-3-P_n is prime. Conjecture: a(n) = min { q*a(n-q); q prime,
P_n <= q < n-1 }."

Conventions (please review):
* `sopfr m` (A001414) is the sum of the prime factors of `m` with multiplicity,
  `(Nat.primeFactorsList m).sum`. `a(n)` (offset 2) is the least `m` with `sopfr m = n`
  (it exists for every `n ≥ 2`, e.g. a product of 2's and at most one 3).
* "Composite" means `n ≥ 2` and not prime; `n = 6` is excluded as in the source.
* `P_n` is "the largest prime `< n-1`" with the stated property; we take it as a hypothesis
  (`IsGreatest`), so the conjecture is asserted whenever `P_n` exists. (For even `n` its existence
  is a Goldbach-type statement; the source presupposes it.)
* `n - 3 - p` uses truncated subtraction; this is harmless since `0` and `1` are not prime.
* The minimum is over the primes `q` with `P_n ≤ q < n - 1`; this set contains `P_n`, and
  `n - q ≥ 2` so `a(n - q)` is defined.
-/

namespace OMA.S_oeis_a056240

/-- A001414: sum of the prime factors of `m`, with multiplicity. -/
def sopfr (m : ℕ) : ℕ := (Nat.primeFactorsList m).sum

/-- A056240: the smallest number whose prime divisors (with multiplicity) add to `n`. -/
noncomputable def a (n : ℕ) : ℕ := sInf {m : ℕ | sopfr m = n}

/-- The defining property of `P_n`: `p` is a prime `< n - 1` such that `n - p` is prime (for even
`n`), resp. `n - 3 - p` is prime (for odd `n`). -/
def PCandidate (n p : ℕ) : Prop :=
  p.Prime ∧ p < n - 1 ∧ (if Even n then (n - p).Prime else (n - 3 - p).Prime)

/-- The Sycamore–Marcus conjecture in OEIS A056240: for composite `n ≠ 6`, with `P_n` the largest
prime `< n - 1` as above, `a(n) = min { q * a(n - q) : q prime, P_n ≤ q < n - 1 }`. -/
theorem main : ∀ n : ℕ, 2 ≤ n → ¬ n.Prime → n ≠ 6 → ∀ P : ℕ, IsGreatest {p | PCandidate n p} P →
    a n = sInf {x : ℕ | ∃ q : ℕ, q.Prime ∧ P ≤ q ∧ q < n - 1 ∧ x = q * a (n - q)} := by
  sorry

end OMA.S_oeis_a056240
