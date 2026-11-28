import FormalConjectures.OEIS.«110835»

-- Reduction OeisA110835.conjecture.R1 of Smallest $m > 0$ such that there are no primes between $nm$ and $n(m+1)$ inclusive.
-- Credit: @eltociear
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Sierpinski's bound `a n ≥ n`: the computed range and the open tail

`a n` is the smallest `m > 0` for which the inclusive interval `[n * m, n * (m + 1)]` contains no
prime, and Sierpinski's conjecture (1958) is exactly that `a n ≥ n` for every `n > 0`. The statement
is a finite search for each fixed `n`: one scans `m = 1, 2, 3, …` and stops at the first prime-free
window of the progression `n, 2n, 3n, …`, so `a n ≥ n` says that the first prime-free window is not
one of the first `n - 1` windows.

The OEIS entry A110835 records the computed range as a table of `a n` for `n = 1..599`
(Charles R Greathouse IV). Recomputing that table from the definition (sieve of Eratosthenes up to
`3 * 10 ^ 6`, scanning the first prime at or above `n * m` for each `m`) reproduces the listed terms,
for instance `a 1 = 8`, `a 2 = 4`, `a 3 = 8`, `a 4 = 6`, `a 5 = 18`; over the range the smallest value
of `a n - n` is `2` (at `n = 2` and `n = 4`) and the largest `a n` is `26549` (at `n = 113`). So the
statement splits at the end of the tabulated range:

* `H1` (computed range): `0 < n ≤ 599` has `a n ≥ n`. Finite, one search per `n`.
* `H2` (the open tail): `599 < n` has `a n ≥ n`. This is the conjecture itself; no proof is known
  for any infinite range, and it implies Oppermann's conjecture that each interval `(n ^ 2, n (n + 1))`
  and `(n (n + 1), (n + 1) ^ 2)` contains a prime.

Neither hypothesis mentions the target, the other one, or `main`; `main` is the case split.
-/

namespace OMA.R_OeisA110835_conjecture_R1

/-- The computed range: `a n ≥ n` for every `n` with `0 < n ≤ 599` (table in OEIS A110835). -/
def H1 : Prop :=
  ∀ n : ℕ, 0 < n → n ≤ 599 → OeisA110835.a n ≥ n

/-- The open tail: `a n ≥ n` from `600` on; this is Sierpinski's conjecture itself. -/
def H2 : Prop :=
  ∀ n : ℕ, 599 < n → OeisA110835.a n ≥ n

theorem main : H1 → H2 → type_of% @OeisA110835.conjecture := by
  intro h1 h2 n hn
  by_cases h : n ≤ 599
  · exact h1 n hn h
  · exact h2 n (Nat.lt_of_not_le h)

end OMA.R_OeisA110835_conjecture_R1
