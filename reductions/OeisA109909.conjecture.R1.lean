import FormalConjectures.OEIS.«109909»

-- Reduction OeisA109909.conjecture.R1 of Conjectures associated with A109909
-- Credit: @eltociear
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Primes of the form `k * (n - k) - 1`: the searched range and the open tail

`a n` counts the distinct primes among the values `k * (n - k) - 1` for `1 ≤ k < n`, and the
conjecture says that there is at least one such prime for every `n > 3`.

For a fixed `n` the conjecture is a finite statement: the candidates are `< n ^ 2 / 4`, so
deciding `a n > 0` needs only a primality test on finitely many explicit numbers. What is missing
is a uniform argument: the shifted quadratic `k * (n - k) - 1` ranges over an interval of length
about `n ^ 2 / 4`, and no known estimate (even under the Riemann hypothesis) guarantees a prime in
such a short interval for every `n`.

The OEIS entry A109909 records where the computation stops: Mauro Fiorentini verified the
conjecture up to `10 ^ 9` (comment of Jul 23 2023), and Pengcheng Niu and Junli Zhang study the
same two conjectures of Amarnath Murthy (ResearchGate, 2024). So the statement splits there:

* `H1` (searched range): `3 < n ≤ 10 ^ 9` has `a n > 0`. This is the finite part; each `n` is a
  bounded primality check, and the whole range was run as a computation rather than proved.
* `H2` (the open tail): `10 ^ 9 < n` has `a n > 0`. Nothing is known here; heuristically the
  number of prime values is about `n / (4 log n)`, so the statement is expected to be true with an
  enormous margin, but a proof for all `n` is out of reach of current interval-prime technology.

Neither hypothesis mentions the target, the other one, or `main`; `main` is the case split.
-/

namespace OMA.R_OeisA109909_conjecture_R1

/-- The searched range: every `n` with `3 < n ≤ 10 ^ 9` has a prime `k * (n - k) - 1`
(Fiorentini, OEIS A109909). -/
def H1 : Prop :=
  ∀ n : ℕ, 3 < n → n ≤ 1000000000 → 0 < OeisA109909.a n

/-- The open tail: no `n` above `10 ^ 9` is known, and no uniform bound is known either. -/
def H2 : Prop :=
  ∀ n : ℕ, 1000000000 < n → 0 < OeisA109909.a n

theorem main : H1 → H2 → type_of% @OeisA109909.conjecture := by
  intro h1 h2 n hn
  by_cases h : n ≤ 1000000000
  · exact h1 n hn h
  · exact h2 n (Nat.lt_of_not_le h)

end OMA.R_OeisA109909_conjecture_R1
