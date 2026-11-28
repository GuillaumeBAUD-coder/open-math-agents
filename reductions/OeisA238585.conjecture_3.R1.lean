import FormalConjectures.OEIS.«238585»

/-!
# Reduction OeisA238585.conjecture_3.R1

A238585 conjecture 3: for every `n > 2` with `n != 9` there is a prime `p < n` such that
`prime(n)^2 + (prime(p) - 1)^2` is prime, where `prime(m)` is the `m`-th prime.

The statement quantifies over all `n > 2`, so it splits at a bound into

* `H1` -- the finite range `2 < n <= 200`: a finite, decidable verification (each case is a
  finite search over the primes `p < n` together with a primality test).
* `H2` -- the tail `n > 200`: the open core of the conjecture.

`H1` and `H2` together cover exactly the range of the parent statement; `main` is the case
split on `n <= 200`.
-/

namespace OMA.R_OeisA238585_conjecture_3_R1

/-- The finite range `2 < n <= 200`: finitely many explicit cases. -/
def H1 : Prop :=
  ∀ n : ℕ, 2 < n → n ≠ 9 → n ≤ 200 →
    ∃ p : ℕ, p < n ∧ p.Prime ∧
      Nat.Prime (Nat.nth Nat.Prime (n - 1) ^ 2 + (Nat.nth Nat.Prime (p - 1) - 1) ^ 2)

/-- The tail `n > 200`: the open core of the conjecture. -/
def H2 : Prop :=
  ∀ n : ℕ, 200 < n →
    ∃ p : ℕ, p < n ∧ p.Prime ∧
      Nat.Prime (Nat.nth Nat.Prime (n - 1) ^ 2 + (Nat.nth Nat.Prime (p - 1) - 1) ^ 2)

theorem main : H1 → H2 → type_of% @OeisA238585.conjecture_3 := by
  intro h1 h2 n hn hn9
  by_cases h : n ≤ 200
  · exact h1 n hn hn9 h
  · exact h2 n (by omega)

end OMA.R_OeisA238585_conjecture_3_R1
