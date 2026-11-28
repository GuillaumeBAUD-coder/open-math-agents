import Mathlib

/-!
# A145376: least prime q with T(q*p_n) - q*p_n triangular (nondecreasing for n >= 2)

Source: https://oeis.org/A145376 (OEIS Foundation, CC BY-SA 4.0)
Credit: @trador01 (agent: Claude Code, model claude-opus-5-5)

A145376 (offset 1): if T(n) >= n is the nearest triangular number to n and p_n is the n-th prime,
then a(n) is the least prime such that T(a(n)*p_n) - a(n)*p_n is a triangular number; data
3, 2, 2, 2, 2, 3, 5, 5, 7, 11, 11, 11, 13, 17, ...

The entry records:

  Conjecture. For n>=2 the sequence is nondecreasing.
  The conjecture holds for the first 10000 terms. (Charles R Greathouse IV, Feb 21 2011)

Reading of the source:
* "T(x) >= x is the nearest triangular number to x" is the least triangular number that is at
  least `x`. Triangular numbers are `k(k+1)/2` for `k ≥ 0`, so 0 is triangular (this matches the
  data: a(1) = 3 since T(6) - 6 = 0, while T(4) - 4 = 6 - 4 = 2 is not triangular).
* `p_n` is the `n`-th prime with `p_1 = 2`, i.e. `Nat.nth Nat.Prime (n - 1)`.
* `a n` is the least prime `q` such that `T(q p_n) - q p_n` is triangular, written as `sInf` of
  that set of primes. The source does not prove that such a `q` exists for every `n` (the
  computed terms show it for the first 10000 values). If the set were empty at some index
  `m ≥ 3`, `sInf` would give `a m = 0 < a (m - 1)`, so `main` also implies that every term from
  n = 3 on is defined, as the source takes for granted.
* "For n>=2 the sequence is nondecreasing": `a n ≤ a (n + 1)` for every `n ≥ 2`.
-/

namespace OMA.S_oeis_a145376

/-- `x` is a triangular number `k(k+1)/2` (`k ≥ 0`, so 0 is triangular). -/
def IsTriangular (x : ℕ) : Prop := ∃ k : ℕ, x = k * (k + 1) / 2

/-- The least triangular number that is at least `x`. -/
noncomputable def triCeil (x : ℕ) : ℕ := sInf {t : ℕ | IsTriangular t ∧ x ≤ t}

/-- `p n`: the `n`-th prime, with `p 1 = 2`. -/
noncomputable def p (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

/-- A145376(n): the least prime `q` such that `triCeil (q p_n) - q p_n` is triangular. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {q : ℕ | q.Prime ∧ IsTriangular (triCeil (q * p n) - q * p n)}

/-- The conjecture: the sequence is nondecreasing from `n = 2` on. -/
theorem main : ∀ n : ℕ, 2 ≤ n → a n ≤ a (n + 1) := by
  sorry

end OMA.S_oeis_a145376
