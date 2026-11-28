import FormalConjectures.OEIS.«69004»

/-!
# Reduction OeisA69004.conjecture1.R1

A069004: `a n` counts the positive integers `s < n` such that `n^2 + s^2` is prime.
Conjecture 1 says that `a n` is positive for every `n > 1`, i.e. every `n > 1` has such an `s`.

The statement quantifies over all `n > 1`, so it splits at a bound into

* `H1` -- the finite range `1 < n <= 100`: a finite, decidable verification (each case is a
  finite search over `s < n` together with a primality test).
* `H2` -- the tail `n > 100`: the open core of the conjecture.

`H1` and `H2` together cover exactly the range of the parent statement; `main` is the case
split on `n <= 100`.
-/

namespace OMA.R_OeisA69004_conjecture1_R1

open OeisA69004

/-- The finite range `1 < n <= 100`: finitely many explicit cases. -/
def H1 : Prop :=
  ∀ n : ℕ, 1 < n → n ≤ 100 → 0 < a n

/-- The tail `n > 100`: the open core of the conjecture. -/
def H2 : Prop :=
  ∀ n : ℕ, 100 < n → 0 < a n

theorem main : H1 → H2 → type_of% @OeisA69004.conjecture1 := by
  intro h1 h2 n hn
  by_cases h : n ≤ 100
  · exact h1 n hn h
  · exact h2 n (by omega)

end OMA.R_OeisA69004_conjecture1_R1
