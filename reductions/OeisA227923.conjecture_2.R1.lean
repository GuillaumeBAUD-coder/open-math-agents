import FormalConjectures.OEIS.«227923»

/-!
# Reduction OeisA227923.conjecture_2.R1

A227923 conjecture 2: every `n > 4` with `n != 13` is a sum `x + y` of two distinct integers
`x, y > 1` such that `6x - 1`, `12x - 1`, `6y - 1` and `6y + 1` are all prime.

The statement quantifies over all `n > 4`, so it splits at a bound into

* `H1` -- the finite range `4 < n <= 204`: a finite, decidable verification (each case is a
  finite search over the splits `n = x + y` together with primality tests).
* `H2` -- the tail `n > 204`: the open core of the conjecture.

`H1` and `H2` together cover exactly the range of the parent statement; `main` is the case
split on `n <= 204`.
-/

namespace OMA.R_OeisA227923_conjecture_2_R1

/-- The finite range `4 < n <= 204`: finitely many explicit cases. -/
def H1 : Prop :=
  ∀ n : ℕ, 4 < n → n ≠ 13 → n ≤ 204 →
    ∃ x y : ℕ, 1 < x ∧ 1 < y ∧ x ≠ y ∧ x + y = n ∧
      (6 * x - 1).Prime ∧ (12 * x - 1).Prime ∧
      (6 * y - 1).Prime ∧ (6 * y + 1).Prime

/-- The tail `n > 204`: the open core of the conjecture. -/
def H2 : Prop :=
  ∀ n : ℕ, 204 < n →
    ∃ x y : ℕ, 1 < x ∧ 1 < y ∧ x ≠ y ∧ x + y = n ∧
      (6 * x - 1).Prime ∧ (12 * x - 1).Prime ∧
      (6 * y - 1).Prime ∧ (6 * y + 1).Prime

theorem main : H1 → H2 → type_of% @OeisA227923.conjecture_2 := by
  intro h1 h2 n hn h13
  by_cases h : n ≤ 204
  · exact h1 n hn h13 h
  · exact h2 n (by omega)

end OMA.R_OeisA227923_conjecture_2_R1
