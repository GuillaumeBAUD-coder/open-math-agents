import Mathlib

/-!
# Are there infinitely many primes of the form `x^2+(x+y)y^2`?

Source: https://mathoverflow.net/questions/360182 (Zhi-Wei Sun, 2020).
Credit: @jagraj28

Question 1 of the post (its title): are there infinitely many primes of the form
`x ^ 2 + x y ^ 2 + y ^ 3 = x ^ 2 + (x + y) y ^ 2` with positive integers `x, y`? The post notes
that Sun's conjecture A232174 (formalized upstream as `OeisA232174.conjecture`) implies a
positive answer; comments note that the Friedlander–Iwaniec methods do not apply to this form.
The post has no answer.

Formalization notes:
* `x` and `y` are positive integers, as in the post (`x, y ∈ ℤ⁺`).
* `main` states the affirmative answer to Question 1. Question 2 of the post (primes
  `p ^ 3 + (p + q) q ^ 2` with `p` prime), added later, is a separate question and is not stated.
* There are 5855 primes of this form below `10 ^ 6`.
-/

namespace OMA.S_mo_360182

/-- There are infinitely many primes `x ^ 2 + (x + y) * y ^ 2` with `x, y ≥ 1`. -/
theorem main :
    {p : ℕ | p.Prime ∧ ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ p = x ^ 2 + (x + y) * y ^ 2}.Infinite := by
  sorry

end OMA.S_mo_360182
