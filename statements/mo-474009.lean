import Mathlib

/-!
# Does there exist a polynomial that extracts the highest digit of an integer in base p?

Source: https://mathoverflow.net/questions/474009
Credit: @ivillar

Status: this entry covers the "result mod `p`" version of the question, whose answer is no.
The reason is elementary (it is the obstruction pointed out in the comments: integer-coefficient
polynomials cannot realise arbitrary functions, since `a - b` divides `f(a) - f(b)`): `0` and
`p^(n-1)` are congruent mod `p` but have highest digits `0` and `1`. The other version in the
question (result taken mod `p^n`) is not part of this statement.

Given an odd prime $p$, a positive integer $1 \lt n$, and an integer
$x \in \mathbb{Z}/p^n\mathbb{Z}$ (meaning $0 \le x < p^n$, as clarified in the comments), does
there exist an integer-coefficient polynomial that extracts the highest digit of $x$? The
extracted digit can be either $\bmod p^n$ or $\bmod p$. [...] If the result is $\bmod p$, then
$f(x)$ maps $x=(x_{n-1},x_{n-2},\ldots,x_1,x_0)$ to $x_{n-1}$. Does either of these polynomials
$f(x)$ exist?

Formalization notes:
* The highest base-`p` digit of `0 ≤ x < p ^ n` is `x / p ^ (n - 1)`.
* `main` states that no `f : ℤ[X]` satisfies `f(x) ≡ x / p ^ (n - 1) (mod p)` for all
  `0 ≤ x < p ^ n`.
-/

namespace OMA.S_mo_474009

theorem main : ∀ (p n : ℕ), p.Prime → Odd p → 1 < n →
    ¬ ∃ f : Polynomial ℤ, ∀ x : ℕ, x < p ^ n →
      f.eval (x : ℤ) ≡ ((x / p ^ (n - 1) : ℕ) : ℤ) [ZMOD (p : ℤ)] := by
  sorry

end OMA.S_mo_474009
