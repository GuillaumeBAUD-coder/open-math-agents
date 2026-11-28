import Mathlib

/-!
# Is this bound on a Kummer function known?

Source: https://mathoverflow.net/questions/85023
Credit: @JeremyDevs

Question (MathOverflow 85023, 2012). Is it already known that
`₁F₁(a; b; x) ≤ Γ(b) (1 + |x|)^(-a)` when `a` is an integer, `a < 0`, and `b > 0`? If it is,
what is a reference?

The inequality is false (the answer at the source also says that the alleged inequality is
false). A counterexample within the stated range: `a = -1`, `b = 3/2`, `x = 0`. Indeed
`₁F₁(a; b; 0) = 1`, while `Γ(3/2) (1 + 0)^1 = √π / 2 < 1`; more generally `Γ(b) < 1` for all
`1 < b < 2`, so the bound already fails at `x = 0`. `main` states that the inequality does not
hold for all negative integers `a`, all `b > 0` and all real `x`.

Conventions:
* Write `a = -n` with `n` a positive integer. For such `a` the Kummer series
  `₁F₁(a; b; x) = ∑_k (a)_k / (b)_k * x^k / k!` terminates after the term `k = n`, and
  `kummerNeg n b x` is this finite sum; `(c)_k` is the rising factorial
  `(ascPochhammer ℝ k).eval c` (nonzero for `c = b > 0`).
* `(1 + |x|)^(-a)` is `(1 + |x|) ^ n`, and `Γ` is `Real.Gamma`.
-/

namespace OMA.S_mo_85023

/-- Kummer's confluent hypergeometric function `₁F₁(-n; b; x)` for a natural number `n`
(a terminating series). -/
noncomputable def kummerNeg (n : ℕ) (b x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1),
    (ascPochhammer ℝ k).eval (-(n : ℝ)) / (ascPochhammer ℝ k).eval b * x ^ k / (k.factorial : ℝ)

/-- The bound `₁F₁(a; b; x) ≤ Γ(b) (1 + |x|)^(-a)` fails for some negative integer `a = -n`,
some `b > 0` and some real `x`. -/
theorem main :
    ¬ ∀ (n : ℕ) (b x : ℝ), 0 < n → 0 < b →
      kummerNeg n b x ≤ Real.Gamma b * (1 + |x|) ^ n := by
  sorry

end OMA.S_mo_85023
