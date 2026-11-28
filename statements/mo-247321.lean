import Mathlib

/-!
# Increasing derivatives of recursively defined polynomials

Source: https://mathoverflow.net/questions/247321 (CC BY-SA 4.0).

Let `f_0(x) = x` and `f_{n+1}(x) = f_n(x) - f_n'(x) x (1 - x)`. All roots of `f_n` lie in `[0, 1)`;
let `x_n` be the largest root of `f_n`. The asker wants to prove `f_n'(x) > f_{n-1}'(x)` for all
`x ∈ [x_{n+1}, 1)`.

We state the conjecture for `n ≥ 2`.

Formalization notes:
* The polynomials are given as any `f : ℕ → ℝ[X]` satisfying the recursion (which determines them).
* `x ≥ x_{n+1}` is written as "every real root of `f_{n+1}` is `≤ x`" (roots exist: `f_{n+1}(0) = 0`).
* For `n = 1` the strict inequality fails: `x_2 = 1/2` and `f_1'(1/2) = f_0'(1/2) = 1`. The asker's
  worked cases start at `f_2' - f_1'`, so we take `n ≥ 2`.
* Checked numerically for `2 ≤ n ≤ 15` (on a fine grid of `[x_{n+1}, 1)`): the difference is positive.
-/

namespace OMA.S_mo_247321

/-- For `n ≥ 2` and `x_{n+1} ≤ x < 1`, `f_{n-1}'(x) < f_n'(x)`. -/
theorem main :
    ∀ (f : ℕ → Polynomial ℝ) (h0 : f 0 = Polynomial.X)
      (hrec : ∀ n, f (n + 1) = f n - Polynomial.derivative (f n) * Polynomial.X * (1 - Polynomial.X))
      (n : ℕ) (hn : 2 ≤ n) (x : ℝ) (hx1 : x < 1) (hx : ∀ y : ℝ, (f (n + 1)).IsRoot y → y ≤ x),
    (Polynomial.derivative (f (n - 1))).eval x < (Polynomial.derivative (f n)).eval x := by
  sorry

end OMA.S_mo_247321
