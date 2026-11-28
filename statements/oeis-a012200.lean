import Mathlib

/-!
# A012200: Expansion of arctanh(arctan(arcsin(x)))

Source: https://oeis.org/A012200
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Draft from an earlier generic agent run; audited against the source and re-checked before submission.

Conjecture:
Let `a(n)` be the coefficient of `x^(2*n + 1) / (2*n + 1)!` in the Taylor expansion of
`arctanh(arctan(arcsin(x))) = x + 1/3!*x^3 + 17/5!*x^5 + 393/7!*x^7 + 25601/9!*x^9 + ...`.
Then `a(n) ~ (2*n)! / (sin(tan(1)))^(2*n + 1)` as `n → ∞`.

Conventions:
- `artanh x` is defined as `(1 / 2) * Real.log ((1 + x) / (1 - x))`.
- `a(n)` is given by `iteratedDeriv (2 * n + 1) (fun x => artanh (Real.arctan (Real.arcsin x))) 0`.
- Asymptotic equivalence `a(n) ~ b(n)` is expressed as `a(n) / b(n) → 1` as `n → ∞`.
-/

namespace OMA.S_oeis_a012200

noncomputable def artanh (x : ℝ) : ℝ :=
  (1 / 2 : ℝ) * Real.log ((1 + x) / (1 - x))

noncomputable def aSeq (n : ℕ) : ℝ :=
  iteratedDeriv (2 * n + 1) (fun x => artanh (Real.arctan (Real.arcsin x))) 0

theorem main :
    Filter.Tendsto
      (fun n : ℕ =>
        aSeq n / ((Nat.factorial (2 * n) : ℝ) / (Real.sin (Real.tan 1)) ^ (2 * n + 1)))
      Filter.atTop (nhds 1) := by
  sorry

end OMA.S_oeis_a012200
