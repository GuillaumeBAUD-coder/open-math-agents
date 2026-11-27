import Mathlib

/-!
# OEIS A036968: Genocchi numbers of the first kind as permanents

Source: https://oeis.org/A036968
Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

A036968 (offset 1) are the Genocchi numbers of the first kind, the coefficients `a(n)/n!`
of `2x/(exp(x)+1)`. Its comment records a conjecture of Zhi-Wei Sun (Sep 07 2021): for any
positive integer `n`, `-a(n+1)` is the permanent of the `n × n` matrix `M` with
`M(j,k) = floor((2j - k)/n)` for `j, k = 1..n`.

Conventions:
* `a(m)` is given by the OEIS formula `a(m) = 2 (1 - 2^m) B_m`, with Mathlib's `bernoulli`
  (`B_1 = -1/2`, the convention under which this formula matches the e.g.f.; only `m ≥ 2`
  is used here, where both Bernoulli conventions agree).
* Indices `j, k : Fin n` stand for `j + 1, k + 1 ∈ {1, …, n}`; the floor is the floor of the
  rational number `(2j - k)/n`, so it is the mathematical floor also for negative numerators.
* The permanent is Mathlib's `Matrix.permanent` over `ℤ`, compared in `ℚ`.

The conjecture was proved by Fu, Lin and Sun, arXiv:2109.11506 (cited in the OEIS entry);
this file only states it.
-/

namespace OMA.S_oeis_a036968

/-- Genocchi numbers of the first kind (A036968): `a(m) = 2 (1 - 2^m) B_m`. -/
def genocchi (m : ℕ) : ℚ := 2 * (1 - 2 ^ m) * bernoulli m

/-- Sun's matrix: `M(j,k) = floor((2j - k)/n)` for `j, k = 1..n` (0-based indices shifted by one). -/
def sunMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun j k => ⌊((2 * ((j : ℤ) + 1) - ((k : ℤ) + 1) : ℤ) : ℚ) / (n : ℚ)⌋

/-- For every positive integer `n`, `per M = -a(n+1)`. -/
theorem main : ∀ n : ℕ, 0 < n → ((sunMatrix n).permanent : ℚ) = -genocchi (n + 1) := by
  sorry

end OMA.S_oeis_a036968
