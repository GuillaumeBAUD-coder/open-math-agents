import Mathlib

/-!
# A216275: "Fibonacci + Goldbach" (the ratio of consecutive terms tends to the golden ratio)

Source: https://oeis.org/A216275 (OEIS Foundation, CC BY-SA 4.0)
Credit: @trador01 (agent: Claude Code, model claude-opus-5-5)

A216275 (offset 1): Fibonacci + Goldbach: a(1)=6, a(2)=8 and for n>=3,
a(n)=g(a(n-1)) + g(a(n-2)), where for m>=3, g(2*m) is the maximal prime p < 2*m such that
2*m - p is prime; data 6, 8, 8, 10, 12, 14, 18, 24, 32, 48, 72, 110, ...
(a(6) = g(10) + g(12) = 7 + 7 = 14).

The entry records:

  Conjecture. lim a(n+1)/a(n)=phi as n goes to infinity (phi=golden ratio).

Reading of the source:
* `g x` is the largest prime `p < x` such that `x - p` is prime. It is applied to terms of the
  sequence, which are even numbers ≥ 6; that such a `p` exists for them is the Goldbach property
  the name refers to. It is written as `sSup` of that (finite) set of primes.
* `a 1 = 6`, `a 2 = 8`, and `a n = g(a(n-1)) + g(a(n-2))` for `n ≥ 3`; `a 0` is not part of the
  source and is set to 0 (unused).
* The conjecture: `a(n+1)/a(n) → φ` in `ℝ` (`φ = Real.goldenRatio`).
-/

namespace OMA.S_oeis_a216275

open Filter Topology

/-- `g x`: the largest prime `p < x` with `x - p` prime. -/
noncomputable def g (x : ℕ) : ℕ := sSup {p : ℕ | p.Prime ∧ p < x ∧ (x - p).Prime}

/-- A216275: `a(1) = 6`, `a(2) = 8`, `a(n) = g(a(n-1)) + g(a(n-2))` for `n ≥ 3`. -/
noncomputable def a : ℕ → ℕ
  | 0 => 0
  | 1 => 6
  | 2 => 8
  | n + 3 => g (a (n + 2)) + g (a (n + 1))

/-- The conjecture: `a(n+1)/a(n) → φ`. -/
theorem main :
    Tendsto (fun n : ℕ => (a (n + 1) : ℝ) / a n) atTop (𝓝 Real.goldenRatio) := by
  sorry

end OMA.S_oeis_a216275
