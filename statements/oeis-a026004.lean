import Mathlib

/-!
# A026004: a(n) = T(3n+1,n), where T = Catalan triangle (A008315).

Source: https://oeis.org/A026004
Credit: @<your GitHub handle>

The entry records the conjectured generating function (Harvey P. Dale, Jun 30 2011):
"G.f.: ((sqrt(x)*sin(2/3*arcsin((3*sqrt(3)*sqrt(x))/2)))/sqrt(4/3-9*x)
        -cos(1/3*arccos(1-(27*x)/2))+1)/(3*x)."

Conventions (please review):
* `T` is the Catalan triangle A008315, `T(n,k) = C(n,k) - C(n,k-1)` (with `C(n,-1) = 0`), so
  `a(n) = T(3n+1, n) = C(3n+1, n) - C(3n+1, n-1)` for `n ≥ 1` and `a(0) = 1`
  (`1, 3, 14, 75, 429, 2548, ...`). Computed in `ℤ`.
* The proposed g.f. involves `sqrt(x)` and a division by `x`, so it is not a formal power series
  expression as written; we read the claim analytically: for every real `x` with
  `0 < x < 4/27` (`4/27` is the radius of convergence of `Sum a(n) x^n`; it is also where `4/3 - 9x`
  vanishes and where `3√3√x/2 = 1`), the series
  `Sum_{n ≥ 0} a(n) x^n` converges to the stated closed form. On this interval every square root
  argument is positive and the `arcsin`, `arccos` arguments lie in `[-1, 1]`, so the real
  functions `Real.sqrt`, `Real.arcsin`, `Real.arccos` agree with the intended ones. Since the
  g.f. is analytic at `0`, agreement on this interval determines it.
-/

namespace OMA.S_oeis_a026004

/-- A026004: `a(n) = T(3n+1, n)` with `T(n,k) = C(n,k) - C(n,k-1)` the Catalan triangle A008315. -/
def a (n : ℕ) : ℤ :=
  (Nat.choose (3 * n + 1) n : ℤ) - (if n = 0 then 0 else (Nat.choose (3 * n + 1) (n - 1) : ℤ))

/-- Dale's proposed closed form for the generating function. -/
noncomputable def G (x : ℝ) : ℝ :=
  ((Real.sqrt x * Real.sin (2 / 3 * Real.arcsin (3 * Real.sqrt 3 * Real.sqrt x / 2))) /
      Real.sqrt (4 / 3 - 9 * x) -
    Real.cos (1 / 3 * Real.arccos (1 - 27 * x / 2)) + 1) / (3 * x)

/-- Dale's conjecture in OEIS A026004: `Sum a(n) x^n = G(x)` for `0 < x < 4/27`. -/
theorem main : ∀ x : ℝ, 0 < x → x < 4 / 27 → HasSum (fun n : ℕ => (a n : ℝ) * x ^ n) (G x) := by
  sorry

end OMA.S_oeis_a026004
