import Mathlib

/-!
# A037958: a(n) = binomial(n, floor((n-8)/2))

Source: https://oeis.org/A037958
Credit: @sntntHb

The sequence (offset 0: `0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 10, 11, 66, ...`) is
`a(n) = binomial(n, floor((n-8)/2))`, which is `0` for `n < 8` (the lower index is negative).
The entry records the conjecture (R. J. Mathar, Jul 26 2015, verified by Robert Israel, Jun 28 2018):
`Conjecture: -(n+9)*(n-8)*a(n) +2*(n)*a(n-1) + 4*n*(n-1)*a(n-2) = 0.`

The recurrence involves `a(n-2)`, so it is stated for `n ≥ 2` (offset 0). The identity is stated
over `ℤ`. Natural-number subtraction would turn `(n-8)/2` into `0` for `n < 8`, so the definition
sets `a n = 0` there explicitly, matching the listed terms.
-/

namespace OMA.S_oeis_a037958

/-- `a n = binomial(n, floor((n-8)/2))`, which is `0` for `n < 8` (OEIS A037958). -/
def a (n : ℕ) : ℕ := if n < 8 then 0 else Nat.choose n ((n - 8) / 2)

/-- R. J. Mathar's conjectured recurrence for OEIS A037958. -/
theorem main : ∀ n : ℕ, 2 ≤ n →
    -((n : ℤ) + 9) * ((n : ℤ) - 8) * (a n : ℤ) + 2 * (n : ℤ) * (a (n - 1) : ℤ) +
      4 * (n : ℤ) * ((n : ℤ) - 1) * (a (n - 2) : ℤ) = 0 := by
  sorry

end OMA.S_oeis_a037958
