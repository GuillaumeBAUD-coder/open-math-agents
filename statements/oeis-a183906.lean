import Mathlib

/-!
# A183906: Number of nondecreasing arrangements of n+2 numbers in 0..3 with each number being the sum mod 4 of two others.

Source: https://oeis.org/A183906
Credit: @Salofe

Conjectures from Colin Barker, Apr 05 2018, quoted verbatim from the entry:
* "G.f.: x*(2 - 3*x + 9*x^2 - 8*x^3 - x^4 + 2*x^5) / (1 - x)^4."
* "a(n) = 4*a(n-1) - 6*a(n-2) + 4*a(n-3) - a(n-4) for n>6."

Formalization notes:
* Offset 1, as in the entry (data: 2, 5, 17, 38, 67, 105, 153, ...). The value of `a 0` is never
  used.
* An arrangement of n+2 numbers in 0..3 is a sequence `x 0, x 1, ..., x (n+1)` of values in
  `Fin 4`, i.e. a function `x : Fin (n + 2) → Fin 4`; nondecreasing means `Monotone x`.
* "Each number being the sum mod 4 of two others": for every position `i` there are two
  positions `j ≠ k`, both different from `i`, such that `(x j + x k) mod 4 = x i`, computed in
  `ℕ`. The two others are two other entries of the arrangement, so they sit at two distinct
  positions (equal values at different positions may be used). This reading reproduces the data:
  a brute-force count gives 2, 5, 17, 38, 67, 105, ..., whereas letting one position be used
  twice (allowing `j = k`) gives 3, 11, 25, 46, ...
* The g.f. is the ordinary one, Sum_{n>=1} a(n) x^n, written as `PowerSeries.mk` of the function
  that is 0 at n = 0 and a(n) for n ≥ 1. The identity is stated over `ℤ⟦X⟧`, cross-multiplied by
  the denominator `(1 - x)^4`, whose constant coefficient is 1.
* The recurrence is stated in `ℤ` for every n > 6, as in the entry.
-/

namespace OMA.S_oeis_a183906

open PowerSeries

/-- A nondecreasing arrangement `x 0 ≤ x 1 ≤ ... ≤ x (N - 1)` of numbers in `0..3` in which each
number is the sum mod 4 of two others: the entries at two distinct positions, both different from
its own position. -/
def Good {N : ℕ} (x : Fin N → Fin 4) : Prop :=
  Monotone x ∧
    ∀ i : Fin N, ∃ j k : Fin N, j ≠ i ∧ k ≠ i ∧ j ≠ k ∧ ((x j : ℕ) + (x k : ℕ)) % 4 = (x i : ℕ)

/-- A183906(n): the number of nondecreasing arrangements of `n + 2` numbers in `0..3` with each
number being the sum mod 4 of two others. -/
noncomputable def a (n : ℕ) : ℕ := Nat.card {x : Fin (n + 2) → Fin 4 // Good x}

/-- Barker's conjectures: the generating function
`x(2 - 3x + 9x^2 - 8x^3 - x^4 + 2x^5)/(1 - x)^4`, and the recurrence
`a(n) = 4a(n-1) - 6a(n-2) + 4a(n-3) - a(n-4)` for `n > 6`. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (a n : ℤ)) *
        ((1 - X) ^ 4 : PowerSeries ℤ) =
      X * (2 - 3 * X + 9 * X ^ 2 - 8 * X ^ 3 - X ^ 4 + 2 * X ^ 5) ∧
    ∀ n : ℕ, 6 < n →
      (a n : ℤ) = 4 * (a (n - 1) : ℤ) - 6 * (a (n - 2) : ℤ) + 4 * (a (n - 3) : ℤ) -
        (a (n - 4) : ℤ) := by
  sorry

end OMA.S_oeis_a183906
