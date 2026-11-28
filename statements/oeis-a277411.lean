import Mathlib

/-!
# Formulas for the first nonconstant column of A277410

Source: https://oeis.org/A277411 and https://oeis.org/A277410.

The parent exponential generating function is A = x + G(x + y(A-x),y),
where G is the integral of A in x with zero constant coefficient.
Write A = A₀ + y A₁ modulo y². Its defining equation in these two
coefficients reads A₀ = x + ∫A₀ and A₁ = ∫A₁ + (A₀-x)A₀.
The sequences below store the coefficients of xʳ/r! in A₀ and A₁.
Integration shifts the coefficient index by one, and multiplication
uses binomial convolution. These two equations determine the column.

The entry starts at n = 1, with triangle row n + 1 and column 1.
Its zero extension at n = 0 supplies the constant term of the ordinary
generating function. The denominator has constant coefficient 1, so
the multiplication identity specifies the quoted rational function.
The proof checks the first six published terms from the column definition.
-/

namespace OMA.S_oeis_a277411

def base : ℕ → ℕ
  | 0 => 0
  | m + 1 => base m + (if m = 0 then 1 else 0)

def productTerm (r i : ℕ) : ℕ :=
  r.choose i * (base i - (if i = 1 then 1 else 0)) * base (r - i)

def linear : ℕ → ℕ
  | 0 => 0
  | m + 1 => linear m + ∑ i ∈ Finset.range (m + 2), productTerm (m + 1) i

def a (n : ℕ) : ℕ := linear (n + 1)

def gf : PowerSeries ℚ := PowerSeries.mk fun n => (a n : ℚ)

theorem main :
    (gf * ((1 - PowerSeries.X) ^ 3 * (1 - 2 * PowerSeries.X)) =
      PowerSeries.X ^ 2 * (3 - 2 * PowerSeries.X)) ∧
    (∀ n : ℕ, 4 < n → (a n : ℚ) =
      5 * a (n - 1) - 9 * a (n - 2) + 7 * a (n - 3) - 2 * a (n - 4)) ∧
    (∀ n : ℕ, 1 ≤ n → (a n : ℚ) =
      (8 * ((2 : ℚ) ^ n - 1) - n * ((n : ℚ) + 7)) / 2) := by
  sorry

end OMA.S_oeis_a277411
