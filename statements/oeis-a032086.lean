import Mathlib

/-!
Source: https://oeis.org/A032086
Source text: https://github.com/oeis/oeisdata/blob/main/seq/A032/A032086.seq
Credit: @Heart-galaxy

All four conjectured formulas imported by the API are retained. Howroyd
records them as true (October 10, 2017). The sequence is defined by the
independent exact formula of Russell and Rorabaugh (June 22, 2018), with
a(1)=3; a(0)=0 is the zero constant coefficient of its ordinary g.f.
The g.f. is expressed after multiplication by its denominator, whose
constant coefficient is one, and expansion of its numerator.
-/

namespace OMA.S_oeis_a032086

def a (n : ℕ) : ℚ :=
  if n = 0 then 0 else if n = 1 then 3 else
    ((3:ℚ)^n - (3:ℚ)^((n+1)/2))/2

def series : PowerSeries ℚ := PowerSeries.mk a

theorem main :
    (∀ n : ℕ, 4 < n → a n = 3*a (n-1)+3*a (n-2)-9*a (n-3)) ∧
    (((1-PowerSeries.C 3*PowerSeries.X)*(1-PowerSeries.C 3*PowerSeries.X^2))*series =
      PowerSeries.C 3*PowerSeries.X - PowerSeries.C 6*PowerSeries.X^2 -
        PowerSeries.C 9*PowerSeries.X^3 + PowerSeries.C 27*PowerSeries.X^4) ∧
    (∀ n : ℕ, 2 < n → Even n →
      a n = (2*(3:ℚ)^n - 2*(3:ℚ)^(n/2))/4) ∧
    (∀ n : ℕ, 2 < n → Odd n →
      a n = (2*(3:ℚ)^n - 2*(3:ℚ)^((n+1)/2))/4) := by
  sorry

end OMA.S_oeis_a032086
