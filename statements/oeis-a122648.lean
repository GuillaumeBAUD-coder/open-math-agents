import Mathlib

/-!
Source: https://oeis.org/A122648
Source text: https://github.com/oeis/oeisdata/blob/main/seq/A122/A122648.seq
Credit: @Heart-galaxy

The sequence is defined by the source's exponential generating function
exp(x^2)*(exp(2*x)+1)/2, using exact formal power-series substitution.
Thus a(n) is n! times the coefficient of x^n. Mathar's conjectured
recurrence is recorded as proved by Sela Fried on December 7, 2025:
https://oeis.org/A122648/a122648.pdf
The offset is zero. All five terms in the recurrence are in its domain
exactly when n >= 4. The coefficients and equality are taken in Q.
-/

namespace OMA.S_oeis_a122648
open PowerSeries

noncomputable def E : PowerSeries ℚ := (exp ℚ).subst (X^2)
noncomputable def H : PowerSeries ℚ := (exp ℚ).subst (C 2*X)
noncomputable def egf : PowerSeries ℚ := C (1/2:ℚ) * (E*(H+1))
noncomputable def a (n : ℕ) : ℚ := (Nat.factorial n : ℚ) * coeff n egf

theorem main : ∀ n : ℕ, 4 ≤ n →
    a n - 2*a (n-1)+2*(-2*(n:ℚ)+3)*a (n-2)+
      4*((n:ℚ)-2)*a (n-3)+4*((n:ℚ)-2)*((n:ℚ)-3)*a (n-4)=0 := by
  sorry

end OMA.S_oeis_a122648
