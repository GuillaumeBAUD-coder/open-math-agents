import Mathlib

/-!
# Two recurrences for OEIS A129833

R. J. Mathar posed both recurrences on February 28, 2015.
Source: https://oeis.org/A129833 (OEIS Foundation, CC BY-SA 4.0).
Credit: @connoranderson
-/

namespace OMA.S_oeis_a129833

/-- The factorial-binomial sum defining A129833, with offset zero. -/
def a (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (n+1),
    ((n+1).choose (k+1) : ℚ) * (n.choose k : ℚ) * (k.factorial : ℚ)

theorem main :
    (∀ n : ℕ, 5 ≤ n → let t : ℚ := n
      (t+1)*a n - t*(2*t+5)*a (n-1) + (t-1)*(t^2+6*t+3)*a (n-2) -
        (t-2)*(3*t^2-2)*a (n-3) + (t-2)*(t-3)*(3*t-4)*a (n-4) -
        (t-4)*(t-3)^2*a (n-5) = 0) ∧
    (∀ n : ℕ, 3 ≤ n → let t : ℚ := n
      (t+1)*(t^2-4*t+2)*a n - t*(2*t^3-5*t^2-6*t+3)*a (n-1) +
        t*(t-1)*(t^3-2*t^2-2*t-2)*a (n-2) -
        (t-2)*(t^2-2*t-1)*(t-1)^2*a (n-3) = 0) := by
  sorry

end OMA.S_oeis_a129833
