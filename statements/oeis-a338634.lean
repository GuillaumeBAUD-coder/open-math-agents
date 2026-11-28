import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Data.Fintype.Basic

/-!
# Parity in a continued fraction with fourth-power weights

Let U_j be the reciprocal of the nested denominator whose numerator below it
is (j+2)^4 x. The defining continued fraction of OEIS A338634 gives
A = 1 + x U_0 and U_j = 1 + x U_j ((j+2)^4 U_(j+1) - U_0).
The coefficient rule below determines each degree from lower degrees of the
tails. In particular it specifies the infinite fraction without choosing a
finite truncation or a convergence convention for numerical values of x.

Source: https://oeis.org/A338634
Credit: @hiattco
-/

namespace OMA.S_oeis_a338634

/-- The coefficient of x^n in the reciprocal of the jth nested denominator. -/
def invTailCoeff (n j : ℕ) : ℤ :=
  match n with
  | 0 => 1
  | d + 1 => ∑ i : Fin (d + 1), invTailCoeff i.val j *
      (((j : ℤ) + 2)^4 * invTailCoeff (d - i.val) (j + 1) - invTailCoeff (d - i.val) 0)
termination_by n
decreasing_by all_goals omega

/-- Coefficients of the generating function A = 1 + x U_0. -/
def a : ℕ → ℤ
  | 0 => 1
  | n + 1 => invTailCoeff n 0

theorem main : ∀ n : ℕ, 0 < n → (Odd (a n) ↔ ∃ k : ℕ, n = 2 ^ k) := by
  sorry

end OMA.S_oeis_a338634
