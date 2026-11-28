import Mathlib

/-!
# OEIS A214970: L(2k-1) and L(2k)+1 divide their change-of-base images

Source: https://oeis.org/A214970 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Clark Kimberling, Oct 17 2012), offset 1: Integers n that divide f(n), where f is the
change-of-base function defined at A214969, using b = (golden ratio) and c=b^2.
Conjecture: L(2k-1) and L(2k)+1 are terms of the sequence, for all positive integers k, where
L=A000032 (Lucas numbers).
Data: 1, 4, 8, 11, 19, 22, 29, 48, 55, 58, 76, 124, 152, 192, 199, ...
Example: 8 = r^4 + 1/r^4, where r = (1 + sqrt(5))/2 (the golden ratio), so f(8) = r^8 + 1/r^8 = 48,
so 8 divides f(8).
A214969 (Clark Kimberling), defining the change-of-base function: Suppose that b>1 and c>1, and for
x>=0 given by the greedy algorithm as x = sum{d(i)*b^i}, define f(x) = sum{d(i)*c^i}.
A000032: Lucas numbers beginning at 2: L(n) = L(n-1) + L(n-2), L(0) = 2, L(1) = 1.

Formalization notes:
* The greedy algorithm for x > 0 in base b > 1 starts at the exponent `top b x` of the largest
  power of b not exceeding x and goes down through all integer exponents: at exponent
  `top b x - k` the digit is `digit b x k`, the floor of the current remainder `rem b x k` divided
  by that power, and the remainder drops by the digit times the power.
* `chg b c x` is f(x) = Sum d(i) c^i, the sum running over the same exponents (a convergent series
  for c > 1, since the digits are bounded and the exponents go to minus infinity).
* "n divides f(n)" is read in the reals: f(n) = n m for an integer m. `IsTerm n` adds n >= 1, the
  sequence listing positive integers.
* `main` states the conjecture for every k >= 1.
-/

namespace OMA.S_oeis_a214970

/-- The exponent of the largest power of b that does not exceed x. -/
noncomputable def top (b x : ℝ) : ℤ := sSup {i : ℤ | b ^ i ≤ x}

/-- The remainder of the greedy algorithm for x in base b before the exponent top - k. -/
noncomputable def rem (b x : ℝ) : ℕ → ℝ
  | 0 => x
  | k + 1 => rem b x k - ⌊rem b x k / b ^ (top b x - k)⌋₊ * b ^ (top b x - k)

/-- The digit at the exponent top - k of the greedy expansion of x in base b. -/
noncomputable def digit (b x : ℝ) (k : ℕ) : ℕ := ⌊rem b x k / b ^ (top b x - k)⌋₊

/-- The change-of-base function of A214969: f(x) = Sum d(i) c^i where x = Sum d(i) b^i greedily. -/
noncomputable def chg (b c x : ℝ) : ℝ := ∑' k : ℕ, (digit b x k : ℝ) * c ^ (top b x - k)

/-- A000032, the Lucas numbers. -/
def lucas : ℕ → ℕ
  | 0 => 2
  | 1 => 1
  | n + 2 => lucas n + lucas (n + 1)

/-- n is a term of A214970: n >= 1 and n divides f(n) for b = phi, c = phi^2. -/
def IsTerm (n : ℕ) : Prop :=
  1 ≤ n ∧ ∃ m : ℤ, chg Real.goldenRatio (Real.goldenRatio ^ 2) n = (n : ℝ) * m

/-- The conjecture: L(2k-1) and L(2k)+1 are terms of A214970 for every k >= 1. -/
theorem main : ∀ k : ℕ, 1 ≤ k → IsTerm (lucas (2 * k - 1)) ∧ IsTerm (lucas (2 * k) + 1) := by
  sorry

end OMA.S_oeis_a214970
