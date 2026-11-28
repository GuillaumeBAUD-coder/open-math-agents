import Mathlib

/-!
# A273796: ON cells at stage 2^n-1 of the 2D 5-neighbor cellular automaton "Rule 942"

The automaton lives on the square grid `ℤ × ℤ`, starting at stage 0 with the single ON cell
`(0, 0)`. Following Wolfram's outer totalistic 5-neighbor code (as in the entry's Mathematica
program: `ListConvolve[{{0,2,0},{2,1,2},{0,2,0}}, ...]` followed by digit `10 - v` of the
10-bit binary expansion of the code), a cell's next state is bit `v` of 942, where
`v = (own state) + 2 * (number of ON cells among its four von Neumann neighbors)`.
A273796(n) is the number of ON cells at stage `2^n - 1`. The Lean definition below gives
1, 5, 21, 89 for n = 0..3, and a simulation of the same rule matches all listed terms
(n = 0..15).

Bit 0 of 942 is 0, so cells far from the pattern stay OFF and the set of ON cells is finite;
`Nat.card` counts it.

The problem: the conjectures
  a(n) = 2*4^n - 16*3^(n-2) + 2^n + 1 for n > 1 (Lars Blomberg, Jul 25 2016),
  a(n) = 10*a(n-1) - 35*a(n-2) + 50*a(n-3) - 24*a(n-4) for n > 5 (Colin Barker, Dec 01 2016),
  G.f.: (1 - 5*x + 6*x^2 + 4*x^3 + 4*x^4 - 16*x^5) / ((1 - x)*(1 - 2*x)*(1 - 3*x)*(1 - 4*x))
  (Colin Barker).
The offset is 0. The g.f. is stated after multiplying both sides by the denominator.

Source: https://oeis.org/A273796
Credit: @VashaTS
-/

namespace OMA.S_oeis_a273796

open PowerSeries

/-- One step of the outer totalistic 5-neighbor automaton with the given code: the new state of
`p` is bit `own + 2 * (ON von Neumann neighbors)` of `code`. -/
def step (code : ℕ) (f : ℤ × ℤ → Bool) : ℤ × ℤ → Bool := fun p =>
  code.testBit ((f p).toNat + 2 * ((f (p.1 + 1, p.2)).toNat + (f (p.1 - 1, p.2)).toNat +
    (f (p.1, p.2 + 1)).toNat + (f (p.1, p.2 - 1)).toNat))

/-- The configuration of Rule 942 at stage `t`, started from the single ON cell `(0, 0)`. -/
def stage (t : ℕ) : ℤ × ℤ → Bool := (step 942)^[t] fun p => decide (p = (0, 0))

/-- A273796(n): the number of ON cells at stage `2^n - 1`. -/
noncomputable def a (n : ℕ) : ℕ := Nat.card {p : ℤ × ℤ // stage (2 ^ n - 1) p = true}

theorem main :
    (∀ n : ℕ, 1 < n → (a n : ℤ) = 2 * 4 ^ n - 16 * 3 ^ (n - 2) + 2 ^ n + 1) ∧
    (∀ n : ℕ, 5 < n →
      (a n : ℤ) = 10 * a (n - 1) - 35 * a (n - 2) + 50 * a (n - 3) - 24 * a (n - 4)) ∧
    PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) * (1 - 2 * X) * (1 - 3 * X) * (1 - 4 * X)) =
      1 - 5 * X + 6 * X ^ 2 + 4 * X ^ 3 + 4 * X ^ 4 - 16 * X ^ 5 := by
  sorry

end OMA.S_oeis_a273796
