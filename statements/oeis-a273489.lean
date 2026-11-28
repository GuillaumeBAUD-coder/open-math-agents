import Mathlib

/-!
# A273489: ON cells at stage 2^n-1 of the 2D 5-neighbor cellular automaton "Rule 758"

The automaton lives on the square grid `ℤ × ℤ`, starting at stage 0 with the single ON cell
`(0, 0)`. Following Wolfram's outer totalistic 5-neighbor code (as in the entry's Mathematica
program: `ListConvolve[{{0,2,0},{2,1,2},{0,2,0}}, ...]` followed by digit `10 - v` of the
10-bit binary expansion of the code), a cell's next state is bit `v` of 758, where
`v = (own state) + 2 * (number of ON cells among its four von Neumann neighbors)`.
A273489(n) is the number of ON cells at stage `2^n - 1`. The Lean definition below gives
1, 5, 21, 85 for n = 0..3, and a simulation of the same rule matches all listed terms
(n = 0..15).

Bit 0 of 758 is 0, so cells far from the pattern stay OFF and the set of ON cells is finite;
`Nat.card` counts it.

The problem: the conjectures
  a(n) = 2*4^n - 4*3^(n-1) + 2*2^n - 23 for n > 2 (Lars Blomberg, Jul 20 2016),
  a(n) = 10*a(n-1) - 35*a(n-2) + 50*a(n-3) - 24*a(n-4) for n > 6 (Colin Barker, Jul 20 2016),
  G.f.: (1-5*x+6*x^2+72*x^4-320*x^5+384*x^6) / ((1-x)*(1-2*x)*(1-3*x)*(1-4*x)) (Colin Barker).
The offset is 0. The g.f. is stated after multiplying both sides by the denominator.

Source: https://oeis.org/A273489
Credit: @VashaTS
-/

namespace OMA.S_oeis_a273489

open PowerSeries

/-- One step of the outer totalistic 5-neighbor automaton with the given code: the new state of
`p` is bit `own + 2 * (ON von Neumann neighbors)` of `code`. -/
def step (code : ℕ) (f : ℤ × ℤ → Bool) : ℤ × ℤ → Bool := fun p =>
  code.testBit ((f p).toNat + 2 * ((f (p.1 + 1, p.2)).toNat + (f (p.1 - 1, p.2)).toNat +
    (f (p.1, p.2 + 1)).toNat + (f (p.1, p.2 - 1)).toNat))

/-- The configuration of Rule 758 at stage `t`, started from the single ON cell `(0, 0)`. -/
def stage (t : ℕ) : ℤ × ℤ → Bool := (step 758)^[t] fun p => decide (p = (0, 0))

/-- A273489(n): the number of ON cells at stage `2^n - 1`. -/
noncomputable def a (n : ℕ) : ℕ := Nat.card {p : ℤ × ℤ // stage (2 ^ n - 1) p = true}

theorem main :
    (∀ n : ℕ, 2 < n → (a n : ℤ) = 2 * 4 ^ n - 4 * 3 ^ (n - 1) + 2 * 2 ^ n - 23) ∧
    (∀ n : ℕ, 6 < n →
      (a n : ℤ) = 10 * a (n - 1) - 35 * a (n - 2) + 50 * a (n - 3) - 24 * a (n - 4)) ∧
    PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) * (1 - 2 * X) * (1 - 3 * X) * (1 - 4 * X)) =
      1 - 5 * X + 6 * X ^ 2 + 72 * X ^ 4 - 320 * X ^ 5 + 384 * X ^ 6 := by
  sorry

end OMA.S_oeis_a273489
