import Mathlib

/-!
# OEIS A278901: Barker's conjectures for the x-axis (origin to right edge, base 2) of Rule 107

Source: https://oeis.org/A278901
Formalization: @longling12 (drafted with AI assistance)

Entry A278901 (Robert Price, Nov 30 2016), offset 0: Decimal representation of the x-axis, from
the origin to the right edge, of the n-th stage of growth of the two-dimensional cellular
automaton defined by Rule 107, based on the 5-celled von Neumann neighborhood. Initialized with
a single black (ON) cell at stage zero.
Conjectures from Colin Barker, Nov 30 2016:
a(n) = 5*a(n-2) - 20*a(n-6) + 16*a(n-8) for n>15.
G.f.: (1 +2*x -x^2 +5*x^3 -16*x^4 -16*x^5 -16*x^7 +144*x^8 +16*x^9 -64*x^10 +64*x^11 -320*x^12
  -320*x^13 +256*x^14 +256*x^15) / ((1 -x)*(1 +x)*(1 -2*x)*(1 +2*x)*(1 -2*x^2)*(1 +2*x^2)).

Modeling notes:
* Rule 107 uses Wolfram's outer totalistic code on the 5-cell von Neumann neighborhood (kernel
  {{0,2,0},{2,1,2},{0,2,0}}): a cell's next state is bit c + 2*s of 107, where c is its current
  state and s is the number of ON orthogonal neighbors.
* At stage 0 only the origin (0, 0) in Z^2 is ON; every stage updates all cells of Z^2.
* At stage n, a(n) reads the cells (0, 0), (1, 0), ..., (n, 0) as binary digits with
  (0, 0) most significant and (n, 0) least significant, matching FromDigits[..., 2] in the
  entry's Mathematica program.
* The generating function identity A(x) = N(x)/D(x) is stated as A(x) * D(x) = N(x) in
  PowerSeries Z, which is equivalent since D(0) = 1.
-/

namespace OMA.S_oeis_a278901

open PowerSeries

/-- One step of the two-dimensional outer totalistic Rule 107 on the von Neumann neighborhood. -/
def step (s : ℤ → ℤ → Bool) (x y : ℤ) : Bool :=
  Nat.testBit 107 ((s x y).toNat + 2 * ((s (x - 1) y).toNat + (s (x + 1) y).toNat +
    (s x (y - 1)).toNat + (s x (y + 1)).toNat))

/-- Stage n of Rule 107 started from a single ON cell at the origin. -/
def state : ℕ → ℤ → ℤ → Bool
  | 0 => fun x y => decide (x = 0 ∧ y = 0)
  | n + 1 => step (state n)

/-- A278901(n): the cells (0, 0)..(n, 0) of stage n read in binary from origin to right edge. -/
def a (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (n + 1), (state n (i : ℤ) 0).toNat * 2 ^ (n - i)

/-- Barker's recurrence and generating function conjectures for A278901. -/
theorem main :
    (∀ n : ℕ, 15 < n → (a n : ℤ) = 5 * a (n - 2) - 20 * a (n - 6) + 16 * a (n - 8)) ∧
    PowerSeries.mk (fun n => (a n : ℤ)) *
      ((1 - X) * (1 + X) * (1 - 2 * X) * (1 + 2 * X) * (1 - 2 * X ^ 2) * (1 + 2 * X ^ 2)) =
      1 + 2 * X - X ^ 2 + 5 * X ^ 3 - 16 * X ^ 4 - 16 * X ^ 5 - 16 * X ^ 7 + 144 * X ^ 8 +
      16 * X ^ 9 - 64 * X ^ 10 + 64 * X ^ 11 - 320 * X ^ 12 - 320 * X ^ 13 + 256 * X ^ 14 +
      256 * X ^ 15 := by
  sorry

end OMA.S_oeis_a278901
