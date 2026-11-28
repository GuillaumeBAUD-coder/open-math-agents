import Mathlib

/-!
# OEIS A284182: Barker's conjectures for the x-axis (origin to right edge, base 2) of Rule 813

Source: https://oeis.org/A284182
Formalization: @longling12 (drafted with AI assistance)

Entry A284182 (Robert Price, Mar 21 2017), offset 0: Decimal representation of the x-axis, from the origin to the right edge, of the n-th stage of growth of the two-dimensional cellular automaton defined by Rule 813, based on the 5-celled von Neumann neighborhood. Initialized with a single black (ON) cell
at stage zero.
Conjectures from Colin Barker, Mar 22 2017:
G.f.: (1 - x + 3*x^2 - 5*x^3 + 18*x^4 + 4*x^5 - 8*x^6 - 16*x^7 - 64*x^8 - 256*x^9 + 1024*x^10 + 512*x^13 - 1024*x^14) / ((1 - x)*(1 + x)*(1 - 2*x)*(1 + x^2)).
a(n) = 2*a(n-1) + a(n-4) - 2*a(n-5) for n>10.

Modeling notes:
* Rule 813 uses Wolfram's outer totalistic code on the 5-cell von Neumann neighborhood (kernel
  {{0,2,0},{2,1,2},{0,2,0}}): a cell's next state is bit c + 2*s of 813, where c is its current
  state and s is the number of ON orthogonal neighbors.
* At stage 0 only the origin (0, 0) in Z^2 is ON; every stage updates all cells of Z^2.
* At stage n, a(n) reads (0, 0)..(n, 0) in binary from origin to right edge.
* The generating function identity A(x) = N(x)/D(x) is stated as A(x) * D(x) = N(x) in
  PowerSeries Z, which is equivalent since D(0) = 1.
-/

namespace OMA.S_oeis_a284182

open PowerSeries

/-- One step of the two-dimensional outer totalistic Rule 813 on the von Neumann neighborhood. -/
def step (s : ℤ → ℤ → Bool) (x y : ℤ) : Bool :=
  Nat.testBit 813 ((s x y).toNat + 2 * ((s (x - 1) y).toNat + (s (x + 1) y).toNat +
    (s x (y - 1)).toNat + (s x (y + 1)).toNat))

/-- Stage n of Rule 813 started from a single ON cell at the origin. -/
def state : ℕ → ℤ → ℤ → Bool
  | 0 => fun x y => decide (x = 0 ∧ y = 0)
  | n + 1 => step (state n)

/-- A284182(n): the cells (0, 0)..(n, 0) of stage n read in binary from origin to right edge. -/
def a (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (n + 1), (state n (i : ℤ) 0).toNat * 2 ^ (n - i)

/-- Barker's conjectures for A284182. -/
theorem main :
    PowerSeries.mk (fun n => (a n : ℤ)) *
      ((1 - X) * (1 + X) * (1 - 2 * X) * (1 + X ^ 2)) =
      1 - X + 3 * X ^ 2 - 5 * X ^ 3 + 18 * X ^ 4 + 4 * X ^ 5 - 8 * X ^ 6 - 16 * X ^ 7 -
      64 * X ^ 8 - 256 * X ^ 9 + 1024 * X ^ 10 + 512 * X ^ 13 - 1024 * X ^ 14 ∧
    (∀ n : ℕ, 10 < n → (a n : ℤ) = 2 * a (n - 1) + a (n - 4) - 2 * a (n - 5)) := by
  sorry

end OMA.S_oeis_a284182
