import Mathlib

/-!
# OEIS A279700: Wu's conjectures for the x-axis (left edge to origin, base 2) of Rule 185

Source: https://oeis.org/A279700
Formalization: @longling12 (drafted with AI assistance)

Entry A279700 (Robert Price, Dec 17 2016), offset 0: Decimal representation of the x-axis, from
the left edge to the origin, of the n-th stage of growth of the two-dimensional cellular
automaton defined by Rule 185, based on the 5-celled von Neumann neighborhood. Initialized with
a single black (ON) cell at stage zero.
Conjectures from Chai Wah Wu, May 04 2024:
a(n) = a(n-2) + 256*a(n-8) - 256*a(n-10) for n > 27.
G.f.: (2048*x^27 + 2048*x^26 - 768*x^25 - 1536*x^24 - 6400*x^23 - 3328*x^22 + 1536*x^21
  + 2560*x^20 + 5112*x^19 - 5128*x^18 - 2045*x^17 + 1286*x^16 + 25*x^15 + 525*x^14 - 6*x^13
  - 778*x^12 + 236*x^11 + 20*x^10 + 72*x^9 - 20*x^8 + 16*x^7 + 62*x^6 + 4*x^5 + 18*x^4 + 4*x^2
  + 1) / (256*x^10 - 256*x^8 - x^2 + 1).

Modeling notes:
* Rule 185 uses Wolfram's outer totalistic code on the 5-cell von Neumann neighborhood (kernel
  {{0,2,0},{2,1,2},{0,2,0}}): a cell's next state is bit c + 2*s of 185, where c is its current
  state and s is the number of ON orthogonal neighbors.
* At stage 0 only the origin (0, 0) in Z^2 is ON; every stage updates all cells of Z^2.
* At stage n, a(n) reads the cells (-n, 0), (-n+1, 0), ..., (0, 0) as binary digits with
  (-n, 0) most significant and (0, 0) least significant, matching FromDigits[..., 2] in the
  entry's Mathematica program.
* The generating function identity A(x) = N(x)/D(x) is stated as A(x) * D(x) = N(x) in
  PowerSeries Z, which is equivalent since D(0) = 1.
-/

namespace OMA.S_oeis_a279700

open PowerSeries

/-- One step of the two-dimensional outer totalistic Rule 185 on the von Neumann neighborhood. -/
def step (s : ℤ → ℤ → Bool) (x y : ℤ) : Bool :=
  Nat.testBit 185 ((s x y).toNat + 2 * ((s (x - 1) y).toNat + (s (x + 1) y).toNat +
    (s x (y - 1)).toNat + (s x (y + 1)).toNat))

/-- Stage n of Rule 185 started from a single ON cell at the origin. -/
def state : ℕ → ℤ → ℤ → Bool
  | 0 => fun x y => decide (x = 0 ∧ y = 0)
  | n + 1 => step (state n)

/-- A279700(n): the cells (-n, 0)..(0, 0) of stage n read in binary from left edge to origin. -/
def a (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (n + 1), (state n ((i : ℤ) - n) 0).toNat * 2 ^ (n - i)

/-- Wu's recurrence and generating function conjectures for A279700. -/
theorem main :
    (∀ n : ℕ, 27 < n → (a n : ℤ) = a (n - 2) + 256 * a (n - 8) - 256 * a (n - 10)) ∧
    PowerSeries.mk (fun n => (a n : ℤ)) * (256 * X ^ 10 - 256 * X ^ 8 - X ^ 2 + 1) =
      2048 * X ^ 27 + 2048 * X ^ 26 - 768 * X ^ 25 - 1536 * X ^ 24 - 6400 * X ^ 23 -
      3328 * X ^ 22 + 1536 * X ^ 21 + 2560 * X ^ 20 + 5112 * X ^ 19 - 5128 * X ^ 18 -
      2045 * X ^ 17 + 1286 * X ^ 16 + 25 * X ^ 15 + 525 * X ^ 14 - 6 * X ^ 13 - 778 * X ^ 12 +
      236 * X ^ 11 + 20 * X ^ 10 + 72 * X ^ 9 - 20 * X ^ 8 + 16 * X ^ 7 + 62 * X ^ 6 + 4 * X ^ 5 +
      18 * X ^ 4 + 4 * X ^ 2 + 1 := by
  sorry

end OMA.S_oeis_a279700
