import Mathlib

/-!
# A209721: 1/4 the number of (n+1) X 3 0..2 arrays with every 2 X 2 subblock having distinct clockwise edge differences.

Source: https://oeis.org/A209721

The conjectures formalized here:
* Formula section (R. H. Hardin): Empirical: a(n) = a(n-1) +2*a(n-2) -2*a(n-3).
* Formula section (Colin Barker, Mar 23 2012): Empirical g.f.: x*(3+x-5*x^2)/((1-x)*(1-2*x^2)).
* Comment section (Richard Locke Peterson, Apr 26 2020): The formula a(n) = 2*a(n-2)-1 also fits
  empirically.
* Comment section (George Beck, Mar 26 2022): Conjectures: a(n) = A029744(n+1)+1.

The same comment of George Beck also states "a(n) = positions of the zeros in A309019(n+2) -
A002487(n+2)". That second claim is not formalized here: as written its indexing is unclear (the
zeros of A309019(k) - A002487(k) are k = 0 and the terms of A029744, so the claim is a restatement
of the first one up to a shift that the text does not pin down).

A029744: Numbers of the form 2^k or 3*2^k (a list, offset 1: 1, 2, 3, 4, 6, 8, 12, 16, ...).

Conventions:
* An (n+1) X 3 array with entries 0..2 is a map x : Fin (n + 1) → Fin 3 → Fin 3 (row i, column j).
  Its 2 X 2 subblocks are formed by two adjacent rows i, i+1 and two adjacent columns j, j+1. For
  the subblock [[p, q], [r, s]] (p, q in the upper row), going clockwise p -> q -> s -> r -> p gives
  the edge differences q - p, s - q, r - s, p - r, computed as integers; the condition is that
  these four are pairwise distinct. Going counterclockwise, or taking each difference with the
  opposite sign, only permutes and negates the four differences, so the condition does not depend
  on those conventions.
* N(n) is the number of such arrays and a(n) = N(n)/4 is taken as a rational number, so that no
  rounding is involved (the conjectured formulas say that it is an integer). The entry has offset
  1.
* The recurrences are stated for every n for which all the terms they mention are terms of the
  entry: n >= 4 for Hardin's, n >= 3 for Peterson's. Beck's formula is stated for every n >= 1.
* A029744(m) is the m-th smallest number of the form 2^k or 3*2^k (k >= 0), m >= 1, written with
  Nat.nth, which counts from 0.
* The g.f. is the series A(x) = Sum_{n >= 1} a(n) x^n (the constant coefficient is 0). It is
  stated as A(x) * (1 - x) * (1 - 2 x^2) = x (3 + x - 5 x^2) in the ring of formal power series
  over the rationals; since (1 - x) (1 - 2 x^2) has constant coefficient 1 and is invertible
  there, this is the same as the stated quotient.

Numerical check: a transfer-matrix enumeration of the compatible pairs of rows gives a(1..21) = 3,
4, 5, 7, 9, 13, 17, 25, 33, 49, 65, 97, 129, 193, 257, 385, 513, 769, 1025, 1537, 2049, the DATA of
the entry.
-/

namespace OMA.S_oeis_a209721

open PowerSeries

/-- The clockwise edge differences of the subblock [[p, q], [r, s]] are pairwise distinct. -/
abbrev CW (p q r s : Fin 3) : Prop :=
  [(q : ℤ) - p, (s : ℤ) - q, (r : ℤ) - s, (p : ℤ) - r].Nodup

/-- Every 2 X 2 subblock formed by the rows u (upper) and v (lower) satisfies the condition. -/
abbrev BlockOK (u v : Fin 3 → Fin 3) : Prop :=
  ∀ j : Fin 2, CW (u j.castSucc) (u j.succ) (v j.castSucc) (v j.succ)

/-- N(n): the number of (n+1) X 3 0..2 arrays all of whose 2 X 2 subblocks satisfy the
condition. -/
def N (n : ℕ) : ℕ :=
  (Finset.univ.filter fun x : Fin (n + 1) → Fin 3 → Fin 3 =>
    ∀ i : Fin n, BlockOK (x i.castSucc) (x i.succ)).card

/-- A209721: a(n) = N(n)/4. -/
def a (n : ℕ) : ℚ := (N n : ℚ) / 4

/-- A029744(m): the m-th smallest number of the form 2^k or 3*2^k (offset 1). -/
noncomputable def A029744 (m : ℕ) : ℕ := Nat.nth (fun x => ∃ k : ℕ, x = 2 ^ k ∨ x = 3 * 2 ^ k) (m - 1)

/-- The conjectures of Hardin, Barker, Peterson and Beck. -/
theorem main :
    (∀ n : ℕ, 4 ≤ n → a n = a (n - 1) + 2 * a (n - 2) - 2 * a (n - 3)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else a n) * ((1 - X) * (1 - 2 * X ^ 2)) =
      X * (3 + X - 5 * X ^ 2) ∧
    (∀ n : ℕ, 3 ≤ n → a n = 2 * a (n - 2) - 1) ∧
    (∀ n : ℕ, 1 ≤ n → a n = A029744 (n + 1) + 1) := by
  sorry

end OMA.S_oeis_a209721
