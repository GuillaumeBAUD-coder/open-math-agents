import Mathlib

/-!
# A032191: Number of necklaces with 6 black beads and n-6 white beads.

Source: https://oeis.org/A032191
Credit: @xor2k

Ralf Stephan, in the formula section of A032191:
  G.f.: (1-x+x^2+4*x^3+2*x^4+3*x^6+x^7+x^8)/((1-x)^6*(1+x)^3*(1+x+x^2)^2*(1-x+x^2)) (conjectured).
Wolfdieter Lang restates it in the entry with the offset made explicit:
  G.f.: (x^6)*(1-x+x^2+4*x^3+2*x^4+3*x^6+x^7+x^8)/((1-x)^2*(1-x^2)^2*(1-x^3)*(1-x^6)).

Conventions:
* A coloring of n beads in cyclic order with 6 black beads and n-6 white beads is a function
  f : Fin n → Bool with exactly 6 indices i such that f i = true (true is black).
* Necklaces (turning over is not allowed): two colorings f, g give the same necklace when one is a
  rotation of the other: g(i) = f(i + r) for all i, for some r (indices mod n, the addition of
  Fin n). This relation is an equivalence, and `a n` is the number of its classes, `Nat.card` of
  the quotient.
* Offset 6; the definition gives a(n) = 0 for n < 6. Stephan's series starts with the constant
  term 1 = a(6), so his g.f. is stated for the series with coefficient a(n+6) at X^n (first part).
  The second part is the same g.f. in Lang's form, for the series with coefficient a(n) at X^n and
  the factor X^6. Both are identities of formal power series over ℚ with the denominator
  multiplied out. The two denominators are equal as polynomials.

Numerical check: a Python copy of the definition (orbits counted by brute force) gives
1, 1, 4, 10, 22, 42, 80, 132, 217, 335, 504, 728, 1038, 1428, 1944, 2586, 3399, 4389, 5620, 7084
for n = 6..25 (and 0 for n < 6), the DATA of the entry as far as remembered (the entry was not
available offline); the g.f. was checked against these terms.
-/

namespace OMA.S_oeis_a032191

/-- Colorings of n beads in cyclic order, 6 of them black (true) and n - 6 white (false). -/
def W (n : ℕ) : Type :=
  {f : Fin n → Bool // (Finset.univ.filter (fun i => f i = true)).card = 6}

/-- Two colorings give the same necklace (rotation only). -/
def SameNecklace (n : ℕ) (f g : W n) : Prop :=
  ∃ r : Fin n, ∀ i, g.1 i = f.1 (i + r)

/-- A032191: the number of necklaces with 6 black beads and n - 6 white beads. -/
noncomputable def a (n : ℕ) : ℕ := Nat.card (Quot (SameNecklace n))

open PowerSeries in
/-- Stephan's conjectured g.f., and the same g.f. in Lang's form. -/
theorem main :
    (PowerSeries.mk (fun n => (a (n + 6) : ℚ)) *
        ((1 - X) ^ 6 * (1 + X) ^ 3 * (1 + X + X ^ 2) ^ 2 * (1 - X + X ^ 2) : PowerSeries ℚ) =
      1 - X + X ^ 2 + 4 * X ^ 3 + 2 * X ^ 4 + 3 * X ^ 6 + X ^ 7 + X ^ 8) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) *
        ((1 - X) ^ 2 * (1 - X ^ 2) ^ 2 * (1 - X ^ 3) * (1 - X ^ 6) : PowerSeries ℚ) =
      X ^ 6 * (1 - X + X ^ 2 + 4 * X ^ 3 + 2 * X ^ 4 + 3 * X ^ 6 + X ^ 7 + X ^ 8)) := by
  sorry

end OMA.S_oeis_a032191
