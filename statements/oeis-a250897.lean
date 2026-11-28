import Mathlib

/-!
# OEIS A250897: Barker's conjectures for (n+1) X (7+1) 0..2 arrays with nondecreasing horizontal differences and absolute vertical differences

Source: https://oeis.org/A250897 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @marcusbuffett.

Entry A250897 (R. H. Hardin, Nov 28 2014), offset 1: Number of (n+1) X (7+1) 0..2 arrays with nondecreasing x(i,j)-x(i,j-1) in the i direction and nondecreasing absolute value of x(i,j)-x(i-1,j) in the j direction.
Formula section:
Empirical: a(n) = 12*a(n-1) - 60*a(n-2) + 162*a(n-3) - 255*a(n-4) + 234*a(n-5) - 116*a(n-6) + 24*a(n-7) for n>9.
Conjectures from _Colin Barker_, Nov 23 2018: (Start)
G.f.: x*(32095 - 296719*x + 1108848*x^2 - 2144026*x^3 + 2239408*x^4 - 1181770*x^5+ 162292*x^6 + 174146*x^7 - 73990*x^8) / ((1 - x)^3*(1 - 2*x)^3*(1 - 3*x)).
a(n) = -17515/4 + 4833*2^(-1+n) + (198025*3^(-3+n))/4 + (23737/2-28323*2^(-5+n))*n + (5071+53217*2^(-5+n))*n^2 for n>2.
(End)

Formalization notes:
* An array is x : Fin (n + 1) → Fin 8 → Fin 3, with row i and column j (so n+1 rows and 7+1
  columns); entries are compared as integers, never modulo 3.
* Nondecreasing x(i,j)-x(i,j-1) in the i direction: for each column j ≥ 1 the differences
  x(i,j) - x(i,j-1) do not decrease as i increases; nondecreasing absolute value of x(i,j)-x(i-1,j)
  in the j direction: for each row i ≥ 1 the values |x(i,j) - x(i-1,j)| do not decrease as j
  increases. Both conditions compare consecutive indices only, so `good` asks, for the 2 X 2 block of
  every two consecutive rows i-1, i and columns j-1, j, x(i-1,j) - x(i-1,j-1) ≤ x(i,j) - x(i,j-1)
  and |x(i,j-1) - x(i-1,j-1)| ≤ |x(i,j) - x(i-1,j)| (`blk`, with p, q the upper row and r, s the
  lower row of the block).
* This reading reproduces all 20 listed terms of the entry (32095, 88421, 244200, ...), checked by a
  transfer-matrix computation over the 3^8 rows.
* a(n) is defined for every n (a(0) counts the single-row arrays); the entry starts at n = 1, so the
  g.f. is stated for A(x) = Sum_{n >= 1} a(n) x^n, as the identity A(x) (1 - x)^3 (1 - 2x)^3 (1 - 3x)
  = (the entry's numerator) in the formal power series ring over the rationals.
* The closed form is stated over the rationals for every n > 2, with the powers 2^(-1+n), 3^(-3+n) and
  2^(-5+n) taken as integer powers (2^(-5+n) is a fraction for n = 3, 4).
* `main` is the conjunction of Barker's two conjectures (the g.f. and the closed form), the problem as
  posed by the site. Hardin's empirical recurrence is not part of it.
-/

namespace OMA.S_oeis_a250897

open PowerSeries

/-- The 2 X 2 block condition: p = x(i-1,j-1), q = x(i-1,j) (upper row), r = x(i,j-1), s = x(i,j). -/
def blk (p q r s : Fin 3) : Prop :=
  ((q : ℕ) : ℤ) - (p : ℕ) ≤ ((s : ℕ) : ℤ) - (r : ℕ) ∧
    |((r : ℕ) : ℤ) - (p : ℕ)| ≤ |((s : ℕ) : ℤ) - (q : ℕ)|

instance : ∀ p q r s, Decidable (blk p q r s) := fun p q r s => by unfold blk; infer_instance

/-- Every 2 X 2 block of consecutive rows and columns satisfies `blk`. -/
def good {n : ℕ} (x : Fin (n + 1) → Fin 8 → Fin 3) : Prop :=
  ∀ i : Fin n, ∀ j : Fin 7,
    blk (x i.castSucc j.castSucc) (x i.castSucc j.succ) (x i.succ j.castSucc) (x i.succ j.succ)

instance {n : ℕ} : DecidablePred (@good n) := fun x => by unfold good; infer_instance

/-- A250897: the number of good (n+1) X (7+1) arrays over 0..2. -/
def a (n : ℕ) : ℕ := ((Finset.univ : Finset (Fin (n + 1) → Fin 8 → Fin 3)).filter good).card

/-- Barker's conjectures. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * ((1 - X) ^ 3 * (1 - 2 * X) ^ 3 * (1 - 3 * X)) =
      X * (32095 - 296719 * X + 1108848 * X ^ 2 - 2144026 * X ^ 3 + 2239408 * X ^ 4 - 1181770 * X ^ 5 + 162292 * X ^ 6 + 174146 * X ^ 7 - 73990 * X ^ 8) ∧
    ∀ n : ℕ, 2 < n → (a n : ℚ) =
      -17515 / 4 + 4833 * (2 : ℚ) ^ ((n : ℤ) - 1) + 198025 * (3 : ℚ) ^ ((n : ℤ) - 3) / 4 + (23737 / 2 - 28323 * (2 : ℚ) ^ ((n : ℤ) - 5)) * n + (5071 + 53217 * (2 : ℚ) ^ ((n : ℤ) - 5)) * n ^ 2 := by
  sorry

end OMA.S_oeis_a250897
