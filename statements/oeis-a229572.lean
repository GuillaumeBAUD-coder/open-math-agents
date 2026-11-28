import Mathlib

/-!
# A229572: Number of defective 4-colorings of an n X 2 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exac

Source: https://oeis.org/A229572
Credit: @Mapika (AI-assisted: Claude Code, model claude-opus-5-5).

Entry A229572 (R. H. Hardin, Sep 26 2013), offset 1, data 1, 6, 26, 80, 216, 544, 1312, 3072, ...:
Number of defective 4-colorings of an n X 2 0..3 array connected horizontally, vertically,
diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3
order.
Formula section:
Empirical: a(n) = 4*a(n-1) - 4*a(n-2) for n>3.
Conjectures from Colin Barker, Sep 19 2018: (Start)
G.f.: x*(1 + 2*x + 6*x^2) / (1 - 2*x)^2.
a(n) = 2^(n-2) * (7*n-8) for n>1. (End)
Conjectured e.g.f.: 2 + (3*x + exp(2*x)*(7*x - 4))/2. - Stefano Spezia, Oct 21 2022

Formalization notes:
* An array is a function x : Fin n -> Fin 2 -> Fin 4, x i j being the color (0..3) of the cell in
  row i and column j.
* The cells are connected horizontally, vertically, diagonally and antidiagonally (the king graph
  of the n X 2 grid). Its edges are: the horizontal edge (i,0)-(i,1) inside each row i, and, for
  consecutive rows i and i+1, the vertical edges (i,j)-(i+1,j), the diagonal edge (i,0)-(i+1,1)
  and the antidiagonal edge (i,1)-(i+1,0), that is (i,j)-(i+1,k) for all four pairs (j,k).
  A mistake is an edge whose two cells have the same color; `mistakes x` counts them, each edge
  once, and the coloring must have exactly one.
* Colors introduced in row-major 0..3 order (`RowMajorNew`): reading the array row by row, each row
  from left to right, every color smaller than an entry occurs before that entry. Equivalently the
  first entry is 0 and every entry is at most 1 + the largest entry before it, so that each array
  stands for one coloring up to renaming of the colors. Not every color has to occur. This reading
  reproduces the entry's data (checked by direct enumeration for n = 1..7).
* The statement is the conjunction of the four conjectures of the entry:
  Hardin's empirical recurrence, over the integers, for every n > 3 as stated;
  the g.f. as the identity A(x) (1 - 2x)^2 = x(1 + 2x + 6x^2) in the formal power series ring over
  the rationals, with A(x) = Sum_{n >= 1} a(n) x^n (offset 1, so the constant term is 0);
  the closed form as an identity of natural numbers for every n >= 2 (7n - 8 > 0 there);
  the e.g.f. as the identity Sum_{n >= 1} a(n) x^n / n! = 2 + (3x + exp(2x) (7x - 4))/2 in the
  formal power series ring over the rationals, exp(2x) being `rescale 2 (exp ℚ)` (again the sum
  starts at n = 1, so the constant term on the left is 0; the right side has constant term
  2 + (-4)/2 = 0 as well).
-/

namespace OMA.S_oeis_a229572

open PowerSeries Finset

/-- The colors of the array x are introduced in row major order: every color below x(i,j) already
occurs at an earlier position in row major order, in a row i' < i or in row i at a column j' < j.
In particular x(0,0) = 0. -/
def RowMajorNew {R C K : ℕ} (x : Fin R → Fin C → Fin K) : Prop :=
  ∀ i j, ∀ u : Fin K, u < x i j → ∃ i' j', (i' < i ∨ (i' = i ∧ j' < j)) ∧ x i' j' = u

instance {R C K : ℕ} : DecidablePred (@RowMajorNew R C K) := fun x => by
  unfold RowMajorNew; infer_instance

/-- The number of mistakes of the coloring x of the n X 2 king graph: horizontal edges
(i,0)-(i,1) with equal colors, plus edges (i,j)-(i',k) between consecutive rows i' = i + 1
(vertical for j = k, diagonal for (j,k) = (0,1), antidiagonal for (j,k) = (1,0)) with equal
colors. -/
def mistakes {n : ℕ} (x : Fin n → Fin 2 → Fin 4) : ℕ :=
  ((univ : Finset (Fin n)).filter (fun i => x i 0 = x i 1)).card +
    ((univ : Finset (Fin n × Fin n × Fin 2 × Fin 2)).filter
      (fun e => e.2.1.val = e.1.val + 1 ∧ x e.1 e.2.2.1 = x e.2.1 e.2.2.2)).card

/-- A229572(n): the number of colorings of the n X 2 array with colors 0..3 (x i j the color in
row i and column j) with exactly one mistake and colors introduced in row major order. -/
def a (n : ℕ) : ℕ :=
  ((univ : Finset (Fin n → Fin 2 → Fin 4)).filter
    (fun x => mistakes x = 1 ∧ RowMajorNew x)).card

/-- Hardin's empirical recurrence, Barker's conjectured g.f. and closed form, and Spezia's
conjectured e.g.f. -/
theorem main :
    (∀ n : ℕ, 3 < n → (a n : ℤ) = 4 * a (n - 1) - 4 * a (n - 2)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - 2 * X) ^ 2 =
      X * (1 + 2 * X + 6 * X ^ 2) ∧
    (∀ n : ℕ, 1 < n → a n = 2 ^ (n - 2) * (7 * n - 8)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ) / (Nat.factorial n : ℚ)) =
      C (2 : ℚ) + C (1 / 2 : ℚ) * (3 * X + rescale (2 : ℚ) (exp ℚ) * (7 * X - 4)) := by
  sorry

end OMA.S_oeis_a229572
