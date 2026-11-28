import Mathlib

/-!
# OEIS A221082: Barker's generating function and closed form

Source: https://oeis.org/A221082 (OEIS Foundation, CC BY-SA 4.0).
Credit: @ceejcake

Entry (R. H. Hardin), offset 1: Number of n X 3 arrays of occupancy after each element moves
to some horizontal or antidiagonal neighbor. Data: 2, 24, 270, 3024, 33858, 379080, ...
Formula section: Empirical: a(n) = 12*a(n-1) - 9*a(n-2).
Conjectures from Colin Barker, Aug 03 2018:
G.f.: 2*x / (1 - 12*x + 9*x^2).
a(n) = ((-(6-3*sqrt(3))^n + (3*(2+sqrt(3)))^n))/(3*sqrt(3)).

Formalization notes:
* The board has `n` rows and 3 columns, indexed by `Fin n` and `Fin 3`, with one element in
  every cell. Each element chooses a move: left `(0, -1)`, right `(0, +1)`, or one of the two
  antidiagonal steps, up-right `(-1, +1)` and down-left `(+1, -1)` (row offset, column offset).
  A choice of moves `mv : Fin n → Fin 3 → Move` is valid when every element lands inside the
  board.
* The occupancy array `occ n mv` gives, for every cell, the number of elements that land there.
  `a n` is the number of distinct occupancy arrays over all valid choices of moves.
  This reading gives a(1) = 2 and a(2) = 24 and reproduces the data of the entry.
* The g.f. is Sum_(n >= 1) a(n) x^n (offset 1, so the constant coefficient is 0). Since the
  denominator has constant term 1, the identity is stated as denominator times series equals
  numerator in the formal power series ring over the integers. The closed form is stated in the
  reals for n >= 1, with sqrt as `Real.sqrt`.
* `main` is the conjunction of Barker's two conjectures.
-/

namespace OMA.S_oeis_a221082

open PowerSeries

/-- The four moves: horizontal steps and the two antidiagonal steps. -/
inductive Move
  | left
  | right
  | upRight
  | downLeft
  deriving DecidableEq

instance : Fintype Move :=
  Fintype.ofList [.left, .right, .upRight, .downLeft] (fun x => by cases x <;> simp)

/-- Row offset of a move (rows are numbered from the top). -/
def Move.dr : Move → ℤ
  | .left => 0
  | .right => 0
  | .upRight => -1
  | .downLeft => 1

/-- Column offset of a move. -/
def Move.dc : Move → ℤ
  | .left => -1
  | .right => 1
  | .upRight => 1
  | .downLeft => -1

/-- Every element lands inside the `n × 3` board. -/
def valid (n : ℕ) (mv : Fin n → Fin 3 → Move) : Prop :=
  ∀ i : Fin n, ∀ j : Fin 3,
    0 ≤ (i : ℤ) + (mv i j).dr ∧ (i : ℤ) + (mv i j).dr < n ∧
    0 ≤ (j : ℤ) + (mv i j).dc ∧ (j : ℤ) + (mv i j).dc < 3

instance (n : ℕ) : DecidablePred (valid n) := fun mv => by
  unfold valid; infer_instance

/-- The occupancy array: the number of elements landing in cell `(i, j)`. -/
def occ (n : ℕ) (mv : Fin n → Fin 3 → Move) (i : Fin n) (j : Fin 3) : ℕ :=
  ∑ i' : Fin n, ∑ j' : Fin 3,
    if (i' : ℤ) + (mv i' j').dr = i ∧ (j' : ℤ) + (mv i' j').dc = j then 1 else 0

/-- A221082(n): the number of distinct occupancy arrays of the `n × 3` board. -/
def a (n : ℕ) : ℕ :=
  ((Finset.univ.filter (valid n)).image (occ n)).card

/-- Barker's conjectures for A221082 (offset 1): the generating function
2x / (1 - 12x + 9x^2), and the closed form for n >= 1. -/
theorem main :
    (1 - 12 * X + 9 * X ^ 2) * mk (fun n => if n = 0 then 0 else (a n : ℤ)) =
      (2 * X : PowerSeries ℤ) ∧
    ∀ n : ℕ, 1 ≤ n → (a n : ℝ) =
      (-(6 - 3 * Real.sqrt 3) ^ n + (3 * (2 + Real.sqrt 3)) ^ n) / (3 * Real.sqrt 3) := by
  sorry

end OMA.S_oeis_a221082
