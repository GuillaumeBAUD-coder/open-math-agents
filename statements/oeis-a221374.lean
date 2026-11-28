import Mathlib

/-!
# OEIS A221374: Barker's generating function and closed form

Source: https://oeis.org/A221374 (OEIS Foundation, CC BY-SA 4.0).
Credit: @ceejcake

Entry (R. H. Hardin), offset 1: Number of n X 2 arrays of occupancy after each element stays
put or moves to some horizontal, vertical or antidiagonal neighbor, with no occupancy greater
than 2. Data: 3, 19, 139, 1035, 7723, 57643, 430251, ...
Formula section: Empirical: a(n) = 9*a(n-1) - 12*a(n-2) + 4*a(n-3).
Conjectures from Colin Barker, Aug 05 2018:
G.f.: x*(3 - 2*x)*(1 - 2*x) / ((1 - x)*(1 - 8*x + 4*x^2)).
a(n) = (1 + (4-2*sqrt(3))^n + (2*(2+sqrt(3)))^n) / 3.

Formalization notes:
* The board has `n` rows and 2 columns, indexed by `Fin n` and `Fin 2`, with one element in
  every cell. Each element chooses a move: stay `(0, 0)`, left `(0, -1)`, right `(0, +1)`,
  up `(-1, 0)`, down `(+1, 0)`, or one of the two antidiagonal steps, up-right `(-1, +1)` and
  down-left `(+1, -1)` (row offset, column offset).
  A choice of moves `mv : Fin n → Fin 2 → Move` is valid when every element lands inside the
  board.
* The occupancy array `occ n mv` gives, for every cell, the number of elements that land there.
  `a n` is the number of distinct occupancy arrays over all valid choices of moves in which
  every entry is at most 2.
  This reading gives a(1) = 3 and a(2) = 19 and reproduces the data of the entry.
* The g.f. is Sum_(n >= 1) a(n) x^n (offset 1, so the constant coefficient is 0). Since the
  denominator has constant term 1, the identity is stated as denominator times series equals
  numerator in the formal power series ring over the integers. The closed form is stated in the
  reals for n >= 1, with sqrt as `Real.sqrt`.
* `main` is the conjunction of Barker's two conjectures.
-/

namespace OMA.S_oeis_a221374

open PowerSeries

/-- The seven moves: staying put, horizontal and vertical steps and the two antidiagonal
steps. -/
inductive Move
  | stay
  | left
  | right
  | up
  | down
  | upRight
  | downLeft
  deriving DecidableEq

instance : Fintype Move :=
  Fintype.ofList [.stay, .left, .right, .up, .down, .upRight, .downLeft]
    (fun x => by cases x <;> simp)

/-- Row offset of a move (rows are numbered from the top). -/
def Move.dr : Move → ℤ
  | .stay => 0
  | .left => 0
  | .right => 0
  | .up => -1
  | .down => 1
  | .upRight => -1
  | .downLeft => 1

/-- Column offset of a move. -/
def Move.dc : Move → ℤ
  | .stay => 0
  | .left => -1
  | .right => 1
  | .up => 0
  | .down => 0
  | .upRight => 1
  | .downLeft => -1

/-- Every element lands inside the `n × 2` board. -/
def valid (n : ℕ) (mv : Fin n → Fin 2 → Move) : Prop :=
  ∀ i : Fin n, ∀ j : Fin 2,
    0 ≤ (i : ℤ) + (mv i j).dr ∧ (i : ℤ) + (mv i j).dr < n ∧
    0 ≤ (j : ℤ) + (mv i j).dc ∧ (j : ℤ) + (mv i j).dc < 2

instance (n : ℕ) : DecidablePred (valid n) := fun mv => by
  unfold valid; infer_instance

/-- The occupancy array: the number of elements landing in cell `(i, j)`. -/
def occ (n : ℕ) (mv : Fin n → Fin 2 → Move) (i : Fin n) (j : Fin 2) : ℕ :=
  ∑ i' : Fin n, ∑ j' : Fin 2,
    if (i' : ℤ) + (mv i' j').dr = i ∧ (j' : ℤ) + (mv i' j').dc = j then 1 else 0

/-- A221374(n): the number of distinct occupancy arrays of the `n × 2` board with every entry
at most 2. -/
def a (n : ℕ) : ℕ :=
  (((Finset.univ.filter (valid n)).image (occ n)).filter fun z => ∀ i j, z i j ≤ 2).card

/-- Barker's conjectures for A221374 (offset 1): the generating function
x(3 - 2x)(1 - 2x) / ((1 - x)(1 - 8x + 4x^2)), and the closed form for n >= 1. -/
theorem main :
    (1 - X) * (1 - 8 * X + 4 * X ^ 2) * mk (fun n => if n = 0 then 0 else (a n : ℤ)) =
      (X * (3 - 2 * X) * (1 - 2 * X) : PowerSeries ℤ) ∧
    ∀ n : ℕ, 1 ≤ n → (a n : ℝ) =
      (1 + (4 - 2 * Real.sqrt 3) ^ n + (2 * (2 + Real.sqrt 3)) ^ n) / 3 := by
  sorry

end OMA.S_oeis_a221374
