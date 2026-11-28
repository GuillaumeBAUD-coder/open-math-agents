import Mathlib

/-!
# OEIS A333650: Domino towers of height k with n bricks

Source: https://oeis.org/A333650 (OEIS Foundation, CC BY-SA 4.0).
`T(n, k)` is the number of domino towers of height `k` consisting of `n` bricks, where the
base is a contiguous row of bricks (canonicalized starting at `0`) and each brick in row
`y + 1` must be at least half supported below by a brick in row `y` (in the staggered brick
lattice, available positions above a row `R` are `R ∪ {x + 1 | x ∈ R}`).

Conjectures (OEIS A333650, Peter Kagey & Peter Luschny):
1. For `n ≥ 2`, `T(n, 2) = A000071(n + 2) = F(n + 2) - 1`.
2. For `n ≥ 2`, `T(n, n - 1) = A339252(n - 2)`.
3. For `n ≥ 3`, `T(n, n - 2) = A339254(n - 3)`.
4. For `n ≥ 4`, `T(n, n - 3) = A339029(n - 4)`.
-/

namespace OMA.S_oeis_a333650

/-- Available brick positions in the next row above `R` in the staggered brick lattice:
each brick at position `x` supports positions `x` and `x + 1` in the row immediately above. -/
def avail (R : Finset ℤ) : Finset ℤ :=
  R ∪ R.image (· + 1)

/-- Valid continuations of `r` additional nonempty rows above row `R`, using `m` total bricks. -/
def towersFrom (R : Finset ℤ) (m : ℕ) : ℕ → Finset (List (Finset ℤ))
  | 0 => if m = 0 then {[]} else ∅
  | r + 1 =>
    ((avail R).powerset.filter (fun S => 1 ≤ S.card ∧ S.card ≤ m)).biUnion fun S =>
      (towersFrom S (m - S.card) r).image (S :: ·)

/-- All domino towers of height `k` with `n` bricks (with contiguous base `{0, ..., b - 1}`). -/
def dominoTowers (n : ℕ) : ℕ → Finset (List (Finset ℤ))
  | 0 => ∅
  | k + 1 =>
    (Finset.Icc 1 n).biUnion fun b =>
      let base : Finset ℤ := (Finset.range b).image (fun i : ℕ => (i : ℤ))
      (towersFrom base (n - b) k).image (base :: ·)

/-- OEIS A333650: `T(n, k)` = number of domino towers of height `k` with `n` bricks. -/
def A333650 (n k : ℕ) : ℕ := (dominoTowers n k).card

/-- OEIS A000071: `F(m) - 1`. -/
def A000071 (m : ℕ) : ℕ := Nat.fib m - 1

/-- OEIS A339252: `a(0) = 1, a(1) = 4, a(2) = 11`, and `a(m) = 4*a(m-1) - 4*a(m-2)` for `m ≥ 3`. -/
def A339252 : ℕ → ℤ
  | 0 => 1
  | 1 => 4
  | 2 => 11
  | m + 3 => 4 * A339252 (m + 2) - 4 * A339252 (m + 1)

/-- OEIS A339254: `a(0..4) = 1, 7, 24, 70, 193`, and
`a(m) = 6*a(m-1) - 12*a(m-2) + 8*a(m-3)` for `m ≥ 5`. -/
def A339254 : ℕ → ℤ
  | 0 => 1
  | 1 => 7
  | 2 => 24
  | 3 => 70
  | 4 => 193
  | m + 5 => 6 * A339254 (m + 4) - 12 * A339254 (m + 3) + 8 * A339254 (m + 2)

/-- OEIS A339029: `a(0..6) = 1, 12, 52, 168, 497, 1412, 3879`, and
`a(m) = 8*a(m-1) - 24*a(m-2) + 32*a(m-3) - 16*a(m-4)` for `m ≥ 7`. -/
def A339029 : ℕ → ℤ
  | 0 => 1
  | 1 => 12
  | 2 => 52
  | 3 => 168
  | 4 => 497
  | 5 => 1412
  | 6 => 3879
  | m + 7 =>
    8 * A339029 (m + 6) - 24 * A339029 (m + 5) + 32 * A339029 (m + 4) - 16 * A339029 (m + 3)

/-- All four conjectures on OEIS A333650:
1. `T(n, 2) = A000071(n + 2)` for all `n ≥ 2`.
2. `T(n, n - 1) = A339252(n - 2)` for all `n ≥ 2`.
3. `T(n, n - 2) = A339254(n - 3)` for all `n ≥ 3`.
4. `T(n, n - 3) = A339029(n - 4)` for all `n ≥ 4`. -/
theorem main :
    (∀ n : ℕ, 2 ≤ n → A333650 n 2 = A000071 (n + 2)) ∧
    (∀ n : ℕ, 2 ≤ n → (A333650 n (n - 1) : ℤ) = A339252 (n - 2)) ∧
    (∀ n : ℕ, 3 ≤ n → (A333650 n (n - 2) : ℤ) = A339254 (n - 3)) ∧
    (∀ n : ℕ, 4 ≤ n → (A333650 n (n - 3) : ℤ) = A339029 (n - 4)) := by
  sorry

end OMA.S_oeis_a333650
