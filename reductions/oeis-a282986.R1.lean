import OMAStatements.S_oeis_a282986
import Mathlib

-- Credit: @qu1r0ra

/-!
Reduction of `OMA.S_oeis_a282986.main` to two hypotheses.

* `H1` (geometric): from `t = 30` on, the 14 axis cells nearest the origin have period 4 in `t`,
  and every farther axis cell equals the cell four steps earlier at the same depth `t - |x|`.
  Checked numerically for `30 ≤ t ≤ 396`. This is the open part: no finite band view of the
  lattice determines itself (aperiodic gliders keep crossing the near-origin quadrant).
* `H2` (finite): the first 38 terms of the sequence.

From these, `a (n + 4) = 16 * a n + c n` with `c n` periodic of period 4 for `n ≥ 30`, which
gives the recurrence and the generating function.
-/

namespace OMA.R_oeis_a282986_R1

open OMA.S_oeis_a282986

def H1 : Prop :=
  ∀ t : ℕ, 30 ≤ t →
    (∀ j : ℕ, j < 14 → cell 541 (t + 4) (-(j : ℤ)) 0 = cell 541 t (-(j : ℤ)) 0) ∧
    (∀ j : ℕ, 14 ≤ j → j ≤ t + 4 →
      cell 541 (t + 4) (-(j : ℤ)) 0 = cell 541 t (-((j - 4 : ℕ) : ℤ)) 0)

def H2 : Prop :=
  ∀ n : ℕ, n < 38 → a n = ([1, 2, 4, 9, 18, 36, 75, 145, 300, 579, 1213, 2334, 4804, 9273, 19410, 37348, 76883, 148393, 310532, 597627, 1230097, 2374372, 4968531, 9561889, 19681356, 37990195, 79496909, 152990002, 314902220, 607844659, 1271953101, 2447845682, 5038429900, 9725511987, 20351252173, 39165536562, 80614872780, 155608189235] : List ℤ).getD n 0

lemma a_eq_digits (p : ℕ → ℕ → Bool) (hp : ∀ n j, p n j = cell 541 n (-(j : ℤ)) 0)
    (n : ℕ) :
    a n = ∑ j ∈ Finset.range (n + 1), (if p n j then (2 : ℤ) ^ j else 0) := by
  calc
    a n = ∑ k ∈ Finset.range (n + 1), (if p n (n - k) then (2 : ℤ) ^ (n - k) else 0) := by
      unfold a
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk' := Finset.mem_range.mp hk
      rw [hp, show (k : ℤ) - (n : ℤ) = -((n - k : ℕ) : ℤ) by omega]
    _ = _ := by
      simpa only [Nat.add_sub_cancel] using
        Finset.sum_range_reflect (fun j => if p n j then (2 : ℤ) ^ j else 0) (n + 1)

lemma shift (p : ℕ → ℕ → Bool) (hp : ∀ n j, p n j = cell 541 n (-(j : ℤ)) 0)
    (hA : ∀ t : ℕ, 30 ≤ t → (∀ j : ℕ, j < 14 → p (t + 4) j = p t j) ∧
      (∀ j : ℕ, 14 ≤ j → j ≤ t + 4 → p (t + 4) j = p t (j - 4)))
    (n : ℕ) (hn : 30 ≤ n) :
    a (n + 4) = 16 * a n +
      ((∑ j ∈ Finset.range 14, (if p n j then (2 : ℤ) ^ j else 0)) -
        16 * ∑ j ∈ Finset.range 10, (if p n j then (2 : ℤ) ^ j else 0)) := by
  rw [a_eq_digits p hp, a_eq_digits p hp, show n + 4 + 1 = 14 + (n - 9) by omega,
    show n + 1 = 10 + (n - 9) by omega, Finset.sum_range_add, Finset.sum_range_add]
  have h1 : (∑ x ∈ Finset.range (n - 9),
        (if p (n + 4) (14 + x) then (2 : ℤ) ^ (14 + x) else 0)) =
      ∑ x ∈ Finset.range (n - 9), 16 * (if p n (10 + x) then (2 : ℤ) ^ (10 + x) else 0) := by
    refine Finset.sum_congr rfl fun x hx => ?_
    have hx' := Finset.mem_range.mp hx
    have hq := (hA n hn).2 (14 + x) (by omega) (by omega)
    rw [show 14 + x - 4 = 10 + x by omega] at hq
    rw [hq]
    split
    · rw [show 14 + x = 4 + (10 + x) by omega, pow_add]
      norm_num
    · simp
  have h2 : (∑ j ∈ Finset.range 14, (if p (n + 4) j then (2 : ℤ) ^ j else 0)) =
      ∑ j ∈ Finset.range 14, (if p n j then (2 : ℤ) ^ j else 0) := by
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' := Finset.mem_range.mp hj
    rw [(hA n hn).1 j hj']
  rw [h1, h2, ← Finset.mul_sum]
  ring

lemma recur (p : ℕ → ℕ → Bool) (hp : ∀ n j, p n j = cell 541 n (-(j : ℤ)) 0)
    (hA : ∀ t : ℕ, 30 ≤ t → (∀ j : ℕ, j < 14 → p (t + 4) j = p t j) ∧
      (∀ j : ℕ, 14 ≤ j → j ≤ t + 4 → p (t + 4) j = p t (j - 4)))
    (hI : ∀ n : ℕ, n < 38 → a n = ([1, 2, 4, 9, 18, 36, 75, 145, 300, 579, 1213, 2334, 4804, 9273, 19410, 37348, 76883, 148393, 310532, 597627, 1230097, 2374372, 4968531, 9561889, 19681356, 37990195, 79496909, 152990002, 314902220, 607844659, 1271953101, 2447845682, 5038429900, 9725511987, 20351252173, 39165536562, 80614872780, 155608189235] : List ℤ).getD n 0)
    (n : ℕ) (hn : 34 ≤ n) :
    (a n : ℚ) = 17 * a (n - 4) - 16 * a (n - 8) := by
  have h : a n = 17 * a (n - 4) - 16 * a (n - 8) := by
    by_cases h38 : 38 ≤ n
    · have e1 := shift p hp hA (n - 4) (by omega)
      have e2 := shift p hp hA (n - 8) (by omega)
      have p14 : (∑ j ∈ Finset.range 14, (if p (n - 8 + 4) j then (2 : ℤ) ^ j else 0)) =
          ∑ j ∈ Finset.range 14, (if p (n - 8) j then (2 : ℤ) ^ j else 0) := by
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [(hA (n - 8) (by omega)).1 j (Finset.mem_range.mp hj)]
      have p10 : (∑ j ∈ Finset.range 10, (if p (n - 8 + 4) j then (2 : ℤ) ^ j else 0)) =
          ∑ j ∈ Finset.range 10, (if p (n - 8) j then (2 : ℤ) ^ j else 0) := by
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [(hA (n - 8) (by omega)).1 j (by have := Finset.mem_range.mp hj; omega)]
      rw [show n - 4 + 4 = n by omega] at e1
      rw [show n - 8 + 4 = n - 4 by omega] at e2 p14 p10
      rw [p14, p10] at e1
      linarith
    · rw [hI n (by omega), hI (n - 4) (by omega), hI (n - 8) (by omega)]
      interval_cases n <;> norm_num
  exact_mod_cast h

set_option maxHeartbeats 4000000 in
open PowerSeries in
lemma gf (hI : ∀ n : ℕ, n < 38 → a n = ([1, 2, 4, 9, 18, 36, 75, 145, 300, 579, 1213, 2334, 4804, 9273, 19410, 37348, 76883, 148393, 310532, 597627, 1230097, 2374372, 4968531, 9561889, 19681356, 37990195, 79496909, 152990002, 314902220, 607844659, 1271953101, 2447845682, 5038429900, 9725511987, 20351252173, 39165536562, 80614872780, 155608189235] : List ℤ).getD n 0)
    (hrec : ∀ n : ℕ, 34 ≤ n → (a n : ℚ) = 17 * a (n - 4) - 16 * a (n - 8)) :
    PowerSeries.mk (fun n => (a n : ℚ)) * (16 * X ^ 8 - 17 * X ^ 4 + 1 : PowerSeries ℚ) =
      -4096 * X ^ 33 - 6144 * X ^ 32 + 5872 * X ^ 31 + 2144 * X ^ 30 + 1296 * X ^ 29 + 720 * X ^ 28 - 79 * X ^ 27 + 394 * X ^ 26 + 159 * X ^ 25 - 165 * X ^ 24 - 202 * X ^ 23 + 47 * X ^ 22 + 59 * X ^ 21 - 50 * X ^ 20 + 55 * X ^ 19 - 30 * X ^ 18 + 16 * X ^ 17 + 15 * X ^ 16 - 10 * X ^ 15 - 11 * X ^ 14 + 6 * X ^ 13 - 8 * X ^ 12 + 13 * X ^ 11 + 2 * X ^ 10 - X ^ 9 + 10 * X ^ 8 - 8 * X ^ 7 + 7 * X ^ 6 + 2 * X ^ 5 + X ^ 4 + 9 * X ^ 3 + 4 * X ^ 2 + 2 * X + 1 := by
  set F : PowerSeries ℚ := mk (fun n => (a n : ℚ)) with hF
  have lhs : F * (16 * X ^ 8 - 17 * X ^ 4 + 1 : PowerSeries ℚ) =
      F + (-17 : ℤ) • (F * X ^ 4) + (16 : ℤ) • (F * X ^ 8) := by
    simp only [zsmul_eq_mul]
    push_cast
    ring
  have rhs : (-4096 * X ^ 33 - 6144 * X ^ 32 + 5872 * X ^ 31 + 2144 * X ^ 30 + 1296 * X ^ 29 + 720 * X ^ 28 - 79 * X ^ 27 + 394 * X ^ 26 + 159 * X ^ 25 - 165 * X ^ 24 - 202 * X ^ 23 + 47 * X ^ 22 + 59 * X ^ 21 - 50 * X ^ 20 + 55 * X ^ 19 - 30 * X ^ 18 + 16 * X ^ 17 + 15 * X ^ 16 - 10 * X ^ 15 - 11 * X ^ 14 + 6 * X ^ 13 - 8 * X ^ 12 + 13 * X ^ 11 + 2 * X ^ 10 - X ^ 9 + 10 * X ^ 8 - 8 * X ^ 7 + 7 * X ^ 6 + 2 * X ^ 5 + X ^ 4 + 9 * X ^ 3 + 4 * X ^ 2 + 2 * X + 1 : PowerSeries ℚ) =
      (-4096 : ℤ) • X ^ 33 +
        (-6144 : ℤ) • X ^ 32 +
        (5872 : ℤ) • X ^ 31 +
        (2144 : ℤ) • X ^ 30 +
        (1296 : ℤ) • X ^ 29 +
        (720 : ℤ) • X ^ 28 +
        (-79 : ℤ) • X ^ 27 +
        (394 : ℤ) • X ^ 26 +
        (159 : ℤ) • X ^ 25 +
        (-165 : ℤ) • X ^ 24 +
        (-202 : ℤ) • X ^ 23 +
        (47 : ℤ) • X ^ 22 +
        (59 : ℤ) • X ^ 21 +
        (-50 : ℤ) • X ^ 20 +
        (55 : ℤ) • X ^ 19 +
        (-30 : ℤ) • X ^ 18 +
        (16 : ℤ) • X ^ 17 +
        (15 : ℤ) • X ^ 16 +
        (-10 : ℤ) • X ^ 15 +
        (-11 : ℤ) • X ^ 14 +
        (6 : ℤ) • X ^ 13 +
        (-8 : ℤ) • X ^ 12 +
        (13 : ℤ) • X ^ 11 +
        (2 : ℤ) • X ^ 10 +
        (-1 : ℤ) • X ^ 9 +
        (10 : ℤ) • X ^ 8 +
        (-8 : ℤ) • X ^ 7 +
        (7 : ℤ) • X ^ 6 +
        (2 : ℤ) • X ^ 5 +
        (1 : ℤ) • X ^ 4 +
        (9 : ℤ) • X ^ 3 +
        (4 : ℤ) • X ^ 2 +
        (2 : ℤ) • X ^ 1 +
        (1 : ℤ) • X ^ 0 := by
    simp only [zsmul_eq_mul]
    push_cast
    ring
  rw [lhs, rhs]
  ext n
  simp only [map_add, map_zsmul, coeff_mul_X_pow', hF, coeff_mk, coeff_X_pow]
  simp only [zsmul_eq_mul]
  by_cases hn : 34 ≤ n
  · have hr := hrec n hn
    simp only [show 4 ≤ n by omega, show 8 ≤ n by omega, show n ≠ 1 by omega, show n ≠ 2 by omega, show n ≠ 3 by omega, show n ≠ 4 by omega, show n ≠ 5 by omega, show n ≠ 6 by omega, show n ≠ 7 by omega, show n ≠ 8 by omega, show n ≠ 9 by omega, show n ≠ 10 by omega, show n ≠ 11 by omega, show n ≠ 12 by omega, show n ≠ 13 by omega, show n ≠ 14 by omega, show n ≠ 15 by omega, show n ≠ 16 by omega, show n ≠ 17 by omega, show n ≠ 18 by omega, show n ≠ 19 by omega, show n ≠ 20 by omega, show n ≠ 21 by omega, show n ≠ 22 by omega, show n ≠ 23 by omega, show n ≠ 24 by omega, show n ≠ 25 by omega, show n ≠ 26 by omega, show n ≠ 27 by omega, show n ≠ 28 by omega, show n ≠ 29 by omega, show n ≠ 30 by omega, show n ≠ 31 by omega, show n ≠ 32 by omega, show n ≠ 33 by omega,
      show n ≠ 0 by omega, ite_true, ite_false]
    push_cast
    linarith
  · have h₀ := hI n (by omega)
    have h₄ := hI (n - 4) (by omega)
    have h₈ := hI (n - 8) (by omega)
    rw [h₀, h₄, h₈]
    interval_cases n <;> norm_num

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a282986.main := fun h1 h2 =>
  ⟨recur (fun n j => cell 541 n (-(j : ℤ)) 0) (fun _ _ => rfl) h1 h2,
    gf h2 (recur (fun n j => cell 541 n (-(j : ℤ)) 0) (fun _ _ => rfl) h1 h2)⟩

end OMA.R_oeis_a282986_R1
