import OMAStatements.S_oeis_a340507
import Mathlib.Tactic.Linarith

/-!
# The unsigned projection difference of A340507

On row t the two first coordinates differ in absolute value precisely when
y exceeds x. The square root of 2n crosses t+1 at precisely that position.

Source: https://oeis.org/A340507
Credit: @ali-hamdan-007
-/

namespace OMA.S_oeis_a340507

/-- Compute the gap between the two published X-coordinates of the
triangle-stretching maps. -/
theorem projection_gap (x y : ℤ) :
    |variantX x y - originalX x y| = if x < y then 1 else 0 := by
  by_cases h : x < y
  · have hd : x - y < 0 := by omega
    simp only [variantX, originalX, if_pos h, if_pos hd, if_pos hd.le]
    rcases (show (1 + x - y) % 2 = 0 ∨ (1 + x - y) % 2 = 1 by omega) with he | ho
    · have hv : 2*x + (1+(x-y))%2 - (2*x + (x-y)%2) = -1 := by omega
      simp [hv]
    · have hv : 2*x + (1+(x-y))%2 - (2*x + (x-y)%2) = 1 := by omega
      simp [hv]
  · have he : variantX x y = originalX x y := by
      have hd : ¬ x-y < 0 := by omega
      simp only [variantX, originalX, if_neg hd]
      split <;> split <;> omega
    simp [he, h]

end OMA.S_oeis_a340507

namespace OMA.S_oeis_a340507

/-- The triangular number indexing the row is at most n, and the next one exceeds n.
The inequalities are doubled to avoid division. -/
private theorem row_bounds (n : ℕ) :
    row n * (row n + 1) ≤ 2*n ∧ 2*n < (row n+1)*(row n+2) := by
  let r := (8*n+1).sqrt
  let t := row n
  have hr : 1 ≤ r := Nat.le_sqrt.mpr (by omega)
  have hl : 2*t+1 ≤ r := by change 2*((r-1)/2)+1 ≤ r; omega
  have hu : r+1 ≤ 2*t+3 := by change r+1 ≤ 2*((r-1)/2)+3; omega
  have hrl : r*r ≤ 8*n+1 := Nat.sqrt_le _
  have hru : 8*n+1 < (r+1)*(r+1) := Nat.lt_succ_sqrt _
  change t*(t+1) ≤ 2*n ∧ 2*n < (t+1)*(t+2)
  constructor
  · nlinarith only [Nat.mul_le_mul hl hl, hrl]
  · nlinarith only [Nat.mul_le_mul hu hu, hru]

private theorem double_triangular (t : ℕ) : 2*(t*(t+1)/2) = t*(t+1) := by
  have he : t*(t+1)%2 = 0 := by
    rw [Nat.mul_mod]
    rcases (show t%2=0 ∨ (t+1)%2=0 by omega) with h | h <;> simp [h]
  omega

/-- Inside one row, the square root advances exactly when the y coordinate
is larger than the x coordinate. -/
theorem root_gap (n : ℕ) :
    ((2*n).sqrt : ℤ) - (row n : ℤ) =
      if (pointX n : ℤ) < (pointY n : ℤ) then 1 else 0 := by
  let t := row n
  let y := pointY n
  let x := pointX n
  obtain ⟨hl,hu⟩ := row_bounds n
  change t*(t+1) ≤ 2*n at hl
  change 2*n < (t+1)*(t+2) at hu
  have hnext : (t+1)*(t+2) = t*(t+1)+2*(t+1) := by nlinarith
  have htri := double_triangular t
  have hn : 2*n = t*(t+1)+2*y := by
    change 2*n = t*(t+1)+2*(n-t*(t+1)/2)
    omega
  have hy : y ≤ t := by omega
  have hxy : x+y=t := by change t-y+y=t; omega
  have hmin : t ≤ (2*n).sqrt := by apply Nat.le_sqrt.mpr; nlinarith only [hl]
  have hmax : (2*n).sqrt < t+2 := by apply Nat.sqrt_lt.mpr; nlinarith only [hu]
  have hs : (t+1)*(t+1)=t*(t+1)+t+1 := by nlinarith
  change ((2*n).sqrt : ℤ) - (t : ℤ) = if (x:ℤ) < (y:ℤ) then 1 else 0
  split
  · rename_i hc
    have h₁ : t+1 ≤ (2*n).sqrt := Nat.le_sqrt.mpr (by omega)
    omega
  · rename_i hc
    have h₁ : (2*n).sqrt < t+1 := Nat.sqrt_lt.mpr (by omega)
    omega

end OMA.S_oeis_a340507

open OMA.S_oeis_a340507

theorem OMA.solution : type_of% @OMA.S_oeis_a340507.main := by
  intro n
  rw [root_gap, difference, projection_gap]
