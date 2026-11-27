import OMAStatements.S_oeis_a330080
import Mathlib

open OMA.S_oeis_a330080

namespace OMA.P_oeis_a330080

theorem key (x y z : ℚ) (hx : 6 ≤ x) (hy : 0 < y) (hz : 0 < z) :
    24 * x * y * z < (x + y + z) * (1 + x) * (1 + y) * (1 + z) := by
  have hp : 4 * (y * z) ≤ (y + z) ^ 2 := by nlinarith [sq_nonneg (y - z)]
  rcases le_or_gt (24 * x) ((x + y + z) * (1 + x)) with h | h
  · nlinarith [mul_pos hy hz, mul_pos (mul_pos hy hz) (show (0:ℚ) < x by linarith)]
  · have hs : y + z < 36 := by nlinarith
    have h1 : (x + y + z) * (1 + x) * 6 ≥ x * (7 * 6 + 7 * (y + z)) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hx) (show (0:ℚ) ≤ 6 * x - (y + z) by linarith)]
    have h2 : 0 < 7 * (y+z) ^ 3 - 74 * (y+z) ^ 2 + 196 * (y+z) + 168 := by
      nlinarith [sq_nonneg ((y+z) - 5), sq_nonneg ((y+z) - 6), mul_pos hy hz]
    nlinarith [mul_pos hy hz, mul_pos (mul_pos hy hz) (show (0:ℚ) < x by linarith)]

theorem term_succ3 (n : ℕ) : term (n + 3) = (term (n + 2) + term (n + 1)) / term n := by
  rw [term]

theorem invariant (n : ℕ) :
    (0 < term n ∧ 0 < term (n + 1) ∧ 0 < term (n + 2)) ∧
    (term n + term (n + 1) + term (n + 2)) * (1 + term n) * (1 + term (n + 1)) *
      (1 + term (n + 2)) = 24 * term n * term (n + 1) * term (n + 2) := by
  induction n with
  | zero => norm_num [term]
  | succ n ih =>
    obtain ⟨⟨hx, hy, hz⟩, h⟩ := ih
    have e : term (n + 1 + 2) = (term (n + 2) + term (n + 1)) / term n := term_succ3 n
    rw [show n + 1 + 1 = n + 2 by ring, e]
    set x := term n
    set y := term (n + 1)
    set z := term (n + 2)
    refine ⟨⟨hy, hz, by positivity⟩, ?_⟩
    field_simp
    linear_combination (y + z) * h

theorem term_lt_six (n : ℕ) : term n < 6 := by
  obtain ⟨⟨hx, hy, hz⟩, h⟩ := invariant n
  by_contra hc
  push_neg at hc
  have := key _ _ _ hc hy hz
  linarith

end OMA.P_oeis_a330080

theorem OMA.solution : type_of% @OMA.S_oeis_a330080.main := by
  intro n
  obtain ⟨⟨hx, -, -⟩, -⟩ := OMA.P_oeis_a330080.invariant n
  have h6 := OMA.P_oeis_a330080.term_lt_six n
  constructor
  · exact Int.floor_nonneg.mpr hx.le
  · rw [Int.floor_le_iff]
    norm_num
    exact h6
