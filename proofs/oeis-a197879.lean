import OMAStatements.S_oeis_a197879
import Mathlib

/-!
# A197879: proof of Cicuttin's remarks

Credit: @ivillar

Write k(n) = floor(n sqrt 8). Since 2.8 < sqrt 8 < 2.9, k(n+1) - k(n) is 2 or 3 and
k(n+2) - k(n) >= 5, so two consecutive equalities of parity (both differences 2) are
impossible. For the first claim, sqrt 8 = 2 sqrt 2, and floor(2y) = 2 floor(y) + [frac y >= 1/2];
frac(sqrt 2 * n) = 1/2 is excluded because sqrt 2 * n is irrational for n >= 1.
-/

namespace PA197879
open OMA.S_oeis_a197879

theorem s8_lo : (2.8 : ℝ) < Real.sqrt 8 := by
  rw [Real.lt_sqrt (by norm_num)]; norm_num

theorem s8_hi : Real.sqrt 8 < 2.9 := by
  rw [Real.sqrt_lt' (by norm_num)]; norm_num

theorem s8_eq : Real.sqrt 8 = 2 * Real.sqrt 2 := by
  rw [show (8 : ℝ) = 2 ^ 2 * 2 by norm_num, Real.sqrt_mul (by norm_num),
    Real.sqrt_sq (by norm_num)]

/-- Bounds for the floor. -/
theorem fl (x : ℝ) (hx : 0 ≤ x) : (⌊x⌋₊ : ℝ) ≤ x ∧ x < ⌊x⌋₊ + 1 :=
  ⟨Nat.floor_le hx, Nat.lt_floor_add_one x⟩

theorem three (n : ℕ) : ¬ (a n = a (n + 1) ∧ a (n + 1) = a (n + 2)) := by
  unfold a
  have h0 := fl ((n : ℝ) * Real.sqrt 8) (by positivity)
  have h1 := fl (((n + 1 : ℕ) : ℝ) * Real.sqrt 8) (by positivity)
  have h2 := fl (((n + 2 : ℕ) : ℝ) * Real.sqrt 8) (by positivity)
  set k0 := ⌊(n : ℝ) * Real.sqrt 8⌋₊
  set k1 := ⌊((n + 1 : ℕ) : ℝ) * Real.sqrt 8⌋₊
  set k2 := ⌊((n + 2 : ℕ) : ℝ) * Real.sqrt 8⌋₊
  push_cast at h1 h2
  have lo := s8_lo
  have hi := s8_hi
  have a1 : (k0 : ℝ) + 1 < k1 := by nlinarith
  have a2 : (k1 : ℝ) < k0 + 4 := by nlinarith
  have a3 : (k1 : ℝ) + 1 < k2 := by nlinarith
  have a4 : (k2 : ℝ) < k1 + 4 := by nlinarith
  have a5 : (k0 : ℝ) + 4 < k2 := by nlinarith
  have b1 : k0 + 1 < k1 := by exact_mod_cast a1
  have b2 : k1 < k0 + 4 := by exact_mod_cast a2
  have b3 : k1 + 1 < k2 := by exact_mod_cast a3
  have b4 : k2 < k1 + 4 := by exact_mod_cast a4
  have b5 : k0 + 4 < k2 := by exact_mod_cast a5
  omega

theorem frac_form (n : ℕ) (hn : 1 ≤ n) :
    a n = if 1 / 2 < Int.fract (Real.sqrt 2 * n) then 1 else 0 := by
  unfold a
  set y := Real.sqrt 2 * n with hy
  have hy0 : 0 ≤ y := by positivity
  have e : (n : ℝ) * Real.sqrt 8 = 2 * y := by rw [s8_eq, hy]; ring
  rw [e]
  set m := ⌊y⌋₊ with hm
  have hfr : Int.fract y = y - m := by
    rw [Int.fract, ← Int.natCast_floor_eq_floor hy0]
    push_cast
    ring
  have hm1 := fl y hy0
  rw [← hm] at hm1
  have hne : y ≠ m + 1 / 2 := by
    intro h
    have hirr : Irrational y := by
      rw [hy]
      exact irrational_sqrt_two.mul_natCast (by omega)
    exact hirr.ne_rat ((m : ℚ) + 1 / 2) (by rw [h]; push_cast; ring)
  rw [hfr]
  split_ifs with h
  · have : ⌊2 * y⌋₊ = 2 * m + 1 := by
      rw [Nat.floor_eq_iff (by positivity)]
      push_cast
      constructor <;> linarith
    rw [this]
    omega
  · have hlt : y < m + 1 / 2 := lt_of_le_of_ne (by linarith) hne
    have : ⌊2 * y⌋₊ = 2 * m := by
      rw [Nat.floor_eq_iff (by positivity)]
      push_cast
      constructor <;> linarith
    rw [this]
    omega

end PA197879

theorem OMA.solution : type_of% @OMA.S_oeis_a197879.main :=
  ⟨PA197879.frac_form, fun n _ => PA197879.three n⟩
