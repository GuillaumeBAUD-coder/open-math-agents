import OMAStatements.S_oeis_a341239

-- OEIS A341239. Credit: @ArtemCherbaev
open OMA.S_oeis_a341239

theorem OMA.solution : type_of% @OMA.S_oeis_a341239.main := by
  intro n hn
  let m : ℤ := ⌊s * (n : ℝ)⌋
  let x : ℝ := s * (n : ℝ) - m
  have hx₀ : 0 < x := by
    have hirr : Irrational (s * (n : ℝ)) := irrational_sqrt_two.mul_natCast (by omega)
    exact sub_pos.mpr (lt_of_le_of_ne (Int.floor_le _) (hirr.ne_int m).symm)
  have hx₁ : x < 1 := by
    dsimp only [x]
    linarith [Int.lt_floor_add_one (s * (n : ℝ))]
  have hs : s * s = 2 := by
    simpa only [s, ← sq] using Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hprod : r * (m : ℝ) = m + 2 * (n : ℝ) - s * x := by
    dsimp only [r, x]
    change (1 + s) * (m : ℝ) = _
    linear_combination (n : ℝ) * hs
  have hsmall : 0 < s * x := mul_pos (Real.sqrt_pos.2 (by norm_num)) hx₀
  have hlarge : s * x < 2 := by
    have hlt : s < 2 := by
      dsimp [s]
      linarith [Real.sqrt_two_lt_three_halves]
    exact (mul_lt_mul_of_pos_left hx₁ (Real.sqrt_pos.2 (by norm_num))).trans_le
      (by simpa using hlt.le)
  have hlo : (a n : ℝ) ≤ r * (m : ℝ) := Int.floor_le _
  have hhi : r * (m : ℝ) < (a n : ℝ) + 1 := Int.lt_floor_add_one _
  -- The integer part of the error is either one or two.
  let k : ℤ := m + 2 * (n : ℤ) - a n
  have hkcast : (k : ℝ) = (m : ℝ) + 2 * n - a n := by simp [k]
  have hk₀ : (0 : ℝ) < k := by linarith
  have hk₃ : (k : ℝ) < 3 := by linarith
  have hk₁ : (1 : ℤ) ≤ k := by
    have : (0 : ℤ) < k := by exact_mod_cast hk₀
    omega
  have hk₂ : k ≤ (2 : ℤ) := by
    have : k < (3 : ℤ) := by exact_mod_cast hk₃
    omega
  have herr : r * s * (n : ℝ) - a n = x + k := by
    rw [hkcast]
    dsimp only [x]
    change (1 + s) * s * (n : ℝ) - _ = _
    linear_combination (n : ℝ) * hs
  rw [herr]
  constructor
  · linarith [show (1 : ℝ) ≤ k by exact_mod_cast hk₁]
  · linarith [show (k : ℝ) ≤ 2 by exact_mod_cast hk₂]
