import OMAStatements.S_oeis_a341254
import Mathlib

theorem OMA.solution : type_of% @OMA.S_oeis_a341254.main := by
  intro n hn
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  have hs1 : Real.sqrt 5 < 9 / 4 := by nlinarith
  have hs2 : 2 < Real.sqrt 5 := by nlinarith
  have hrdef : OMA.S_oeis_a341254.r = (2 + Real.sqrt 5) / 2 := rfl
  set r := OMA.S_oeis_a341254.r with hr
  have hrr : r ^ 2 = 2 * r + 1 / 4 := by rw [hrdef]; nlinarith
  have hr2 : 2 < r := by rw [hrdef]; linarith
  have hr3 : r - 2 < 1 / 8 := by rw [hrdef]; linarith
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set m : ℤ := ⌊r * (n : ℝ)⌋ with hm
  have hm1 : (m : ℝ) ≤ r * n := Int.floor_le _
  have hm2 : r * n < m + 1 := Int.lt_floor_add_one _
  have hne : (m : ℝ) ≠ r * n := by
    intro h
    have hirr : Irrational (Real.sqrt 5) := by
      have := Nat.Prime.irrational_sqrt (show Nat.Prime 5 by norm_num)
      simpa using this
    apply hirr
    refine ⟨((2 * m - 2 * n : ℤ) : ℚ) / (n : ℚ), ?_⟩
    have hn0 : (n : ℝ) ≠ 0 := by positivity
    push_cast
    rw [div_eq_iff hn0]
    rw [hrdef] at h
    linarith
  have hf0 : 0 < r * n - m := by
    rcases lt_or_eq_of_le hm1 with h | h
    · linarith
    · exact absurd h hne
  set A : ℤ := ⌊r * (m : ℝ)⌋ with hA
  have ha : OMA.S_oeis_a341254.a n = A := rfl
  have hA1 : (A : ℝ) ≤ r * m := Int.floor_le _
  have hA2 : r * m < A + 1 := Int.lt_floor_add_one _
  set q : ℤ := 4 * (2 * m - A) + n with hq
  have hqr : (q : ℝ) / 4 = (r * m - A) + (r - 2) * (r * n - m) := by
    rw [hq]
    push_cast
    nlinarith
  have hq0 : (0 : ℝ) < q := by nlinarith
  have hq5 : (q : ℝ) < 5 := by nlinarith
  have hq1 : (1 : ℤ) ≤ q := by
    have : (0 : ℤ) < q := by exact_mod_cast hq0
    omega
  have hq4 : q ≤ 4 := by
    have : q < 5 := by exact_mod_cast hq5
    omega
  have hq1' : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  have hq4' : (q : ℝ) ≤ 4 := by exact_mod_cast hq4
  have hV : (n : ℝ) * r ^ 2 - A = 2 * (r * n - m) + q / 4 := by
    rw [hq]
    push_cast
    nlinarith
  rw [ha, hV]
  constructor <;> nlinarith
