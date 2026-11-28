import OMAStatements.S_oeis_a197879
import Mathlib

open OMA.S_oeis_a197879

namespace P197879

lemma s8 : Real.sqrt 8 = 2 * Real.sqrt 2 := by
  rw [show (8 : ℝ) = 2 ^ 2 * 2 by norm_num, Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]

lemma part1 (n : ℕ) (hn : 1 ≤ n) : a n = if 1 / 2 < Int.fract (Real.sqrt 2 * n) then 1 else 0 := by
  unfold a
  set y := Real.sqrt 2 * n with hy
  have y0 : 0 ≤ y := by positivity
  set m := ⌊y⌋₊ with hm
  have m1 : (m : ℝ) ≤ y := Nat.floor_le y0
  have m2 : y < m + 1 := Nat.lt_floor_add_one y
  have hf : Int.fract y = y - m := by
    rw [Int.fract, show ⌊y⌋ = (m : ℤ) from ?_]
    · push_cast; ring
    · rw [Int.floor_eq_iff]; push_cast; exact ⟨m1, m2⟩
  have e2 : (n : ℝ) * Real.sqrt 8 = 2 * y := by rw [s8, hy]; ring
  rw [e2, hf]
  have hne : y - m ≠ 1 / 2 := by
    intro h
    have hi : Irrational (Real.sqrt 2 * n) := irrational_sqrt_two.mul_natCast (by omega)
    apply hi.ne_rat ((m : ℚ) + 1 / 2)
    rw [← hy]; push_cast; linarith
  split_ifs with h
  · have : ⌊2 * y⌋₊ = 2 * m + 1 := by
      rw [Nat.floor_eq_iff (by positivity)]; push_cast; constructor <;> linarith
    rw [this]; omega
  · have h' : y - m < 1 / 2 := lt_of_le_of_ne (not_lt.mp h) hne
    have : ⌊2 * y⌋₊ = 2 * m := by
      rw [Nat.floor_eq_iff (by positivity)]; push_cast; constructor <;> linarith
    rw [this]; omega

lemma sb : 1.414 < Real.sqrt 2 ∧ Real.sqrt 2 < 1.4143 := by
  constructor
  · rw [Real.lt_sqrt (by norm_num)]; norm_num
  · rw [Real.sqrt_lt' (by norm_num)]; norm_num

lemma step (y : ℝ) : ∃ z : ℤ, Int.fract (y + Real.sqrt 2) = Int.fract y + Real.sqrt 2 - z ∧ 1 ≤ z ∧ z ≤ 2 := by
  refine ⟨⌊y + Real.sqrt 2⌋ - ⌊y⌋, ?_, ?_⟩
  · rw [Int.fract, Int.fract]; push_cast; ring
  · obtain ⟨b1, b2⟩ := sb
    have f1 := Int.fract_nonneg (y + Real.sqrt 2)
    have f2 := Int.fract_lt_one (y + Real.sqrt 2)
    have f3 := Int.fract_nonneg y
    have f4 := Int.fract_lt_one y
    have e : ((⌊y + Real.sqrt 2⌋ - ⌊y⌋ : ℤ) : ℝ) = Int.fract y + Real.sqrt 2 - Int.fract (y + Real.sqrt 2) := by
      rw [Int.fract, Int.fract]; push_cast; ring
    have l : (0 : ℝ) < ((⌊y + Real.sqrt 2⌋ - ⌊y⌋ : ℤ) : ℝ) := by rw [e]; linarith
    have u : ((⌊y + Real.sqrt 2⌋ - ⌊y⌋ : ℤ) : ℝ) < 3 := by rw [e]; linarith
    have l' : (0 : ℤ) < ⌊y + Real.sqrt 2⌋ - ⌊y⌋ := by exact_mod_cast l
    have u' : ⌊y + Real.sqrt 2⌋ - ⌊y⌋ < (3 : ℤ) := by exact_mod_cast u
    constructor <;> omega

end P197879

open P197879 in
theorem OMA.solution : type_of% @OMA.S_oeis_a197879.main := by
  refine ⟨part1, ?_⟩
  intro n hn ⟨h1, h2⟩
  rw [part1 n hn, part1 (n + 1) (by omega)] at h1
  rw [part1 (n + 1) (by omega), part1 (n + 2) (by omega)] at h2
  have q1 : Real.sqrt 2 * ((n + 1 : ℕ) : ℝ) = Real.sqrt 2 * n + Real.sqrt 2 := by push_cast; ring
  have q2 : Real.sqrt 2 * ((n + 2 : ℕ) : ℝ) = Real.sqrt 2 * ((n + 1 : ℕ) : ℝ) + Real.sqrt 2 := by push_cast; ring
  obtain ⟨z1, e1, l1, u1⟩ := step (Real.sqrt 2 * n)
  obtain ⟨z2, e2, l2, u2⟩ := step (Real.sqrt 2 * ((n + 1 : ℕ) : ℝ))
  rw [← q1] at e1
  rw [← q2] at e2
  obtain ⟨b1, b2⟩ := sb
  have f0 := Int.fract_nonneg (Real.sqrt 2 * n)
  have f0' := Int.fract_lt_one (Real.sqrt 2 * n)
  have f1 := Int.fract_nonneg (Real.sqrt 2 * ((n + 1 : ℕ) : ℝ))
  have f1' := Int.fract_lt_one (Real.sqrt 2 * ((n + 1 : ℕ) : ℝ))
  have f2 := Int.fract_nonneg (Real.sqrt 2 * ((n + 2 : ℕ) : ℝ))
  have f2' := Int.fract_lt_one (Real.sqrt 2 * ((n + 2 : ℕ) : ℝ))
  have hz1 : z1 = 1 ∨ z1 = 2 := by omega
  have hz2 : z2 = 1 ∨ z2 = 2 := by omega
  rcases hz1 with rfl | rfl <;> rcases hz2 with rfl | rfl <;> push_cast at * <;>
    split_ifs at h1 h2 with c0 c1 c2 <;> simp at h1 h2 <;> linarith
