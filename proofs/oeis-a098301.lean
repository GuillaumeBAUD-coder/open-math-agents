import OMAStatements.S_oeis_a098301
import Mathlib

/-!
# A098301: the identity fails at `n = 1` with the current offsets

`A007655(2) = 1`, `A046184(1) = 1`, `A055793(3) = 4` and `a(2) = (T(2,7) - 1)/6 = 16`, so the
identity at `n = 1` would say `4 * 1 + 1 = 4 + 16`.
-/

namespace A098301Disproof

open OMA.S_oeis_a098301

theorem nth_of_count {p : ℕ → Prop} [DecidablePred p] (n c : ℕ) (hp : p n)
    (hc : Nat.count p n = c) : Nat.nth p c = n := by
  rw [← hc]
  exact Nat.nth_count hp

theorem sq4 : IsSquare (4 : ℕ) := ⟨2, rfl⟩

theorem sq1 : IsSquare (1 : ℕ) := ⟨1, rfl⟩

theorem nsq (n r : ℕ) (h1 : r * r < n) (h2 : n < (r + 1) * (r + 1)) : ¬ IsSquare n := by
  rintro ⟨s, rfl⟩
  have a1 : r < s := Nat.mul_self_lt_mul_self_iff.mp h1
  have a2 : s < r + 1 := Nat.mul_self_lt_mul_self_iff.mp h2
  omega

theorem v1 : A007654 2 = 3 := by
  classical
  apply nth_of_count
  · exact ⟨by norm_num, by norm_num⟩
  · simp [Nat.count_succ, IsA007654]

theorem v2 : A046184 1 = 1 := by
  classical
  apply nth_of_count
  · exact ⟨le_refl 1, by norm_num⟩
  · simp [Nat.count_succ, IsA046184]

theorem v3 : A055793 3 = 4 := by
  classical
  apply nth_of_count
  · exact ⟨sq4, by norm_num⟩
  · have h2 : ¬ IsSquare (2 : ℕ) := nsq 2 1 (by norm_num) (by norm_num)
    have h3 : ¬ IsSquare (3 : ℕ) := nsq 3 1 (by norm_num) (by norm_num)
    simp [Nat.count_succ, IsA055793, h2, h3]

theorem v4 : a 2 = 16 := by
  simp [a, Polynomial.Chebyshev.T_two]

end A098301Disproof

open OMA.S_oeis_a098301 A098301Disproof in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a098301.main) := by
  intro h
  have h1 := h 1 (le_refl 1)
  have e2 : (1 : ℕ) + 1 = 2 := rfl
  have e3 : (1 : ℕ) + 2 = 3 := rfl
  rw [e2, e3, v2, v3, v4, A007655, v1] at h1
  norm_num at h1
