import OMAStatements.S_mo_201980
import Mathlib

open OMA.S_mo_201980

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_201980.main) := by
  rintro ⟨k, hk, n, hn, x, y, z, hx, hy, hz, h⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hk
  have hk8 : k ≤ 8 := by omega
  set M := max x (max y z) with hM
  have hxM : x ≤ M := le_max_left _ _
  have hyM : y ≤ M := le_trans (le_max_left _ _) (le_max_right _ _)
  have hzM : z ≤ M := le_trans (le_max_right _ _) (le_max_right _ _)
  have hMpos : 0 < M := lt_of_lt_of_le hx hxM
  have hMn : M ^ n ≤ x ^ n + y ^ n + z ^ n := by
    rcases le_total y z with h1 | h1 <;> rcases le_total x (max y z) with h2 | h2
    all_goals
      first
      | (have : M = x := by simp [hM]; omega
         rw [this]; omega)
      | (have : M = y := by simp [hM]; omega
         rw [this]; omega)
      | (have : M = z := by simp [hM]; omega
         rw [this]; omega)
  have hrhs : k * x * y * z ≤ 8 * M ^ 3 := by
    have := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul hk8 hxM) hyM) hzM
    calc k * x * y * z ≤ 8 * M * M * M := this
      _ = 8 * M ^ 3 := by ring
  have hkey : M ^ (n - 3) * M ^ 3 ≤ 8 * M ^ 3 := by
    rw [← pow_add, Nat.sub_add_cancel (by omega)]; omega
  have hM3 : 0 < M ^ 3 := pow_pos hMpos 3
  have hle : M ^ (n - 3) ≤ 8 := le_of_mul_le_mul_right hkey hM3
  have hM8 : M ≤ 8 := by
    have : M ≤ M ^ (n - 3) := Nat.le_self_pow (by omega) M
    omega
  rcases Nat.lt_or_ge M 2 with hM1 | hM2
  · have hx1 : x = 1 := by omega
    have hy1 : y = 1 := by omega
    have hz1 : z = 1 := by omega
    subst hx1 hy1 hz1
    simp at h
    omega
  · have hn6 : n ≤ 6 := by
      have h2 : 2 ^ (n - 3) ≤ M ^ (n - 3) := Nat.pow_le_pow_left hM2 _
      have : 2 ^ (n - 3) ≤ 2 ^ 3 := by omega
      have := (Nat.pow_le_pow_iff_right (by norm_num)).1 this
      omega
    have hx8 : x < 9 := by omega
    have hy8 : y < 9 := by omega
    have hz8 : z < 9 := by omega
    have hfin : ∀ n, 4 ≤ n → n ≤ 6 → ∀ x < 9, ∀ y < 9, ∀ z < 9,
        x = 0 ∨ y = 0 ∨ z = 0 ∨
        (x ^ n + y ^ n + z ^ n ≠ 4 * x * y * z ∧ x ^ n + y ^ n + z ^ n ≠ 7 * x * y * z ∧
        x ^ n + y ^ n + z ^ n ≠ 8 * x * y * z) := by
      intro n h4 h6
      interval_cases n <;> decide
    have := hfin n hn hn6 x hx8 y hy8 z hz8
    rcases hk with rfl | rfl | rfl <;> omega
