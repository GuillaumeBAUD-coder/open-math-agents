import OMAStatements.S_mo_201980
import Mathlib

-- Problem: mo-201980, is x^n + y^n + z^n = k x y z solvable in positive integers for some
-- n >= 4 and some k in {4, 7, 8}?
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- No. Let m = max(x, y, z). Then m^n <= x^n + y^n + z^n = k x y z <= 8 m^3, so
-- m^(n-3) <= 8. If m = 1 then x = y = z = 1 and k = 3, which is excluded. If m >= 2 then
-- 2^(n-3) <= 8 and m <= 8, so n <= 6 and x, y, z <= 8, and a finite check finishes.

namespace MO201980

theorem fin_check : ∀ n ∈ Finset.Icc 4 6, ∀ x ∈ Finset.Icc 1 8, ∀ y ∈ Finset.Icc 1 8,
    ∀ z ∈ Finset.Icc 1 8, ∀ k ∈ ({4, 7, 8} : Finset ℕ),
      x ^ n + y ^ n + z ^ n ≠ k * x * y * z := by
  decide +kernel

end MO201980

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_201980.main) := by
  rintro ⟨k, hk, n, hn, x, y, z, hx, hy, hz, heq⟩
  have hk' : k = 4 ∨ k = 7 ∨ k = 8 := by simpa using hk
  have hk8 : k ≤ 8 := by omega
  obtain ⟨m, hxm, hym, hzm, hmeq⟩ :
      ∃ m, x ≤ m ∧ y ≤ m ∧ z ≤ m ∧ (m = x ∨ m = y ∨ m = z) :=
    ⟨max x (max y z), by omega, by omega, by omega, by omega⟩
  have h1 : m ^ n ≤ x ^ n + y ^ n + z ^ n := by
    rcases hmeq with h | h | h
    · rw [h]
      omega
    · rw [h]
      omega
    · rw [h]
      omega
  have h2 : k * x * y * z ≤ 8 * m ^ 3 := by
    calc k * x * y * z ≤ 8 * m * m * m :=
          Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul hk8 hxm) hym) hzm
      _ = 8 * m ^ 3 := by ring
  have h3 : m ^ n ≤ 8 * m ^ 3 := by omega
  by_cases hm1 : m = 1
  · have ex : x = 1 := by omega
    have ey : y = 1 := by omega
    have ez : z = 1 := by omega
    subst ex ey ez
    simp at heq
    omega
  · have hm2 : 2 ≤ m := by omega
    obtain ⟨d, hd⟩ : ∃ d, n = d + 3 := ⟨n - 3, by omega⟩
    subst hd
    have h4 : m ^ d * m ^ 3 ≤ 8 * m ^ 3 := by
      rw [← pow_add]
      exact h3
    have h5 : m ^ d ≤ 8 := Nat.le_of_mul_le_mul_right h4 (by positivity)
    have h6 : 2 ^ d ≤ m ^ d := Nat.pow_le_pow_left hm2 d
    have hd3 : d ≤ 3 := by
      by_contra hcon
      have h7 : 2 ^ 4 ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hm8 : m ≤ 8 := by
      have h8 : m ^ 1 ≤ m ^ d := Nat.pow_le_pow_right (by omega) (by omega)
      rw [pow_one] at h8
      omega
    exact MO201980.fin_check (d + 3) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩) x
      (Finset.mem_Icc.mpr ⟨by omega, by omega⟩) y (Finset.mem_Icc.mpr ⟨by omega, by omega⟩) z
      (Finset.mem_Icc.mpr ⟨by omega, by omega⟩) k hk heq
