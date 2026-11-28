import OMAStatements.S_oeis_a122122
import Mathlib

open OMA.S_oeis_a122122 in
theorem OMA.solution : type_of% @OMA.S_oeis_a122122.main := by
  have A (j : ℕ) : a (j+1) = ((j:ℚ)+3)/8 * 4^(j+1) - (j+1)*(4*j+1)/(4*(2*j+1)) * (j+1).centralBinom := by
    have : 1 - 2*((j:ℚ)+1) ≠ 0 := fun h => by linarith [(j.cast_nonneg : (0:ℚ) ≤ j)]
    simp [a, zpow_sub₀, zpow_add₀, ← Nat.centralBinom_eq_two_mul_choose]
    field_simp
    ring
  have h (j : ℕ) : ((j+1).centralBinom : ℚ) = 2*(2*j+1)/(j+1) * j.centralBinom := by
    rw [div_mul_eq_mul_div, eq_div_iff (by positivity)]
    exact mod_cast (by linarith [j.succ_mul_centralBinom_succ])
  constructor <;> intro n hn <;> obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn <;> simp [A, h] <;> field_simp <;> ring
