import OMAStatements.S_oeis_a052227
import Mathlib

open OMA.S_oeis_a052227

theorem OMA.solution : type_of% @OMA.S_oeis_a052227.main := by
  have key : ∀ m : ℕ, ((3 * (m + 1)).choose (m + 1) : ℚ) =
      ((3 * m).choose m : ℚ) * ((3 * m + 1) * (3 * m + 2) * (3 * m + 3)) /
        ((m + 1) * (2 * m + 1) * (2 * m + 2)) := by
    intro m
    have h1 := Nat.add_one_mul_choose_eq (3 * m + 2) m
    have h2 := Nat.choose_mul_succ_eq (3 * m + 1) m
    have h3 := Nat.choose_mul_succ_eq (3 * m) m
    have e1 : 3 * (m + 1) = 3 * m + 2 + 1 := by ring
    have e2 : 3 * m + 1 + 1 - m = 2 * m + 2 := by omega
    have e3 : 3 * m + 1 - m = 2 * m + 1 := by omega
    rw [e2] at h2; rw [e3] at h3
    rw [e1]
    have q1 : ((3 * m + 2 + 1 : ℕ) : ℚ) * ((3 * m + 2).choose m : ℚ) = ((3 * m + 2 + 1).choose (m + 1) : ℚ) * ((m + 1 : ℕ) : ℚ) := by exact_mod_cast h1
    have q2 : ((3 * m + 1).choose m : ℚ) * ((3 * m + 1 + 1 : ℕ) : ℚ) = ((3 * m + 1 + 1).choose m : ℚ) * ((2 * m + 2 : ℕ) : ℚ) := by exact_mod_cast h2
    have q3 : ((3 * m).choose m : ℚ) * ((3 * m + 1 : ℕ) : ℚ) = ((3 * m + 1).choose m : ℚ) * ((2 * m + 1 : ℕ) : ℚ) := by exact_mod_cast h3
    push_cast at q1 q2 q3
    have hm1 : ((m:ℚ) + 1) ≠ 0 := by positivity
    have hm2 : (2 * (m:ℚ) + 1) ≠ 0 := by positivity
    have hm3 : (2 * (m:ℚ) + 2) ≠ 0 := by positivity
    rw [eq_div_iff (by positivity)]
    have : ((3 * m + 2 + 1).choose (m + 1) : ℚ) = (3 * m + 3) * ((3 * m + 2).choose m : ℚ) / (m + 1) := by
      rw [eq_div_iff hm1]; linarith
    rw [this]
    have : ((3 * m + 2).choose m : ℚ) = (3 * m + 2) * ((3 * m + 1).choose m : ℚ) / (2 * m + 2) := by
      rw [eq_div_iff hm3]; linarith
    rw [this]
    have : ((3 * m + 1).choose m : ℚ) = (3 * m + 1) * ((3 * m).choose m : ℚ) / (2 * m + 1) := by
      rw [eq_div_iff hm2]; linarith
    rw [this]
    field_simp
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have e1 : m + 2 - 1 = m + 1 := by omega
  have e2 : m + 2 - 2 = m := by omega
  rw [e1, e2]
  unfold a
  have k1 := key m
  have k2 := key (m + 1)
  have e3 : m + 2 = m + 1 + 1 := by ring
  rw [e3, k2, k1]
  push_cast
  field_simp
  ring
