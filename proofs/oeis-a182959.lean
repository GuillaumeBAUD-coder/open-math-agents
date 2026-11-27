import OMAStatements.S_oeis_a182959
import Mathlib

lemma OMA.cb (m : ℕ) : ((m + 1).centralBinom : ℚ) = 2 * (2 * m + 1) / (m + 1) * m.centralBinom := by
  have h := Nat.succ_mul_centralBinom_succ m
  have h' : ((m + 1 : ℕ) : ℚ) * ((m + 1).centralBinom : ℚ) = 2 * (2 * m + 1) * m.centralBinom := by
    exact_mod_cast h
  have : ((m : ℚ) + 1) ≠ 0 := by positivity
  push_cast at h'
  field_simp
  linarith

theorem OMA.solution : type_of% @OMA.S_oeis_a182959.main := by
  refine ⟨4, fun n hn => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 + 2 := ⟨n - 4, by omega⟩
  rw [show m + 2 + 2 - 1 = m + 1 + 2 by omega, show m + 2 + 2 - 2 = m + 2 by omega]
  simp only [OMA.S_oeis_a182959.a]
  rw [show m + 2 + 1 = m + 1 + 1 + 1 by ring, OMA.cb (m + 1 + 1), show m + 1 + 1 = m + 1 + 1 by rfl,
    OMA.cb (m + 1)]
  have : ((m : ℚ) + 1) ≠ 0 := by positivity
  have : ((m : ℚ) + 1 + 1) ≠ 0 := by positivity
  have : ((m : ℚ) + 2) ≠ 0 := by positivity
  have : ((m : ℚ) + 3) ≠ 0 := by positivity
  have : ((m : ℚ) + 1 + 2) ≠ 0 := by positivity
  have : ((m : ℚ) + 1 + 3) ≠ 0 := by positivity
  have : ((m : ℚ) + 2 + 2) ≠ 0 := by positivity
  have : ((m : ℚ) + 2 + 3) ≠ 0 := by positivity
  push_cast
  field_simp
  ring
