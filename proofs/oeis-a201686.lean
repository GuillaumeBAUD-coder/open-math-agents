import OMAStatements.S_oeis_a201686
import Mathlib

open OMA.S_oeis_a201686

theorem OMA.solution : type_of% @OMA.S_oeis_a201686.main := by
  have cS : ∀ k : ℕ, ((Nat.centralBinom (k + 1) : ℕ) : ℚ) =
      (Nat.centralBinom k : ℚ) * (2 * (2 * k + 1)) / (k + 1) := by
    intro k
    have h := Nat.succ_mul_centralBinom_succ k
    have h' : ((k + 1 : ℕ) : ℚ) * (Nat.centralBinom (k + 1) : ℚ) = 2 * (2 * (k : ℚ) + 1) * Nat.centralBinom k := by
      exact_mod_cast h
    push_cast at h'
    rw [eq_div_iff (by positivity)]; linarith
  have aE : ∀ k : ℕ, ((a (2 * k) : ℤ) : ℚ) = (Nat.centralBinom k : ℚ) - 2 := by
    intro k
    rw [a, show 2 * k / 2 = k by omega, Nat.centralBinom_eq_two_mul_choose]
    push_cast; ring
  have aO : ∀ k : ℕ, ((a (2 * k + 1) : ℤ) : ℚ) = (Nat.centralBinom k : ℚ) * (2 * k + 1) / (k + 1) - 2 := by
    intro k
    rw [a, show (2 * k + 1) / 2 = k by omega]
    have h := Nat.choose_mul_succ_eq (2 * k) k
    rw [show 2 * k + 1 - k = k + 1 by omega, ← Nat.centralBinom_eq_two_mul_choose] at h
    have h' : (Nat.centralBinom k : ℚ) * ((2 * k + 1 : ℕ) : ℚ) = ((2 * k + 1).choose k : ℚ) * ((k + 1 : ℕ) : ℚ) := by
      exact_mod_cast h
    push_cast at h' ⊢
    have : ((2 * k + 1).choose k : ℚ) = (Nat.centralBinom k : ℚ) * (2 * k + 1) / (k + 1) := by
      rw [eq_div_iff (by positivity)]; linarith
    rw [this]
  intro n hn
  rw [← Int.cast_inj (α := ℚ)]
  push_cast
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
    rw [show 2 * (j + 2) - 1 = 2 * (j + 1) + 1 by omega, show 2 * (j + 2) - 2 = 2 * (j + 1) by omega,
      show 2 * (j + 2) - 3 = 2 * j + 1 by omega, show 2 * (j + 2) - 4 = 2 * j by omega,
      aE, aE, aE, aO, aO, show j + 2 = j + 1 + 1 by ring, cS, cS]
    push_cast
    field_simp
    ring
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
    rw [show 2 * (j + 2) + 1 - 1 = 2 * (j + 2) by omega, show 2 * (j + 2) + 1 - 2 = 2 * (j + 1) + 1 by omega,
      show 2 * (j + 2) + 1 - 3 = 2 * (j + 1) by omega, show 2 * (j + 2) + 1 - 4 = 2 * j + 1 by omega,
      aE, aE, aO, aO, aO, show j + 2 = j + 1 + 1 by ring, cS, cS]
    push_cast
    field_simp
    ring
