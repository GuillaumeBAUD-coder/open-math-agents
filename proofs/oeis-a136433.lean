import OMAStatements.S_oeis_a136433

open OMA.S_oeis_a136433

def dd : ℕ → ℕ
  | 0 => 13
  | 1 => 9
  | 2 => 7
  | 3 => 17
  | 4 => 6
  | _ => 8

lemma key (m : ℕ) : a (m + 4) = 6 * a (m + 1) + dd (m % 6) := by
  have e1 : a (m + 2) = a (m + 1) * (m % 3 + 1) + (m % 2 + 1) := rfl
  have e2 : a (m + 3) = a (m + 2) * ((m + 1) % 3 + 1) + ((m + 1) % 2 + 1) := rfl
  have e3 : a (m + 4) = a (m + 3) * ((m + 2) % 3 + 1) + ((m + 2) % 2 + 1) := rfl
  have hr : m % 6 < 6 := Nat.mod_lt _ (by norm_num)
  rw [e3, e2, e1]
  interval_cases h : m % 6
  · rw [show m % 3 = 0 by omega, show m % 2 = 0 by omega, show (m + 1) % 3 = 1 by omega,
      show (m + 1) % 2 = 1 by omega, show (m + 2) % 3 = 2 by omega, show (m + 2) % 2 = 0 by omega]
    simp [dd]; ring
  · rw [show m % 3 = 1 by omega, show m % 2 = 1 by omega, show (m + 1) % 3 = 2 by omega,
      show (m + 1) % 2 = 0 by omega, show (m + 2) % 3 = 0 by omega, show (m + 2) % 2 = 1 by omega]
    simp [dd]; ring
  · rw [show m % 3 = 2 by omega, show m % 2 = 0 by omega, show (m + 1) % 3 = 0 by omega,
      show (m + 1) % 2 = 1 by omega, show (m + 2) % 3 = 1 by omega, show (m + 2) % 2 = 0 by omega]
    simp [dd]; ring
  · rw [show m % 3 = 0 by omega, show m % 2 = 1 by omega, show (m + 1) % 3 = 1 by omega,
      show (m + 1) % 2 = 0 by omega, show (m + 2) % 3 = 2 by omega, show (m + 2) % 2 = 1 by omega]
    simp [dd]; ring
  · rw [show m % 3 = 1 by omega, show m % 2 = 0 by omega, show (m + 1) % 3 = 2 by omega,
      show (m + 1) % 2 = 1 by omega, show (m + 2) % 3 = 0 by omega, show (m + 2) % 2 = 0 by omega]
    simp [dd]; ring
  · rw [show m % 3 = 2 by omega, show m % 2 = 1 by omega, show (m + 1) % 3 = 0 by omega,
      show (m + 1) % 2 = 0 by omega, show (m + 2) % 3 = 1 by omega, show (m + 2) % 2 = 1 by omega]
    simp [dd]; ring

theorem OMA.solution : type_of% @OMA.S_oeis_a136433.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 10 := ⟨n - 10, by omega⟩
  have k1 := key (m + 6)
  have k2 := key m
  rw [show (m + 6) % 6 = m % 6 by omega] at k1
  rw [show m + 10 - 3 = m + 7 by omega, show m + 10 - 6 = m + 4 by omega,
    show m + 10 - 9 = m + 1 by omega, show m + 10 = m + 6 + 4 by omega,
    show m + 7 = m + 6 + 1 by omega]
  rw [k1, k2]
  push_cast
  ring
