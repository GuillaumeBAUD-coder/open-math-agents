import OMAStatements.S_oeis_a121636

namespace OMA

open OMA.S_oeis_a121636

theorem rec636 (n : ℕ) :
    a (n + 3) = ((n : ℤ) + 3) * ((n + 1).factorial : ℤ) + ((n : ℤ) + 2) * a (n + 2) := rfl

theorem fact636 (m k : ℕ) :
    ((m + (k + 1)).factorial : ℤ) = ((m : ℤ) + (k + 1)) * ((m + k).factorial : ℤ) := by
  have e : m + (k + 1) = (m + k) + 1 := by omega
  rw [e, Nat.factorial_succ]
  push_cast
  ring

theorem key636 (m : ℕ) :
    a (m + 5) + (-2 * ((m : ℤ) + 5) + 3) * a (m + 4)
      + (((m : ℤ) + 5) ^ 2 - 5 * ((m : ℤ) + 5) + 7) * a (m + 3)
      + ((((m : ℤ) + 5) - 3) ^ 2) * a (m + 2) = 0 := by
  have h5 : a (m + 5) = ((m : ℤ) + 5) * ((m + 3).factorial : ℤ) + ((m : ℤ) + 4) * a (m + 4) := by
    have e1 : m + 2 + 3 = m + 5 := by omega
    have e2 : m + 2 + 1 = m + 3 := by omega
    have e3 : m + 2 + 2 = m + 4 := by omega
    have c1 : ((m + 2 : ℕ) : ℤ) + 3 = (m : ℤ) + 5 := by omega
    have c2 : ((m + 2 : ℕ) : ℤ) + 2 = (m : ℤ) + 4 := by omega
    simpa only [e1, e2, e3, c1, c2] using rec636 (m + 2)
  have h4 : a (m + 4) = ((m : ℤ) + 4) * ((m + 2).factorial : ℤ) + ((m : ℤ) + 3) * a (m + 3) := by
    have e1 : m + 1 + 3 = m + 4 := by omega
    have e2 : m + 1 + 1 = m + 2 := by omega
    have e3 : m + 1 + 2 = m + 3 := by omega
    have c1 : ((m + 1 : ℕ) : ℤ) + 3 = (m : ℤ) + 4 := by omega
    have c2 : ((m + 1 : ℕ) : ℤ) + 2 = (m : ℤ) + 3 := by omega
    simpa only [e1, e2, e3, c1, c2] using rec636 (m + 1)
  have h3 : a (m + 3) = ((m : ℤ) + 3) * ((m + 1).factorial : ℤ) + ((m : ℤ) + 2) * a (m + 2) :=
    rec636 m
  have f3 : ((m + 3).factorial : ℤ) = ((m : ℤ) + 3) * ((m + 2).factorial : ℤ) := fact636 m 2
  have f2 : ((m + 2).factorial : ℤ) = ((m : ℤ) + 2) * ((m + 1).factorial : ℤ) := fact636 m 1
  rw [h5, h4, h3]
  rw [f3, f2]
  ring

end OMA

open OMA.S_oeis_a121636 in
theorem OMA.solution : type_of% @OMA.S_oeis_a121636.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  rw [show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega,
    show m + 5 - 3 = m + 2 by omega]
  push_cast
  exact OMA.key636 m
