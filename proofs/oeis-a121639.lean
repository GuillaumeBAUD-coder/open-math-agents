import OMAStatements.S_oeis_a121639

namespace OMA

open OMA.S_oeis_a121639

theorem rec639 (n : ℕ) :
    a (n + 4) = ((n : ℤ) + 4) * a (n + 3) + ((n + 3).factorial : ℤ) - ((n + 1).factorial : ℤ) := rfl

theorem fact639 (m k : ℕ) :
    ((m + (k + 1)).factorial : ℤ) = ((m : ℤ) + (k + 1)) * ((m + k).factorial : ℤ) := by
  have e : m + (k + 1) = (m + k) + 1 := by omega
  rw [e, Nat.factorial_succ]
  push_cast
  ring

theorem key639 (m : ℕ) :
    a (m + 7) + (-2 * ((m : ℤ) + 7) + 1) * a (m + 6)
      + ((m : ℤ) + 7) * (((m : ℤ) + 7) - 2) * a (m + 5)
      + (2 * ((m : ℤ) + 7) - 7) * a (m + 4)
      - ((((m : ℤ) + 7) - 3) * (((m : ℤ) + 7) - 5)) * a (m + 3) = 0 := by
  have h7 : a (m + 7) = ((m : ℤ) + 7) * a (m + 6) + ((m + 6).factorial : ℤ) - ((m + 4).factorial : ℤ) := by
    have e1 : m + 3 + 4 = m + 7 := by omega
    have e2 : m + 3 + 3 = m + 6 := by omega
    have e3 : m + 3 + 1 = m + 4 := by omega
    have e4 : m + 3 + 3 = m + 6 := by omega
    have c1 : ((m + 3 : ℕ) : ℤ) + 4 = (m : ℤ) + 7 := by omega
    simpa only [e1, e2, e3, e4, c1] using rec639 (m + 3)
  have h6 : a (m + 6) = ((m : ℤ) + 6) * a (m + 5) + ((m + 5).factorial : ℤ) - ((m + 3).factorial : ℤ) := by
    have e1 : m + 2 + 4 = m + 6 := by omega
    have e2 : m + 2 + 3 = m + 5 := by omega
    have e3 : m + 2 + 1 = m + 3 := by omega
    have c1 : ((m + 2 : ℕ) : ℤ) + 4 = (m : ℤ) + 6 := by omega
    simpa only [e1, e2, e3, c1] using rec639 (m + 2)
  have h5 : a (m + 5) = ((m : ℤ) + 5) * a (m + 4) + ((m + 4).factorial : ℤ) - ((m + 2).factorial : ℤ) := by
    have e1 : m + 1 + 4 = m + 5 := by omega
    have e2 : m + 1 + 3 = m + 4 := by omega
    have e3 : m + 1 + 1 = m + 2 := by omega
    have c1 : ((m + 1 : ℕ) : ℤ) + 4 = (m : ℤ) + 5 := by omega
    simpa only [e1, e2, e3, c1] using rec639 (m + 1)
  have h4 : a (m + 4) = ((m : ℤ) + 4) * a (m + 3) + ((m + 3).factorial : ℤ) - ((m + 1).factorial : ℤ) :=
    rec639 m
  have f6 : ((m + 6).factorial : ℤ) = ((m : ℤ) + 6) * ((m + 5).factorial : ℤ) := fact639 m 5
  have f5 : ((m + 5).factorial : ℤ) = ((m : ℤ) + 5) * ((m + 4).factorial : ℤ) := fact639 m 4
  have f4 : ((m + 4).factorial : ℤ) = ((m : ℤ) + 4) * ((m + 3).factorial : ℤ) := fact639 m 3
  have f3 : ((m + 3).factorial : ℤ) = ((m : ℤ) + 3) * ((m + 2).factorial : ℤ) := fact639 m 2
  have f2 : ((m + 2).factorial : ℤ) = ((m : ℤ) + 2) * ((m + 1).factorial : ℤ) := fact639 m 1
  rw [h7, h6, h5, h4]
  rw [f6, f5, f4, f3, f2]
  ring

end OMA

open OMA.S_oeis_a121639 in
theorem OMA.solution : type_of% @OMA.S_oeis_a121639.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 7 := ⟨n - 7, by omega⟩
  rw [show m + 7 - 1 = m + 6 by omega, show m + 7 - 2 = m + 5 by omega,
    show m + 7 - 3 = m + 4 by omega, show m + 7 - 4 = m + 3 by omega]
  push_cast
  exact OMA.key639 m
