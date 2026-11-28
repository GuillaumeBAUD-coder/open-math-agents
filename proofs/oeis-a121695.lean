import OMAStatements.S_oeis_a121695
import Mathlib

namespace OMA.S_oeis_a121695

lemma a_succ (n : ℕ) : a (n + 3) = a (n + 1) + ((n : ℤ) + 3) * ((n + 1).factorial : ℤ) * (((n + 2) / 2 : ℕ) : ℤ) := by
  rw [a]

lemma pair (m : ℕ) : a (m + 1) + a (m + 2) = ((m + 1).factorial : ℤ) * (((m + 3) / 2 : ℕ) : ℤ) := by
  induction m with
  | zero => simp [a]
  | succ m ih =>
    have e := a_succ m
    rw [show m + 1 + 1 = m + 2 from rfl, show m + 1 + 2 = m + 3 from rfl, e]
    have : a (m + 1) + a (m + 1 + 1) = _ := ih
    rw [show m + 1 + 3 = m + 4 from rfl, Nat.factorial_succ (m + 1)]
    rcases Nat.even_or_odd' m with ⟨k, rfl | rfl⟩
    · have h1 : (2 * k + 3) / 2 = k + 1 := by omega
      have h2 : (2 * k + 2) / 2 = k + 1 := by omega
      have h3 : (2 * k + 4) / 2 = k + 2 := by omega
      rw [h1] at ih
      rw [h2, h3]
      push_cast at ih ⊢
      linear_combination ih
    · have h1 : (2 * k + 1 + 3) / 2 = k + 2 := by omega
      have h2 : (2 * k + 1 + 2) / 2 = k + 1 := by omega
      have h3 : (2 * k + 1 + 4) / 2 = k + 2 := by omega
      rw [h1] at ih
      rw [h2, h3]
      push_cast at ih ⊢
      linear_combination ih

lemma main_id (j : ℕ) :
    b (j + 5) + b (j + 4) - ((j + 5 : ℕ) : ℤ) * (((j + 5 : ℕ) : ℤ) - 2) * b (j + 3) -
      (2 * ((j + 5 : ℕ) : ℤ) - 3) * (((j + 5 : ℕ) : ℤ) - 2) * b (j + 2) -
      (((j + 5 : ℕ) : ℤ) - 2) * (((j + 5 : ℕ) : ℤ) - 3) * b (j + 1) = 0 := by
  have e5 := a_succ (j + 2)
  have e4 := a_succ (j + 1)
  have e3 := a_succ j
  have pr := pair j
  simp only [b]
  rw [show j + 2 + 3 = j + 5 from rfl, show j + 2 + 1 = j + 3 from rfl] at e5
  rw [show j + 1 + 3 = j + 4 from rfl, show j + 1 + 1 = j + 2 from rfl] at e4
  simp only [Nat.factorial_succ] at e5 e4 e3 pr ⊢
  push_cast at e5 e4 e3 pr ⊢
  rcases Nat.even_or_odd' j with ⟨k, rfl | rfl⟩
  · have h1 : ((2 * (k : ℤ) + 2 + 2) / 2) = k + 2 := by omega
    have h2 : ((2 * (k : ℤ) + 1 + 2) / 2) = k + 1 := by omega
    have h3 : ((2 * (k : ℤ) + 2) / 2) = k + 1 := by omega
    have h4 : ((2 * (k : ℤ) + 3) / 2) = k + 1 := by omega
    push_cast at e5 e4 e3 pr ⊢
    rw [h1] at e5
    rw [h2] at e4
    rw [h3] at e3
    rw [h4] at pr
    linear_combination (-1 : ℤ) * e5 + (-1 : ℤ) * e4 + (((2 * k : ℤ) + 5) * ((2 * k : ℤ) + 3) - 1) * e3 + (((2 * (2 * k : ℤ) + 5)) * ((2 * k : ℤ) + 4) - 0) * pr
  · have h1 : ((2 * (k : ℤ) + 1 + 2 + 2) / 2) = k + 2 := by omega
    have h2 : ((2 * (k : ℤ) + 1 + 1 + 2) / 2) = k + 2 := by omega
    have h3 : ((2 * (k : ℤ) + 1 + 2) / 2) = k + 1 := by omega
    have h4 : ((2 * (k : ℤ) + 1 + 3) / 2) = k + 2 := by omega
    push_cast at e5 e4 e3 pr ⊢
    rw [h1] at e5
    rw [h2] at e4
    rw [h3] at e3
    rw [h4] at pr
    linear_combination (-1 : ℤ) * e5 + (-1 : ℤ) * e4 + (((2 * k : ℤ) + 6) * ((2 * k : ℤ) + 4) - 1) * e3 + (((2 * (2 * k + 1 : ℤ) + 5)) * ((2 * k : ℤ) + 5) - 0) * pr

end OMA.S_oeis_a121695

theorem OMA.solution : type_of% @OMA.S_oeis_a121695.main := by
  intro n hn
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 5 := ⟨n - 5, by omega⟩
  have := OMA.S_oeis_a121695.main_id j
  simpa using this
