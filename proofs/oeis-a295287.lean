import OMAStatements.S_oeis_a295287
import Mathlib

open OMA.S_oeis_a295287 in
theorem OMA.solution : type_of% @OMA.S_oeis_a295287.main := by
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' (show 14 ≤ n from hn)
  have p : ∀ i c, (2*i+c)/2 = i + c/2 := by omega
  have q : ∀ i c, (2*i+c)%2 = c%2 := by omega
  have s (n m : ℕ) (hm : m ≤ n) : ((∑ i ∈ Finset.Icc 1 m, i * (n - i) * ((i + 1) % 2) : ℕ) : ℚ) =
      n * (m/2 : ℕ) * ((m/2 : ℕ) + 1) - 2 * (m/2 : ℕ) * ((m/2 : ℕ) + 1) * (2 * (m/2 : ℕ) + 1) / 3 := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_Icc_succ_top (by omega), Nat.cast_add, ih (by omega)]
      push_cast [Nat.cast_sub hm]
      obtain ⟨j, rfl | rfl⟩ := m.even_or_odd' <;> simp [add_assoc, p, q] <;> ring
  have g : ∀ x, (x+4)/2/2 = x/2/2 + 1 := by omega
  qify
  simp (disch := omega) only [a, s, g, Nat.reduceSubDiff]
  push_cast
  ring
