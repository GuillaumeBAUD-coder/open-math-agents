import OMAStatements.S_oeis_a296161
import Mathlib

open OMA.S_oeis_a296161 in
theorem OMA.solution : type_of% @OMA.S_oeis_a296161.main := by
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' (show 10 ≤ n from hn)
  have p : ∀ i c, (2*i+c)/2 = i + c/2 := by omega
  have s (n m : ℕ) (hm : m ≤ n) : ((∑ i ∈ Finset.Icc 1 m, (n - i) * (i % 2) : ℕ) : ℤ) =
      ((m+1)/2 : ℕ) * (n - ((m+1)/2 : ℕ)) := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_Icc_succ_top (by omega), Nat.cast_add, ih (by omega)]
      obtain ⟨j, rfl | rfl⟩ := m.even_or_odd' <;> simp [add_assoc, p, Nat.cast_sub hm, Nat.add_mod] <;> ring
  have g : ∀ x, ((x+4)/2+1)/2 = (x/2+1)/2 + 1 := by omega
  simp only [a, s _ _ (Nat.div_le_self _ 2), g, Nat.reduceSubDiff]
  push_cast
  ring
