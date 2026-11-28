import OMAStatements.S_oeis_a294139
import Mathlib

open OMA.S_oeis_a294139 in
theorem OMA.solution : type_of% @OMA.S_oeis_a294139.main := by
  have s (n m : ℕ) (hm : m ≤ n) : ((∑ i ∈ Finset.Icc 1 m, (2 * i ^ 2 + 2 * (n - i) ^ 2 + i * (n - i)) : ℕ) : ℚ) =
      m * (m + 1) * (2 * m + 1) / 2 - 3 * n * m * (m + 1) / 2 + 2 * n ^ 2 * m := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_Icc_succ_top (by omega), Nat.cast_add, ih (by omega)]
      push_cast [Nat.cast_sub hm]
      ring
  refine ⟨?_, ?_, fun n hn => ?_⟩
  · rintro n h ⟨j, rfl⟩
    obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le' (show 1 ≤ j by omega)
    rw [a, show (i+1+(i+1)-1)/2 = i by omega, s (i+1+(i+1)) i (by omega)]
    push_cast
    ring
  · rintro n ⟨j, rfl⟩
    rw [a, show (2*j+1-1)/2 = j by omega, s (2*j+1) j (by omega)]
    push_cast
    ring
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' (show 8 ≤ n from hn)
    have g : ∀ x, (x+2)/2 = x/2+1 := by omega
    qify
    simp (disch := omega) only [a, s, g, Nat.reduceSubDiff]
    push_cast
    ring
