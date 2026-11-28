import OMAStatements.S_oeis_a203298
import Mathlib

open OMA.S_oeis_a203298 in
theorem OMA.solution : type_of% @OMA.S_oeis_a203298.main := by
  have p : ∀ i c, (2*i+c)/2 = i + c/2 := by omega
  have u (m : ℕ) : ((∑ i ∈ Finset.Ico 1 (m+1), t i : ℕ) : ℚ) =
      ((m+1)/2 : ℕ) * (m - ((m+1)/2 : ℕ)) + m := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_Ico_succ_top (by omega), Nat.cast_add, ih]
      obtain ⟨j, rfl | rfl⟩ := m.even_or_odd' <;> simp [t, add_assoc, p] <;> ring
  have v (n : ℕ) : ((a n : ℕ) : ℚ) = (6*n^4 + 40*n^3 + 48*n^2 - 112*n) / 192 +
      (n - 2*(n/2 : ℕ)) * (-12*n^2 - 24*n + 54) / 192 := by
    induction n with
    | zero => norm_num [a]
    | succ n ih =>
      rw [a, Finset.sum_Icc_succ_top (by omega), Nat.cast_add, ← a, ih, ← Finset.sum_mul, Nat.cast_mul, u]
      obtain ⟨j, rfl | rfl⟩ := n.even_or_odd' <;> simp [t, add_assoc, p] <;> ring
  refine ⟨?_, ?_, fun n hn => ?_⟩
  · rintro n - ⟨j, rfl⟩
    rw [v, show (j+j)/2 = j by omega]
    push_cast
    ring
  · rintro n - ⟨j, rfl⟩
    rw [v, show (2*j+1)/2 = j by omega]
    push_cast
    ring
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' (show 10 ≤ n from hn)
    qify
    obtain ⟨i, rfl | rfl⟩ := k.even_or_odd' <;> simp [v, add_assoc, p] <;> ring
