import OMAStatements.S_oeis_a378277
import Mathlib

/-!
With Cassini's identity F(j+1)^2 - F(j) F(j+2) = (-1)^j, induction gives
Sum_{k=1..j} (-1)^(k+1) / (F(k) F(k+2)) = F(j)^2 / (F(j+1) F(j+2)).
Adding the last entry (-1)^(j+2) / (F(j+1) F(j+2)) of row j+1 and using Cassini once more
gives F(j-1) / F(j+2) (and 1 / F(2) for j = 0).
-/

namespace R378277
open OMA.S_oeis_a378277 Nat

theorem cas (j : ℕ) : (fib (j + 1) : ℚ) ^ 2 - fib j * fib (j + 2) = (-1) ^ j := by
  induction j with
  | zero => simp [Nat.fib_two]
  | succ j ih =>
    have r1 : (fib (j + 2) : ℚ) = fib j + fib (j + 1) := by exact_mod_cast (Nat.fib_add_two (n := j))
    have r2 : (fib (j + 3) : ℚ) = fib (j + 1) + fib (j + 2) := by
      exact_mod_cast (Nat.fib_add_two (n := j + 1))
    show (fib (j + 2) : ℚ) ^ 2 - fib (j + 1) * fib (j + 3) = (-1) ^ (j + 1)
    rw [r2, r1]
    rw [r1] at ih
    linear_combination (-1 : ℚ) * ih

theorem G_eq (j : ℕ) : ∑ k ∈ Finset.Icc 1 j, (-1 : ℚ) ^ (k + 1) / ((fib k : ℚ) * (fib (k + 2) : ℚ)) =
    (fib j : ℚ) ^ 2 / ((fib (j + 1) : ℚ) * (fib (j + 2) : ℚ)) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    have r1 : (fib (j + 2) : ℚ) = fib j + fib (j + 1) := by exact_mod_cast (Nat.fib_add_two (n := j))
    have r2 : (fib (j + 3) : ℚ) = fib (j + 1) + fib (j + 2) := by
      exact_mod_cast (Nat.fib_add_two (n := j + 1))
    have hb : (0 : ℚ) < fib (j + 1) := by exact_mod_cast Nat.fib_pos.mpr (Nat.succ_pos j)
    have ha : (0 : ℚ) ≤ fib j := Nat.cast_nonneg _
    have c := cas j
    show (fib j : ℚ) ^ 2 / ((fib (j + 1) : ℚ) * fib (j + 2)) +
        (-1 : ℚ) ^ (j + 2) / ((fib (j + 1) : ℚ) * fib (j + 3)) =
        (fib (j + 1) : ℚ) ^ 2 / ((fib (j + 2) : ℚ) * fib (j + 3))
    rw [r2, r1]
    rw [r1] at c
    generalize (fib j : ℚ) = a at ha c ⊢
    generalize (fib (j + 1) : ℚ) = b at hb c ⊢
    have hB : b * (a + b) ≠ 0 := by
      have := mul_pos hb (show (0 : ℚ) < a + b by linarith)
      exact this.ne'
    have hD : b * (b + (a + b)) ≠ 0 := by
      have := mul_pos hb (show (0 : ℚ) < b + (a + b) by linarith)
      exact this.ne'
    have hF : (a + b) * (b + (a + b)) ≠ 0 := by
      have := mul_pos (show (0 : ℚ) < a + b by linarith) (show (0 : ℚ) < b + (a + b) by linarith)
      exact this.ne'
    rw [div_add_div _ _ hB hD, div_eq_div_iff (mul_ne_zero hB hD) hF]
    linear_combination (-(b * (a + b) ^ 2 * (a + 2 * b))) * c

theorem main' (j : ℕ) : ∑ k ∈ Finset.Icc 1 (j + 1), (-1 : ℚ) ^ (k + 1) / (T (j + 1) k : ℚ) =
    (fibSub2 (j + 1) : ℚ) / (fib (j + 1 + 1) : ℚ) := by
  rw [Finset.sum_Icc_succ_top (by omega)]
  have hsum : ∑ k ∈ Finset.Icc 1 j, (-1 : ℚ) ^ (k + 1) / (T (j + 1) k : ℚ) =
      ∑ k ∈ Finset.Icc 1 j, (-1 : ℚ) ^ (k + 1) / ((fib k : ℚ) * (fib (k + 2) : ℚ)) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_Icc] at hk
    unfold T
    rw [if_neg (by omega), Nat.cast_mul]
  have hT : (T (j + 1) (j + 1) : ℚ) = (fib (j + 1) : ℚ) * (fib (j + 2) : ℚ) := by
    unfold T
    rw [if_pos rfl]
    exact Nat.cast_mul _ _
  rw [hsum, hT, G_eq, ← add_div]
  rcases j with _ | i
  · norm_num [fibSub2, Nat.fib_two]
  · have c := cas i
    have h2 : (0 : ℚ) < fib (i + 2) := by exact_mod_cast Nat.fib_pos.mpr (by omega)
    have h3 : (0 : ℚ) < fib (i + 3) := by exact_mod_cast Nat.fib_pos.mpr (by omega)
    have hf : (fibSub2 (i + 1 + 1) : ℚ) = fib i := by
      unfold fibSub2
      rw [if_neg (by omega), show i + 1 + 1 - 2 = i by omega]
    rw [hf]
    show ((fib (i + 1) : ℚ) ^ 2 + (-1 : ℚ) ^ (i + 3)) / ((fib (i + 2) : ℚ) * fib (i + 3)) =
      (fib i : ℚ) / (fib (i + 3) : ℚ)
    rw [div_eq_div_iff (mul_pos h2 h3).ne' h3.ne']
    linear_combination (fib (i + 3) : ℚ) * c

end R378277

theorem OMA.solution : type_of% @OMA.S_oeis_a378277.main := by
  intro n hn
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
  exact R378277.main' j
