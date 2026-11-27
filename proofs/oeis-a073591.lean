import OMAStatements.S_oeis_a073591

/-!
R. J. Mathar conjectured the four-term recurrence for OEIS A073591 in 2014.
The proof derives the first-order recurrence recorded by Georg Fischer from
R. C. Walker's 1976 paper, then eliminates three successive first differences.
Alois P. Heinz gave a recursive implementation. Source: https://oeis.org/A073591
Statement by @OrangeHeadz. Formal proof by @ptlom with OpenAI Codex (gpt-6.2-astra).
-/

open OMA.S_oeis_a073591

private theorem arrangements_succ (n : ℕ) : A000522 (n+1) = (n+1)*A000522 n + 1 := by
  unfold A000522
  rw [Finset.sum_range_succ, Nat.div_self (Nat.factorial_pos _), Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [Nat.factorial_succ, Nat.mul_div_assoc _ (Nat.factorial_dvd_factorial (by
    have := Finset.mem_range.mp hk
    omega))]

private theorem walker (n : ℕ) : a (n+1) = (n+1 : ℤ)*(a n - 1) + 2 := by
  simp only [a, arrangements_succ, Nat.cast_add, Nat.cast_one, Nat.cast_mul]
  ring

theorem OMA.solution : type_of% @OMA.S_oeis_a073591.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k + 3 := ⟨n-3, by omega⟩
  simp only [show k + 3 - 1 = k + 2 by omega, show k + 3 - 2 = k + 1 by omega,
    show k + 3 - 3 = k by omega, Nat.cast_add, Nat.cast_ofNat]
  have first := walker (k+2)
  have second := walker (k+1)
  simp only [Nat.cast_add, Nat.cast_ofNat, Nat.cast_one] at first second
  linear_combination first - 2 * second + walker k
