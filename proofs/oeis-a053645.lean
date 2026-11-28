import OMAStatements.S_oeis_a053645

/-! The distance resets at powers of two, and otherwise increases by one.
Original proof by @LAPRAI. -/

open OMA.S_oeis_a053645 in
theorem OMA.solution : type_of% @OMA.S_oeis_a053645.main := by
  refine ⟨by decide, fun n hn => ?_⟩
  let k := Nat.log 2 (n - 1)
  have hlo : 2 ^ k ≤ n - 1 := Nat.pow_log_le_self 2 (by omega)
  have hhi : n ≤ 2 ^ (k + 1) := by
    have : n - 1 < 2 ^ (k + 1) := Nat.lt_pow_succ_log_self (by decide) _
    omega
  unfold a a036987
  split
  · rename_i h
    obtain ⟨j, -, hj⟩ := h
    rw [show n = 2 ^ j by omega, Nat.log_pow (by decide)]
    simp
  · rename_i h
    have hlt : n < 2 ^ (k + 1) := by
      refine lt_of_le_of_ne hhi fun he => h ⟨k + 1, ?_, by omega⟩
      have := Nat.lt_two_pow_self (n := k + 1)
      omega
    rw [Nat.log_eq_of_pow_le_of_lt_pow (by omega) hlt]
    change n - 2 ^ k = (1 - 0) * (1 + (n - 1 - 2 ^ k))
    omega
