import OMAStatements.S_oeis_a111403

open OMA.S_oeis_a111403

theorem OMA.solution : type_of% @OMA.S_oeis_a111403.main := by
  let b (n : ℕ) : ℤ := f (f n)
  have hb (n : ℕ) : b (n + 1) = b n ^ 2 := by
    dsimp [b, f]
    rw [pow_succ (2 : ℕ) n, pow_mul]
  have hform (n : ℕ) :
      A002716 (2 * n) = b n ^ 2 - b n + 1 ∧
      A002716 (2 * n + 1) = b n ^ 2 + 1 := by
    induction n with
    | zero => norm_num [A002716, b, f]
    | succ n ih =>
      have heven : A002716 (2 * (n + 1)) = b (n + 1) ^ 2 - b (n + 1) + 1 := by
        rw [show 2 * (n + 1) = 2 * n + 2 by omega, A002716,
          if_pos (by omega), ih.2, hb]
        ring
      refine ⟨heven, ?_⟩
      rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by omega, A002716,
        if_neg (by omega), show 2 * n + 1 + 1 = 2 * (n + 1) by omega,
        heven, ih.2, hb]
      ring
  intro n
  change b (n + 1) - b n = A002716 (2 * n) - 1
  rw [(hform n).1, hb]
  ring