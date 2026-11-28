import OMAStatements.S_oeis_a007051

-- Problem: A007051, s(1) = 2, s(n) = (2 s(n-1) + 1)/(s(n-1) + 2) gives s(n) = a(n)/(a(n) - 1).
-- Credit: @ShoQo
-- Proof: induction on n >= 1. With x = 3^n, a(n) = (x+1)/2 and a(n+1) = (3x+1)/2, so the claim
-- is s(n) = (x+1)/(x-1) and the recurrence maps (x+1)/(x-1) to (3x+1)/(3x-1).

open OMA.S_oeis_a007051 in
theorem OMA.solution : type_of% @OMA.S_oeis_a007051.main := by
  intro s h1 hrec n hn
  have ha : ∀ k : ℕ, (a k : ℚ) = (3 ^ k + 1) / 2 := by
    intro k
    have h2 : 2 ∣ 3 ^ k + 1 := by
      have : Odd (3 ^ k) := Odd.pow (by decide)
      exact (Nat.even_add_one.mpr (Nat.not_even_iff_odd.mpr this)).two_dvd
    unfold a; rw [Nat.cast_div h2 (by norm_num)]; push_cast; ring
  induction n, hn using Nat.le_induction with
  | base => rw [h1, ha]; norm_num
  | succ k hk ih =>
    rw [hrec (k + 1) (by omega), show k + 1 - 1 = k by omega, ih, ha, ha, pow_succ]
    have hx : (3 : ℚ) ^ k ≥ 3 := by
      calc (3 : ℚ) ^ k ≥ 3 ^ 1 := pow_le_pow_right₀ (by norm_num) hk
        _ = 3 := by norm_num
    generalize (3 : ℚ) ^ k = x at hx ⊢
    have key : (x + 1) / 2 / ((x + 1) / 2 - 1) = (x + 1) / (x - 1) := by
      rw [show (x + 1) / 2 - 1 = (x - 1) / 2 by ring, div_div_div_cancel_right₀ (by norm_num)]
    have key2 : (x * 3 + 1) / 2 / ((x * 3 + 1) / 2 - 1) = (3 * x + 1) / (3 * x - 1) := by
      rw [show (x * 3 + 1) / 2 - 1 = (3 * x - 1) / 2 by ring, div_div_div_cancel_right₀ (by norm_num)]
      ring
    rw [key, key2]
    have h1' : x - 1 ≠ 0 := by linarith
    have h2' : 3 * x - 1 ≠ 0 := by linarith
    have hA : (x + 1) / (x - 1) + 2 ≠ 0 := by
      have : (x + 1) / (x - 1) > 0 := div_pos (by linarith) (by linarith)
      linarith
    rw [div_eq_div_iff hA h2']
    field_simp
    ring

