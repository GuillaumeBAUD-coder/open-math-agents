import OMAStatements.S_oeis_a217471

lemma OMA.a217471_cassini (n : ℕ) :
    ((Nat.fib (n + 1) : ℚ)) ^ 2 - (Nat.fib (n + 1) : ℚ) * (Nat.fib n : ℚ)
      - (Nat.fib n : ℚ) ^ 2 = (-1) ^ n := by
  induction n with
  | zero => simp
  | succ m ih =>
    have h : (Nat.fib (m + 2) : ℚ) = Nat.fib m + Nat.fib (m + 1) := by
      rw [Nat.fib_add_two]; push_cast; ring
    rw [show m + 1 + 1 = m + 2 by ring, h, pow_succ]
    linear_combination (-1 : ℚ) * ih

theorem OMA.solution : type_of% @OMA.S_oeis_a217471.main := by
  intro n
  induction n with
  | zero => simp [OMA.S_oeis_a217471.a]
  | succ m ih =>
    have hsum : (OMA.S_oeis_a217471.a (m + 1) : ℚ) =
        OMA.S_oeis_a217471.a m + (Nat.fib (2 * m + 2) : ℚ) ^ 5 := by
      unfold OMA.S_oeis_a217471.a
      rw [Finset.sum_range_succ]
      push_cast
      ring_nf
    have hc := OMA.a217471_cassini (2 * m + 1)
    have hv : (Nat.fib (2 * (m + 1) + 1) : ℚ) = Nat.fib (2 * m + 1) + Nat.fib (2 * m + 2) := by
      rw [show 2 * (m + 1) + 1 = 2 * m + 1 + 2 by ring, Nat.fib_add_two]
      push_cast; ring
    rw [hsum, ih, hv]
    have hneg : ((-1 : ℚ)) ^ (2 * m + 1) = -1 := by
      rw [pow_succ, pow_mul]; norm_num
    rw [show 2 * m + 1 + 1 = 2 * m + 2 by ring, hneg] at hc
    set u : ℚ := (Nat.fib (2 * m + 1) : ℚ)
    set w : ℚ := (Nat.fib (2 * m + 2) : ℚ)
    linear_combination ((20 * u ^ 2 * w + 20 * u * w ^ 2 + 40 * w ^ 3 - 25 * w) / 44) * hc
