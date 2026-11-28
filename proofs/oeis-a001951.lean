import OMAStatements.S_oeis_a001951

-- Problem: A001951, the a(n)-th triangular number is within floor(a(n)/2) of a square.
-- Credit: @ShoQo
-- Proof: a(n) = m = isqrt(2 n^2), so m^2 <= 2 n^2 < (m+1)^2, and the square n^2 satisfies
-- |m(m+1)/2 - n^2| <= m/2.

open OMA.S_oeis_a001951 in
theorem OMA.solution : type_of% @OMA.S_oeis_a001951.main := by
  intro n
  have hb : a n = Nat.sqrt (2 * n ^ 2) := by
    unfold a
    rw [show (n : ℝ) * Real.sqrt 2 = Real.sqrt ((2 * n ^ 2 : ℕ) : ℝ) by
      push_cast
      rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (by positivity), mul_comm]]
    exact Real.nat_floor_real_sqrt_eq_nat_sqrt
  refine ⟨n, ?_⟩
  rw [hb]
  have hlo : Nat.sqrt (2 * n ^ 2) * Nat.sqrt (2 * n ^ 2) ≤ 2 * n ^ 2 := Nat.sqrt_le (2 * n ^ 2)
  have hhi : 2 * n ^ 2 < (Nat.sqrt (2 * n ^ 2) + 1) * (Nat.sqrt (2 * n ^ 2) + 1) :=
    Nat.lt_succ_sqrt (2 * n ^ 2)
  generalize Nat.sqrt (2 * n ^ 2) = m at hlo hhi ⊢
  obtain ⟨t, ht⟩ := (Nat.even_mul_succ_self m).two_dvd
  rw [ht, Nat.mul_div_cancel_left t (by norm_num), abs_le]
  have hm2 : (m / 2 : ℕ) * 2 + m % 2 = m := Nat.div_add_mod' m 2
  constructor <;> push_cast <;> nlinarith [Nat.mod_lt m (show 2 > 0 by norm_num)]

