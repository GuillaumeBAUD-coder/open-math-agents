import OMAStatements.S_oeis_a400216

-- Problem: A400216: Scaled x-coordinates of the vertices of a Boerdijk-Coxeter helix starting at a tetrahedron with vertices (-1,-1,-1), (1, -1, 1), (-1, 1, 1), and (1, 1, -1).
-- Upstream: formal-conjectures statements/oeis-a400216.lean:0 (declaration OMA.S_oeis_a400216.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: the x-coordinates x(n) satisfy x(n+4) = (2/3)(x(n+1) + x(n+2) + x(n+3)) - x(n), and
-- a(i+3) = 3^i x(i+3) for all i (also for i = 0, where the scale is 1 = 3^0). Multiplying the
-- recurrence by 3^(i+4) gives a(i+7) = 2a(i+6) + 6a(i+5) + 18a(i+4) - 81a(i+3), whose
-- characteristic polynomial reversed is (3x - 1)^2 (9x^2 + 4x + 1) = 1 - 2x - 6x^2 - 18x^3 + 81x^4.
-- So the coefficients of x^m, m >= 7, of the product vanish, and those for m <= 6 come from
-- a(0..6) = -1, -1, 1, 1, 5, 31, 83.

open OMA.S_oeis_a400216 in
theorem OMA.solution : type_of% @OMA.S_oeis_a400216.main := by
  have hx : ∀ j, V (j + 4) 0 = 2 / 3 * (V (j + 1) 0 + V (j + 2) 0 + V (j + 3) 0) - V j 0 :=
    fun j => rfl
  have ha3 : ∀ i, a (i + 3) = 3 ^ i * V (i + 3) 0 := by
    intro i
    unfold a
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    · subst h0
      norm_num
    · rw [if_neg (show ¬ (i + 3 ≤ 3) by omega), show i + 3 - 3 = i by omega]
  have hr : ∀ i, a (i + 7) = 2 * a (i + 6) + 6 * a (i + 5) + 18 * a (i + 4) - 81 * a (i + 3) := by
    intro i
    have e : V (i + 7) 0 = 2 / 3 * (V (i + 4) 0 + V (i + 5) 0 + V (i + 6) 0) - V (i + 3) 0 :=
      hx (i + 3)
    have h7 : a (i + 7) = 3 ^ (i + 4) * V (i + 7) 0 := ha3 (i + 4)
    have h6 : a (i + 6) = 3 ^ (i + 3) * V (i + 6) 0 := ha3 (i + 3)
    have h5 : a (i + 5) = 3 ^ (i + 2) * V (i + 5) 0 := ha3 (i + 2)
    have h4 : a (i + 4) = 3 ^ (i + 1) * V (i + 4) 0 := ha3 (i + 1)
    have h3 : a (i + 3) = 3 ^ i * V (i + 3) 0 := ha3 i
    rw [h7, h6, h5, h4, h3, e]
    ring
  have hq : ∀ m, 7 ≤ m →
      a m = 2 * a (m - 1) + 6 * a (m - 2) + 18 * a (m - 3) - 81 * a (m - 4) := by
    intro m hm
    obtain ⟨i, rfl⟩ : ∃ i, m = i + 7 := ⟨m - 7, by omega⟩
    rw [show i + 7 - 1 = i + 6 by omega, show i + 7 - 2 = i + 5 by omega,
      show i + 7 - 3 = i + 4 by omega, show i + 7 - 4 = i + 3 by omega]
    exact hr i
  have x0 : V 0 0 = -1 := rfl
  have x1 : V 1 0 = -1 := rfl
  have x2 : V 2 0 = 1 := rfl
  have x3 : V 3 0 = 1 := rfl
  have e4 : V 4 0 = 2 / 3 * (V 1 0 + V 2 0 + V 3 0) - V 0 0 := hx 0
  have e5 : V 5 0 = 2 / 3 * (V 2 0 + V 3 0 + V 4 0) - V 1 0 := hx 1
  have e6 : V 6 0 = 2 / 3 * (V 3 0 + V 4 0 + V 5 0) - V 2 0 := hx 2
  have x4 : V 4 0 = 5 / 3 := by
    rw [e4, x0, x1, x2, x3]
    norm_num
  have x5 : V 5 0 = 31 / 9 := by
    rw [e5, x1, x2, x3, x4]
    norm_num
  have x6 : V 6 0 = 83 / 27 := by
    rw [e6, x2, x3, x4, x5]
    norm_num
  have q0 : a 0 = -1 := by
    unfold a
    rw [if_pos (show (0 : ℕ) ≤ 3 by omega), x0]
    norm_num
  have q1 : a 1 = -1 := by
    unfold a
    rw [if_pos (show (1 : ℕ) ≤ 3 by omega), x1]
    norm_num
  have q2 : a 2 = 1 := by
    unfold a
    rw [if_pos (show (2 : ℕ) ≤ 3 by omega), x2]
    norm_num
  have q3 : a 3 = 1 := by
    unfold a
    rw [if_pos (show (3 : ℕ) ≤ 3 by omega), x3]
    norm_num
  have q4 : a 4 = 5 := by
    have h : a 4 = 3 ^ 1 * V 4 0 := ha3 1
    rw [h, x4]
    norm_num
  have q5 : a 5 = 31 := by
    have h : a 5 = 3 ^ 2 * V 5 0 := ha3 2
    rw [h, x5]
    norm_num
  have q6 : a 6 = 83 := by
    have h : a 6 = 3 ^ 3 * V 6 0 := ha3 3
    rw [h, x6]
    norm_num
  have e : PowerSeries.mk a *
      ((3 * PowerSeries.X - 1) ^ 2 * (9 * PowerSeries.X ^ 2 + 4 * PowerSeries.X + 1)) =
      (PowerSeries.C : ℚ →+* PowerSeries ℚ) 81 * (PowerSeries.mk a * PowerSeries.X ^ 4)
        - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 18 * (PowerSeries.mk a * PowerSeries.X ^ 3)
        - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 6 * (PowerSeries.mk a * PowerSeries.X ^ 2)
        - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2 * (PowerSeries.mk a * PowerSeries.X ^ 1)
        + PowerSeries.mk a := by
    rw [map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 81,
      map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 18,
      map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 6,
      map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2]
    ring
  have e2 : (54 * PowerSeries.X ^ 6 - 84 * PowerSeries.X ^ 5 - 66 * PowerSeries.X ^ 4 +
      23 * PowerSeries.X ^ 3 + 9 * PowerSeries.X ^ 2 + PowerSeries.X - 1 : PowerSeries ℚ) =
      PowerSeries.X ^ 6 * (PowerSeries.C : ℚ →+* PowerSeries ℚ) 54
        - PowerSeries.X ^ 5 * (PowerSeries.C : ℚ →+* PowerSeries ℚ) 84
        - PowerSeries.X ^ 4 * (PowerSeries.C : ℚ →+* PowerSeries ℚ) 66
        + PowerSeries.X ^ 3 * (PowerSeries.C : ℚ →+* PowerSeries ℚ) 23
        + PowerSeries.X ^ 2 * (PowerSeries.C : ℚ →+* PowerSeries ℚ) 9
        + PowerSeries.X ^ 1 - 1 := by
    rw [map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 54,
      map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 84,
      map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 66,
      map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 23,
      map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 9]
    ring
  rw [e, e2]
  ext m
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow',
    PowerSeries.coeff_mk, PowerSeries.coeff_X_pow, PowerSeries.coeff_one, PowerSeries.coeff_mul_C]
  rcases Nat.lt_or_ge m 7 with hm | hm
  · interval_cases m
    · norm_num [q0]
    · norm_num [q0, q1]
    · norm_num [q0, q1, q2]
    · norm_num [q0, q1, q2, q3]
    · norm_num [q0, q1, q2, q3, q4]
    · norm_num [q1, q2, q3, q4, q5]
    · norm_num [q2, q3, q4, q5, q6]
  · simp (disch := omega) only [if_pos, if_neg]
    linarith [hq m hm]
