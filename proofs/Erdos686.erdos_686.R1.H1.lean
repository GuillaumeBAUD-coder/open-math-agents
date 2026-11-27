import OMAReductions.R_Erdos686_erdos_686_R1

-- Step Erdos686.erdos_686.R1.H1: hypothesis H1 of reduction Erdos686.erdos_686.R1
-- Credit: @mattdorman
-- Non-square N: take k = 2. With X = 2m + 3 and Y = 2n + 3 the equation
-- (m+1)(m+2) = N (n+1)(n+2) becomes X^2 - N Y^2 = 1 - N, solved by X = Y = 1. Multiplying by a
-- Pell unit a + b sqrt N with b even (the square of any nontrivial Pell solution) keeps X, Y odd
-- and positive and at least triples Y; three steps give Y >= 27, and then X >= Y + 4.

namespace OMA.E686H1

lemma step (N a b X Y : ℤ) (hN : 0 ≤ N) (hab : a ^ 2 - N * b ^ 2 = 1) (ha : 3 ≤ a)
    (hb : 0 ≤ b) (hbe : Even b) (hao : Odd a) (hXY : X ^ 2 - N * Y ^ 2 = 1 - N)
    (hX : 0 < X) (hY : 0 < Y) (hXo : Odd X) (hYo : Odd Y) :
    (a * X + N * b * Y) ^ 2 - N * (b * X + a * Y) ^ 2 = 1 - N ∧ 0 < a * X + N * b * Y ∧
      3 * Y ≤ b * X + a * Y ∧ Odd (a * X + N * b * Y) ∧ Odd (b * X + a * Y) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have : (a * X + N * b * Y) ^ 2 - N * (b * X + a * Y) ^ 2 =
        (a ^ 2 - N * b ^ 2) * (X ^ 2 - N * Y ^ 2) := by ring
    rw [this, hab, hXY, one_mul]
  · have h1 : 0 < a * X := by nlinarith
    have h2 : 0 ≤ N * b * Y := by positivity
    linarith
  · have h1 : 0 ≤ b * X := by positivity
    nlinarith
  · exact (hao.mul hXo).add_even ((hbe.mul_left N).mul_right Y)
  · exact (hbe.mul_right X).add_odd (hao.mul hYo)

end OMA.E686H1

theorem OMA.solution : OMA.R_Erdos686_erdos_686_R1.H1 := by
  intro N hN hNsq
  have hN0 : (0 : ℤ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN2 : (2 : ℤ) ≤ N := by exact_mod_cast hN
  have hsq : ¬ IsSquare (N : ℤ) := by rwa [Int.isSquare_natCast_iff]
  obtain ⟨u, v, huv, hv⟩ := Pell.exists_of_not_isSquare hN0 hsq
  have hv2 : 1 ≤ v ^ 2 := by
    rcases lt_or_gt_of_ne hv with h | h <;> nlinarith
  set a : ℤ := u ^ 2 + N * v ^ 2 with ha_def
  set b : ℤ := 2 * |u * v| with hb_def
  have hab : a ^ 2 - (N : ℤ) * b ^ 2 = 1 := by
    have hb2 : b ^ 2 = 4 * (u * v) ^ 2 := by
      rw [hb_def, mul_pow, sq_abs]; ring
    rw [hb2, ha_def]
    have : (u ^ 2 + N * v ^ 2) ^ 2 - N * (4 * (u * v) ^ 2) = (u ^ 2 - N * v ^ 2) ^ 2 := by ring
    rw [this, huv]; ring
  have ha3 : 3 ≤ a := by rw [ha_def]; nlinarith
  have hb0 : 0 ≤ b := by rw [hb_def]; positivity
  have hbe : Even b := ⟨|u * v|, by rw [hb_def]; ring⟩
  have hao : Odd a := ⟨N * v ^ 2, by rw [ha_def]; linarith⟩
  have hN0' : (0 : ℤ) ≤ N := hN0.le
  -- three multiplications starting from X = Y = 1
  obtain ⟨e1, p1, y1, o1, q1⟩ := OMA.E686H1.step N a b 1 1 hN0' hab ha3 hb0 hbe hao
    (by ring) one_pos one_pos odd_one odd_one
  obtain ⟨e2, p2, y2, o2, q2⟩ := OMA.E686H1.step N a b _ _ hN0' hab ha3 hb0 hbe hao
    e1 p1 (by linarith) o1 q1
  obtain ⟨e3, p3, y3, o3, q3⟩ := OMA.E686H1.step N a b _ _ hN0' hab ha3 hb0 hbe hao
    e2 p2 (by linarith) o2 q2
  obtain ⟨X, Y, hXY0, hXpos, hY27, hXo, hYo⟩ : ∃ X Y : ℤ, X ^ 2 - N * Y ^ 2 = 1 - N ∧ 0 < X ∧
      27 ≤ Y ∧ Odd X ∧ Odd Y := ⟨_, _, e3, p3, by linarith, o3, q3⟩
  clear e1 e2 e3 p1 p2 p3 y1 y2 y3 o1 o2 q1 q2
  have hXY : X ^ 2 = N * (Y ^ 2 - 1) + 1 := by linarith
  have hlow : 2 * (Y ^ 2 - 1) + 1 ≤ X ^ 2 := by
    have h1 : 2 * (Y ^ 2 - 1) ≤ N * (Y ^ 2 - 1) :=
      mul_le_mul_of_nonneg_right hN2 (by nlinarith)
    linarith
  have hXbig : Y + 4 ≤ X := by
    by_contra h
    have h' : X ≤ Y + 3 := by omega
    have hX2 : X ^ 2 ≤ (Y + 3) ^ 2 := by
      have := mul_le_mul h' h' hXpos.le (by linarith)
      nlinarith
    nlinarith
  obtain ⟨s, hs⟩ := hXo
  obtain ⟨t, ht⟩ := hYo
  have hs1 : 1 ≤ s := by linarith
  have ht1 : 1 ≤ t := by linarith
  refine ⟨2, le_refl _, (t - 1).toNat, (s - 1).toNat, ?_, ?_⟩
  · have hst : t + 2 ≤ s := by linarith
    omega
  · have hm : (((s - 1).toNat : ℕ) : ℤ) = s - 1 := Int.toNat_of_nonneg (by linarith)
    have hn : (((t - 1).toNat : ℕ) : ℤ) = t - 1 := Int.toNat_of_nonneg (by linarith)
    have hprod : ∀ r : ℕ, (∏ i ∈ Finset.Icc (1 : ℕ) 2, ((r : ℚ) + (i : ℚ))) =
        ((r : ℚ) + 1) * ((r : ℚ) + 2) := by
      intro r
      rw [show (Finset.Icc 1 2 : Finset ℕ) = {1, 2} by decide]
      simp
    have key : ((((s - 1).toNat : ℕ) : ℤ) + 1) * ((((s - 1).toNat : ℕ) : ℤ) + 2) =
        (N : ℤ) * (((((t - 1).toNat : ℕ) : ℤ) + 1) * ((((t - 1).toNat : ℕ) : ℤ) + 2)) := by
      rw [hm, hn]
      have hX' : X = 2 * s + 1 := hs
      have hY' : Y = 2 * t + 1 := ht
      rw [hX', hY'] at hXY
      nlinarith
    have keyq : (((s - 1).toNat : ℚ) + 1) * (((s - 1).toNat : ℚ) + 2) =
        (N : ℚ) * ((((t - 1).toNat : ℚ) + 1) * (((t - 1).toNat : ℚ) + 2)) := by
      exact_mod_cast key
    push_cast
    rw [hprod, hprod, eq_div_iff (by positivity), keyq]
