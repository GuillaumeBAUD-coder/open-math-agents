import OMAStatements.S_oeis_a307686

namespace OMA.P307686

open PowerSeries OMA.S_oeis_a307686

/-- Closed form of the inner count. -/
def cc (n k : ℕ) : ℕ := (n - k) / 2 + 1 - max k ((n - 2 * k) / 2 + 1)

lemma filt (n k : ℕ) (hk : 1 ≤ k) :
    (Finset.Icc k ((n - k) / 2)).filter (fun i => n - i - k < i + k)
      = Finset.Icc (max k ((n - 2 * k) / 2 + 1)) ((n - k) / 2) := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_Icc, max_le_iff]
  omega

lemma a_eq (n : ℕ) : a n = ∑ k ∈ Finset.Icc 1 (n / 3), k * cc n k := by
  unfold a
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_Icc] at hk
  rw [Finset.sum_const, filt n k hk.1, Nat.card_Icc, smul_eq_mul, mul_comm]
  rfl

lemma cc_step (n k : ℕ) (hk : 1 ≤ k) (hk2 : 3 * k ≤ n + 2) :
    cc (n + 2) k = cc n k + if n + 2 < 4 * k then 1 else 0 := by
  unfold cc
  rw [max_def, max_def]
  split_ifs <;> omega

lemma cc_zero (n : ℕ) : cc n (n / 3 + 1) = 0 := by
  unfold cc
  rw [max_def]
  split_ifs <;> omega

lemma a_ext (n : ℕ) : a n = ∑ k ∈ Finset.Icc 1 ((n + 2) / 3), k * cc n k := by
  rw [a_eq]
  rcases (by omega : (n + 2) / 3 = n / 3 ∨ (n + 2) / 3 = n / 3 + 1) with h | h
  · rw [h]
  · rw [h, Finset.sum_Icc_succ_top (by omega), cc_zero]
    simp

lemma tail_sum (J d : ℕ) :
    2 * (∑ k ∈ Finset.Icc 1 (J + d), if J < k then k else 0) + J * (J + 1)
      = (J + d) * (J + d + 1) := by
  induction d with
  | zero =>
    have h0 : ∑ k ∈ Finset.Icc 1 (J + 0), (if J < k then k else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      rw [Finset.mem_Icc] at hk
      rw [if_neg (by omega)]
    rw [h0]
    ring
  | succ d ih =>
    have e : J + (d + 1) = (J + d) + 1 := by ring
    rw [e, Finset.sum_Icc_succ_top (by omega), if_pos (by omega)]
    nlinarith [ih]

/-- The key step: `a (n + 2) - a n` is a difference of two triangular numbers. -/
lemma core (n : ℕ) :
    2 * a (n + 2) + ((n + 2) / 4) * ((n + 2) / 4 + 1)
      = 2 * a n + ((n + 2) / 3) * ((n + 2) / 3 + 1) := by
  have h1 : a (n + 2) = ∑ k ∈ Finset.Icc 1 ((n + 2) / 3), k * cc (n + 2) k := a_eq (n + 2)
  have h2 := a_ext n
  have h3 : ∑ k ∈ Finset.Icc 1 ((n + 2) / 3), k * cc (n + 2) k
      = ∑ k ∈ Finset.Icc 1 ((n + 2) / 3), k * cc n k
        + ∑ k ∈ Finset.Icc 1 ((n + 2) / 3), (if (n + 2) / 4 < k then k else 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_Icc] at hk
    rw [cc_step n k hk.1 (by omega)]
    by_cases h : n + 2 < 4 * k
    · rw [if_pos h, if_pos (by omega)]
      ring
    · rw [if_neg h, if_neg (by omega)]
      ring
  obtain ⟨d, hd⟩ : ∃ d, (n + 2) / 3 = (n + 2) / 4 + d :=
    ⟨(n + 2) / 3 - (n + 2) / 4, by omega⟩
  have h4 := tail_sum ((n + 2) / 4) d
  rw [← hd] at h4
  rw [h1, h3, ← h2]
  linarith

lemma a_zero : a 0 = 0 := by rw [a_eq]; rfl

lemma a_one : a 1 = 0 := by rw [a_eq]; rfl

/-- Triangular numbers over the rationals. -/
def t (x : ℕ) : ℚ := (x : ℚ) * ((x : ℚ) + 1) / 2

lemma shift (f : ℕ → ℚ) (d : ℕ) :
    PowerSeries.mk f * (1 - X ^ d)
      = PowerSeries.mk (fun n => f n - if d ≤ n then f (n - d) else 0) := by
  ext n
  rw [mul_sub, mul_one, map_sub, coeff_mul_X_pow']
  simp

lemma Ed (d : ℕ) (hd : 0 < d) :
    PowerSeries.mk (fun n => t (n / d)) * ((1 - X) * (1 - X ^ d) ^ 2) = (X : ℚ⟦X⟧) ^ d := by
  have s1 : PowerSeries.mk (fun n => t (n / d)) * (1 - X ^ d)
      = PowerSeries.mk (fun n => ((n / d : ℕ) : ℚ)) := by
    rw [shift]
    congr 1
    funext n
    split_ifs with h
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + d := ⟨n - d, by omega⟩
      rw [Nat.add_sub_cancel, Nat.add_div_right m hd]
      unfold t
      push_cast
      ring
    · rw [Nat.div_eq_of_lt (by omega)]
      simp [t]
  have s2 : PowerSeries.mk (fun n => ((n / d : ℕ) : ℚ)) * (1 - X ^ d)
      = PowerSeries.mk (fun n => if d ≤ n then (1 : ℚ) else 0) := by
    rw [shift]
    congr 1
    funext n
    split_ifs with h
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + d := ⟨n - d, by omega⟩
      rw [Nat.add_sub_cancel, Nat.add_div_right m hd]
      push_cast
      ring
    · rw [Nat.div_eq_of_lt (by omega)]
      simp
  have s3 : PowerSeries.mk (fun n => if d ≤ n then (1 : ℚ) else 0) * (1 - X)
      = (X : ℚ⟦X⟧) ^ d := by
    have h := shift (fun n => if d ≤ n then (1 : ℚ) else 0) 1
    rw [pow_one] at h
    rw [h]
    ext n
    rw [coeff_mk, coeff_X_pow]
    split_ifs <;> first | (exfalso; omega) | norm_num
  calc PowerSeries.mk (fun n => t (n / d)) * ((1 - X) * (1 - X ^ d) ^ 2)
      = ((PowerSeries.mk (fun n => t (n / d)) * (1 - X ^ d)) * (1 - X ^ d)) * (1 - X) := by ring
    _ = (X : ℚ⟦X⟧) ^ d := by rw [s1, s2, s3]

lemma diff2 : PowerSeries.mk (fun n => (a n : ℚ)) * (1 - X ^ 2)
    = PowerSeries.mk (fun n => t (n / 3)) - PowerSeries.mk (fun n => t (n / 4)) := by
  rw [shift]
  ext n
  rw [map_sub, coeff_mk, coeff_mk, coeff_mk]
  split_ifs with h
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    rw [Nat.add_sub_cancel]
    have hc := core m
    obtain ⟨p, hp⟩ : ∃ p, (m + 2) / 3 = p := ⟨_, rfl⟩
    obtain ⟨q, hq⟩ : ∃ q, (m + 2) / 4 = q := ⟨_, rfl⟩
    rw [hp, hq] at hc
    rw [hp, hq]
    have hcq : (2 * (a (m + 2) : ℚ) + (q : ℚ) * ((q : ℚ) + 1))
        = 2 * (a m : ℚ) + (p : ℚ) * ((p : ℚ) + 1) := by exact_mod_cast hc
    unfold t
    linarith
  · have h01 : n = 0 ∨ n = 1 := by omega
    rcases h01 with rfl | rfl
    · simp [t, a_zero]
    · simp [t, a_one]

lemma gf : PowerSeries.mk (fun n => (a n : ℚ)) *
      ((1 - X) ^ 4 * (1 + X) ^ 3 * (1 + X ^ 2) ^ 2 * (1 + X + X ^ 2) ^ 2) =
    X ^ 3 * (1 + X + X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6) := by
  have hA := diff2
  have h3 := Ed 3 (by norm_num)
  have h4 := Ed 4 (by norm_num)
  linear_combination ((1 - X) ^ 3 * (1 + X) ^ 2 * (1 + X ^ 2) ^ 2 * (1 + X + X ^ 2) ^ 2) * hA
    + ((1 + X) ^ 2 * (1 + X ^ 2) ^ 2) * h3 - ((1 + X + X ^ 2) ^ 2) * h4

lemma cshift (A : ℚ⟦X⟧) (j c m : ℕ) (h : c + j = 16) :
    coeff (m + 16) (A * X ^ j) = coeff (m + c) A := by
  have e : m + 16 = (m + c) + j := by omega
  rw [e, coeff_mul_X_pow]

lemma cX (k m : ℕ) (h : k < 16) : coeff (m + 16) ((X : ℚ⟦X⟧) ^ k) = 0 := by
  rw [coeff_X_pow, if_neg (by omega)]

lemma recQ (m : ℕ) :
    (a (m + 16) : ℚ) + (a (m + 15) : ℚ) - 2 * (a (m + 13) : ℚ) - 4 * (a (m + 12) : ℚ) - 2 * (a (m + 11) : ℚ) + (a (m + 10) : ℚ) + 5 * (a (m + 9) : ℚ) + 5 * (a (m + 8) : ℚ) + (a (m + 7) : ℚ) - 2 * (a (m + 6) : ℚ) - 4 * (a (m + 5) : ℚ) - 2 * (a (m + 4) : ℚ) + (a (m + 2) : ℚ) + (a (m + 1) : ℚ) = 0 := by
  obtain ⟨A, hAdef⟩ : ∃ A : ℚ⟦X⟧, A = PowerSeries.mk (fun n => (a n : ℚ)) := ⟨_, rfl⟩
  have h := gf
  rw [← hAdef] at h
  have h2 : A + A * X ^ 1 - (A * X ^ 3 + A * X ^ 3) - (A * X ^ 4 + A * X ^ 4 + A * X ^ 4 + A * X ^ 4) - (A * X ^ 5 + A * X ^ 5) + A * X ^ 6 + (A * X ^ 7 + A * X ^ 7 + A * X ^ 7 + A * X ^ 7 + A * X ^ 7) + (A * X ^ 8 + A * X ^ 8 + A * X ^ 8 + A * X ^ 8 + A * X ^ 8) + A * X ^ 9 - (A * X ^ 10 + A * X ^ 10) - (A * X ^ 11 + A * X ^ 11 + A * X ^ 11 + A * X ^ 11) - (A * X ^ 12 + A * X ^ 12) + A * X ^ 14 + A * X ^ 15
      = X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 7 + X ^ 8 + X ^ 9 := by
    linear_combination h
  have hc := congrArg (coeff (m + 16)) h2
  simp only [map_add, map_sub] at hc
  rw [cshift A 1 15 m rfl, cshift A 3 13 m rfl, cshift A 4 12 m rfl, cshift A 5 11 m rfl, cshift A 6 10 m rfl, cshift A 7 9 m rfl, cshift A 8 8 m rfl, cshift A 9 7 m rfl, cshift A 10 6 m rfl, cshift A 11 5 m rfl, cshift A 12 4 m rfl, cshift A 14 2 m rfl, cshift A 15 1 m rfl,
    cX 3 m (by norm_num), cX 4 m (by norm_num), cX 5 m (by norm_num), cX 6 m (by norm_num), cX 7 m (by norm_num), cX 8 m (by norm_num), cX 9 m (by norm_num)] at hc
  rw [hAdef] at hc
  simp only [coeff_mk] at hc
  linarith

end OMA.P307686

open PowerSeries OMA.S_oeis_a307686 OMA.P307686 in
theorem OMA.solution : type_of% @OMA.S_oeis_a307686.main := by
  refine ⟨gf, ?_⟩
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 16 := ⟨n - 16, by omega⟩
  simp only [show m + 16 - 1 = m + 15 by omega, show m + 16 - 3 = m + 13 by omega, show m + 16 - 4 = m + 12 by omega, show m + 16 - 5 = m + 11 by omega, show m + 16 - 6 = m + 10 by omega, show m + 16 - 7 = m + 9 by omega, show m + 16 - 8 = m + 8 by omega, show m + 16 - 9 = m + 7 by omega, show m + 16 - 10 = m + 6 by omega, show m + 16 - 11 = m + 5 by omega, show m + 16 - 12 = m + 4 by omega, show m + 16 - 14 = m + 2 by omega, show m + 16 - 15 = m + 1 by omega]
  have hR := recQ m
  have hz : (((a (m + 16) : ℤ) + (a (m + 15) : ℤ) - 2 * (a (m + 13) : ℤ) - 4 * (a (m + 12) : ℤ) - 2 * (a (m + 11) : ℤ) + (a (m + 10) : ℤ) + 5 * (a (m + 9) : ℤ) + 5 * (a (m + 8) : ℤ) + (a (m + 7) : ℤ) - 2 * (a (m + 6) : ℤ) - 4 * (a (m + 5) : ℤ) - 2 * (a (m + 4) : ℤ) + (a (m + 2) : ℤ) + (a (m + 1) : ℤ) : ℤ) : ℚ) = 0 := by
    push_cast
    linarith
  have hz2 := Int.cast_eq_zero.mp hz
  linarith
