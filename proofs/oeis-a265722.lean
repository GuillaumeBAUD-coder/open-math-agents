import OMAStatements.S_oeis_a265722

-- Complete proof of OEIS A265722 (Rule 1 elementary cellular automaton)
-- Author: Paul Roulleau (@Solfanbtc) via Antigravity NEON-SWARM FACTORY v3

open OMA.S_oeis_a265722 PowerSeries

private lemma ruleOut_one (l c r : Bool) :
    ruleOut 1 l c r = (!l && !c && !r) := by
  cases l <;> cases c <;> cases r <;> decide

private lemma cell_one_one (i : ℤ) :
    cell 1 1 i = decide (i ≤ -2 ∨ 2 ≤ i) := by
  change ruleOut 1 (decide (i - 1 = 0)) (decide (i = 0)) (decide (i + 1 = 0)) =
    decide (i ≤ -2 ∨ 2 ≤ i)
  rw [ruleOut_one]
  by_cases h1 : i - 1 = 0
  · have : i = 1 := by omega
    subst this; decide
  · by_cases h2 : i = 0
    · subst h2; decide
    · by_cases h3 : i + 1 = 0
      · have : i = -1 := by omega
        subst this; decide
      · have h4 : i ≤ -2 ∨ 2 ≤ i := by omega
        simp [h1, h2, h3, h4]

private lemma cell_one_two (i : ℤ) :
    cell 1 2 i = decide (i = 0) := by
  change ruleOut 1 (cell 1 1 (i - 1)) (cell 1 1 i) (cell 1 1 (i + 1)) = decide (i = 0)
  rw [cell_one_one, cell_one_one, cell_one_one, ruleOut_one]
  by_cases h0 : i = 0
  · subst h0; decide
  · by_cases hm1 : i = -1
    · subst hm1; decide
    · by_cases hp1 : i = 1
      · subst hp1; decide
      · have h2 : i ≤ -2 ∨ 2 ≤ i := by omega
        simp [h0, h2]

private lemma cell_one_period (t : ℕ) (i : ℤ) :
    cell 1 (t + 2) i = cell 1 t i := by
  induction t generalizing i with
  | zero => exact cell_one_two i
  | succ t ih =>
    change ruleOut 1 (cell 1 (t + 2) (i - 1)) (cell 1 (t + 2) i) (cell 1 (t + 2) (i + 1)) =
      ruleOut 1 (cell 1 t (i - 1)) (cell 1 t i) (cell 1 t (i + 1))
    rw [ih, ih, ih]

private lemma cell_one_even (k : ℕ) (i : ℤ) :
    cell 1 (2 * k) i = decide (i = 0) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have h : 2 * (k + 1) = 2 * k + 2 := by omega
    rw [h, cell_one_period, ih]

private lemma cell_one_odd (k : ℕ) (i : ℤ) :
    cell 1 (2 * k + 1) i = decide (i ≤ -2 ∨ 2 ≤ i) := by
  induction k with
  | zero => exact cell_one_one i
  | succ k ih =>
    have h : 2 * (k + 1) + 1 = (2 * k + 1) + 2 := by omega
    rw [h, cell_one_period, ih]

private lemma a_even (k : ℕ) : a (2 * k) = 1 := by
  unfold a
  have hmem : 2 * k ∈ Finset.range (2 * (2 * k) + 1) := by
    rw [Finset.mem_range]; omega
  trans (∑ j ∈ Finset.range (2 * (2 * k) + 1), if j = 2 * k then (1 : ℤ) else 0)
  · refine Finset.sum_congr rfl ?_
    intro j _
    rw [cell_one_even]
    by_cases hj : j = 2 * k
    · subst hj; simp
    · have hne : ¬ ((j : ℤ) - ↑(2 * k) = 0) := by omega
      rw [decide_eq_false hne]
      simp [hj]
  · simp [hmem]

private lemma a_odd (k : ℕ) : a (2 * k + 1) = 4 * (k : ℤ) := by
  cases k with
  | zero =>
    unfold a
    simp only [Nat.mul_zero, Nat.zero_add]
    have hsum : (∑ j ∈ Finset.range 3, if cell 1 1 ((j : ℤ) - 1) = true then (1 : ℤ) else 0) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro j hj
      rw [Finset.mem_range] at hj
      rw [cell_one_odd 0]
      have hfalse : ¬ ((j : ℤ) - 1 ≤ -2 ∨ 2 ≤ (j : ℤ) - 1) := by omega
      rw [decide_eq_false hfalse]
      simp
    simpa using hsum
  | succ m =>
    unfold a
    set n : ℕ := 2 * (m + 1) + 1 with hn_def
    have hm1 : n - 1 ∈ Finset.range (2 * n + 1) := by rw [Finset.mem_range]; omega
    have hm2 : n ∈ Finset.range (2 * n + 1) := by rw [Finset.mem_range]; omega
    have hm3 : n + 1 ∈ Finset.range (2 * n + 1) := by rw [Finset.mem_range]; omega
    have hcongr :
        (∑ j ∈ Finset.range (2 * n + 1),
          if cell 1 n ((j : ℤ) - (n : ℤ)) = true then (1 : ℤ) else 0) =
        ∑ j ∈ Finset.range (2 * n + 1),
          ((1 : ℤ) - (if j = n - 1 then 1 else 0) -
            (if j = n then 1 else 0) - (if j = n + 1 then 1 else 0)) := by
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [hn_def, cell_one_odd, ← hn_def]
      by_cases h1 : j = n - 1
      · subst h1
        have hlt : ¬ ((↑(n - 1) : ℤ) - (n : ℤ) ≤ -2 ∨ 2 ≤ (↑(n - 1) : ℤ) - (n : ℤ)) := by omega
        have hne1 : n - 1 ≠ n := by omega
        have hne2 : n - 1 ≠ n + 1 := by omega
        rw [decide_eq_false hlt]
        simp [hne1, hne2]
      · by_cases h2 : j = n
        · subst h2
          have hlt : ¬ ((n : ℤ) - (n : ℤ) ≤ -2 ∨ 2 ≤ (n : ℤ) - (n : ℤ)) := by omega
          have hne2 : n ≠ n + 1 := by omega
          rw [decide_eq_false hlt]
          simp [h1, hne2]
        · by_cases h3 : j = n + 1
          · subst h3
            have hlt : ¬ ((↑(n + 1) : ℤ) - (n : ℤ) ≤ -2 ∨ 2 ≤ (↑(n + 1) : ℤ) - (n : ℤ)) := by omega
            rw [decide_eq_false hlt]
            simp [h1, h2]
          · have hok : (j : ℤ) - (n : ℤ) ≤ -2 ∨ 2 ≤ (j : ℤ) - (n : ℤ) := by omega
            rw [decide_eq_true hok]
            simp [h1, h2, h3]
    rw [hcongr]
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
      Finset.sum_ite_eq', hm1, hm2, hm3, ↓reduceIte]
    omega

private lemma a_rec (n : ℕ) (hn : 3 < n) :
    a n = 2 * a (n - 2) - a (n - 4) := by
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · have hk : 2 ≤ k := by omega
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hk
    have h1 : 2 * (m + 2) - 2 = 2 * (m + 1) := by omega
    have h2 : 2 * (m + 2) - 4 = 2 * m := by omega
    rw [h1, h2, a_even, a_even, a_even]
    rfl
  · have hk : 2 ≤ k := by omega
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hk
    have h1 : 2 * (m + 2) + 1 - 2 = 2 * (m + 1) + 1 := by omega
    have h2 : 2 * (m + 2) + 1 - 4 = 2 * m + 1 := by omega
    rw [h1, h2, a_odd, a_odd, a_odd]
    push_cast
    ring

theorem OMA.solution : type_of% @OMA.S_oeis_a265722.main := by
  refine ⟨?_, ?_, ?_⟩
  · intro n
    rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
    · rw [a_even]
      have hpow : (-1 : ℚ) ^ ((2 * k : ℕ) : ℤ) = 1 := by
        rw [zpow_natCast, pow_mul]
        norm_num
      rw [hpow]
      push_cast
      ring
    · rw [a_odd]
      have hpow : (-1 : ℚ) ^ ((2 * k + 1 : ℕ) : ℤ) = -1 := by
        rw [zpow_natCast, pow_succ, pow_mul]
        norm_num
      rw [hpow]
      push_cast
      ring
  · intro n hn
    exact a_rec n hn
  · set F : PowerSeries ℚ := PowerSeries.mk (fun n => (a n : ℚ)) with hF
    have hrew : F * ((1 - (X : PowerSeries ℚ)) ^ 2 * (1 + X) ^ 2) =
        F - C (2 : ℚ) * (X ^ 2 * F) + X ^ 4 * F := by
      have h2 : C (2 : ℚ) = (2 : PowerSeries ℚ) := map_ofNat (C (R := ℚ)) 2
      rw [h2]
      ring
    have hrhs : (1 : PowerSeries ℚ) - X ^ 2 + 4 * X ^ 3 =
        1 - X ^ 2 + C (4 : ℚ) * X ^ 3 := by
      have h4 : C (4 : ℚ) = (4 : PowerSeries ℚ) := map_ofNat (C (R := ℚ)) 4
      rw [h4]
    rw [hrew, hrhs]
    ext n
    simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul',
      PowerSeries.coeff_one, PowerSeries.coeff_X_pow, hF, PowerSeries.coeff_mk]
    rcases n with _ | _ | _ | _ | n
    · have h0 : a 0 = 1 := a_even 0
      simp [h0]
    · have h1 : a 1 = 0 := a_odd 0
      simp [h1]
    · have h2 : a 2 = 1 := a_even 1
      have h0 : a 0 = 1 := a_even 0
      simp [h2, h0]
      norm_num
    · have h3 : a 3 = 4 := a_odd 1
      have h1 : a 1 = 0 := a_odd 0
      simp [h3, h1]
    · have hrec := a_rec (n + 4) (by omega)
      have hq : (a (n + 4) : ℚ) = 2 * (a (n + 2) : ℚ) - (a n : ℚ) := by
        have hsub1 : n + 4 - 2 = n + 2 := by omega
        have hsub2 : n + 4 - 4 = n := by omega
        rw [hsub1, hsub2] at hrec
        exact_mod_cast hrec
      have hne0 : ¬ (n + 4 = 0) := by omega
      have hne2 : ¬ (n + 4 = 2) := by omega
      have hne3 : ¬ (n + 4 = 3) := by omega
      have hle2 : (2 : ℕ) ≤ n + 4 := by omega
      have hle4 : (4 : ℕ) ≤ n + 4 := by omega
      simp only [hne0, hne2, hne3, hle2, hle4, ↓reduceIte]
      have hs2 : n + 4 - 2 = n + 2 := by omega
      have hs4 : n + 4 - 4 = n := by omega
      rw [hs2, hs4]
      linarith
