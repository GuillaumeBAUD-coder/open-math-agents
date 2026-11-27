import OMAStatements.S_oeis_a267921

/-!
Proof of OEIS A267921 (Rule 243 elementary cellular automaton from a single ON cell):
1. rule l c r = (l || !c), so for n >= 1, state n x = decide (x != n - 1).
2. Unfolding encode at 2*n + 1 twice shows (a n : Z) = 2 * 4^n - 3 for n >= 1,
   which immediately yields both the linear recurrence and generating function.
-/

private lemma rule_eq (l c r : Bool) :
    OMA.S_oeis_a267921.rule l c r = (l || !c) := by
  cases l <;> cases c <;> cases r <;> rfl

private lemma state_eq : ∀ n : ℕ, 1 ≤ n → ∀ x : ℤ,
    OMA.S_oeis_a267921.state n x = decide (x ≠ (n : ℤ) - 1)
  | 0, h, _ => absurd h (by omega)
  | 1, _, x => by
      rw [OMA.S_oeis_a267921.state, OMA.S_oeis_a267921.step, rule_eq]
      simp only [OMA.S_oeis_a267921.state, OMA.S_oeis_a267921.initial]
      by_cases hx : x = 0 <;> by_cases hx1 : x - 1 = 0 <;> simp [hx, hx1]
  | n + 2, _, x => by
      have ih := state_eq (n + 1) (by omega)
      rw [OMA.S_oeis_a267921.state, OMA.S_oeis_a267921.step, rule_eq, ih (x - 1), ih x]
      have hcast1 : ((n + 1 : ℕ) : ℤ) - 1 = (n : ℤ) := by push_cast; ring
      have hcast2 : ((n + 2 : ℕ) : ℤ) - 1 = (n : ℤ) + 1 := by push_cast; ring
      rw [hcast1, hcast2]
      by_cases hx1 : x - 1 = (n : ℤ) <;> by_cases hx : x = (n : ℤ) <;>
        simp [hx1, hx] <;> omega

private lemma encode_all_true (g : OMA.S_oeis_a267921.Row) (left : ℤ) :
    ∀ k : ℕ, (∀ t : ℕ, t < k → g (left + (t : ℤ)) = true) →
      (OMA.S_oeis_a267921.encode g left k : ℤ) = 2 ^ k - 1
  | 0, _ => by simp [OMA.S_oeis_a267921.encode]
  | k + 1, hk => by
      have ih := encode_all_true g left k fun t ht => hk t (Nat.lt_succ_of_lt ht)
      have hlast : g (left + (k : ℤ)) = true := hk k (Nat.lt_succ_self k)
      simp only [OMA.S_oeis_a267921.encode, hlast, OMA.S_oeis_a267921.bit, ite_true]
      push_cast
      rw [ih, pow_succ']
      ring

private lemma a_eq (n : ℕ) (hn : 1 ≤ n) :
    (OMA.S_oeis_a267921.a n : ℤ) = 2 * 4 ^ n - 3 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hlen : 2 * (k + 1) + 1 = (2 * k + 1) + 1 + 1 := by omega
  rw [OMA.S_oeis_a267921.a, hlen, OMA.S_oeis_a267921.encode, OMA.S_oeis_a267921.encode]
  rw [state_eq (k + 1) (by omega), state_eq (k + 1) (by omega)]
  rw [decide_eq_false_iff_not.mpr (not_not.mpr (by push_cast; ring)),
    decide_eq_true_iff.mpr (by push_cast; omega)]
  simp only [OMA.S_oeis_a267921.bit, Bool.false_eq_true, ite_false, ite_true]
  push_cast
  rw [encode_all_true _ _ _ fun t ht => by
    rw [state_eq (k + 1) (by omega), decide_eq_true_iff]
    push_cast
    omega]
  have hpow : (4 : ℤ) ^ (k + 1) = 2 * (2 : ℤ) ^ (2 * k + 1) := by
    have h4 : (4 : ℤ) = 2 ^ 2 := by norm_num
    rw [h4, ← pow_mul, show 2 * (k + 1) = (2 * k + 1) + 1 by omega, pow_succ']
  linarith

theorem OMA.solution : type_of% @OMA.S_oeis_a267921.main := by
  have hrec : ∀ n : ℕ, 2 < n →
      (OMA.S_oeis_a267921.a n : ℤ) =
        5 * (OMA.S_oeis_a267921.a (n - 1) : ℤ) - 4 * (OMA.S_oeis_a267921.a (n - 2) : ℤ) := by
    intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
    have hn0 := a_eq (k + 3) (by omega)
    have hn1 := a_eq (k + 2) (by omega)
    have hn2 := a_eq (k + 1) (by omega)
    have hsub1 : k + 3 - 1 = k + 2 := by omega
    have hsub2 : k + 3 - 2 = k + 1 := by omega
    rw [hsub1, hsub2, hn0, hn1, hn2]
    have h41 : (4 : ℤ) ^ (k + 2) = 4 * (4 : ℤ) ^ (k + 1) := by rw [pow_succ']
    have h42 : (4 : ℤ) ^ (k + 3) = 4 * (4 : ℤ) ^ (k + 2) := by rw [pow_succ']
    linarith
  refine ⟨hrec, ?_⟩
  have hC4 : (4 : PowerSeries ℤ) = PowerSeries.C (4 : ℤ) := by
    rw [← Nat.cast_ofNat, ← map_natCast (PowerSeries.C (R := ℤ)), Nat.cast_ofNat]
  have hC5 : (5 : PowerSeries ℤ) = PowerSeries.C (5 : ℤ) := by
    rw [← Nat.cast_ofNat, ← map_natCast (PowerSeries.C (R := ℤ)), Nat.cast_ofNat]
  have hC8 : (8 : PowerSeries ℤ) = PowerSeries.C (8 : ℤ) := by
    rw [← Nat.cast_ofNat, ← map_natCast (PowerSeries.C (R := ℤ)), Nat.cast_ofNat]
  have hpoly : OMA.S_oeis_a267921.series *
      ((1 - PowerSeries.X) * (1 - 4 * PowerSeries.X)) =
      OMA.S_oeis_a267921.series - PowerSeries.C 5 * (PowerSeries.X * OMA.S_oeis_a267921.series) +
        PowerSeries.C 4 * (PowerSeries.X * (PowerSeries.X * OMA.S_oeis_a267921.series)) := by
    rw [← hC4, ← hC5]
    ring
  rw [hpoly, hC8]
  ext m
  have ha0 : (OMA.S_oeis_a267921.a 0 : ℤ) = 1 := rfl
  have ha1 : (OMA.S_oeis_a267921.a 1 : ℤ) = 5 := by
    rw [a_eq 1 (by omega)]
    norm_num
  have ha2 : (OMA.S_oeis_a267921.a 2 : ℤ) = 29 := by
    rw [a_eq 2 (by omega)]
    norm_num
  rw [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul,
    map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_one, PowerSeries.coeff_X_pow]
  by_cases hm0 : m = 0
  · subst hm0
    rw [PowerSeries.coeff_zero_X_mul, PowerSeries.coeff_zero_X_mul]
    simp only [OMA.S_oeis_a267921.series, PowerSeries.coeff_mk, ha0]
    norm_num
  · by_cases hm1 : m = 1
    · subst hm1
      rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_zero_X_mul]
      simp only [OMA.S_oeis_a267921.series, PowerSeries.coeff_mk, ha0, ha1]
      norm_num
    · by_cases hm2 : m = 2
      · subst hm2
        rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_succ_X_mul]
        simp only [OMA.S_oeis_a267921.series, PowerSeries.coeff_mk, ha0, ha1, ha2]
        norm_num
      · obtain ⟨k, rfl⟩ : ∃ k, m = k + 3 := ⟨m - 3, by omega⟩
        have hr := hrec (k + 3) (by omega)
        simp only [show k + 3 - 1 = k + 2 by omega, show k + 3 - 2 = k + 1 by omega] at hr
        rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_succ_X_mul]
        have hne0 : k + 3 ≠ 0 := by omega
        have hne2 : k + 3 ≠ 2 := by omega
        simp only [hne0, hne2, ↓reduceIte, OMA.S_oeis_a267921.series, PowerSeries.coeff_mk]
        linarith
