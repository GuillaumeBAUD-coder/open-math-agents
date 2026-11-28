import OMAReductions.R_oeis_a050412_R1

-- Step oeis-a050412.R1.H1: hypothesis H1 of reduction oeis-a050412.R1
-- Credit: @eoin-or
-- H1 := IsRiesel 509203

private lemma riesel_step {k p m r : ℕ}
    (hp1 : 1 < p) (hp_lt : p < 509203 * 2 - 1)
    (hpow : 2 ^ m % p = 1) (hbase : (509203 * 2 ^ r) % p = 1)
    (hk : 1 ≤ k) (hmod : k % m = r) :
    ¬ (509203 * 2 ^ k - 1).Prime := by
  have hpow_mod : 2 ^ m ≡ 1 [MOD p] := by
    rw [Nat.ModEq, hpow, Nat.mod_eq_of_lt hp1]
  have h2k : 2 ^ k ≡ 2 ^ r [MOD p] := by
    have hk_eq : k = m * (k / m) + r := by
      rw [← hmod, Nat.div_add_mod]
    rw [hk_eq, pow_add, pow_mul]
    simpa [one_pow, one_mul] using (hpow_mod.pow (k / m)).mul_right (2 ^ r)
  have hmul : 509203 * 2 ^ k ≡ 1 [MOD p] := by
    have h1 := h2k.mul_left 509203
    have h2 : 509203 * 2 ^ r ≡ 1 [MOD p] := by
      rw [Nat.ModEq, hbase, Nat.mod_eq_of_lt hp1]
    exact h1.trans h2
  have hmod1 : (509203 * 2 ^ k) % p = 1 := by
    rw [Nat.ModEq, Nat.mod_eq_of_lt hp1] at hmul
    exact hmul
  have hdvd : p ∣ 509203 * 2 ^ k - 1 := by
    have hdiv := Nat.div_add_mod (509203 * 2 ^ k) p
    exact ⟨509203 * 2 ^ k / p, by omega⟩
  have h2_le : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hlt : p < 509203 * 2 ^ k - 1 := by
    have : 509203 * 2 ≤ 509203 * 2 ^ k := Nat.mul_le_mul_left 509203 h2_le
    omega
  intro hprime
  rcases hprime.eq_one_or_self_of_dvd p hdvd with rfl | rfl <;> omega

theorem OMA.solution : OMA.R_oeis_a050412_R1.H1 := by
  refine ⟨⟨254601, by norm_num⟩, ?_⟩
  intro k hk
  by_cases h2 : k % 2 = 0
  · exact riesel_step (p := 3) (m := 2) (r := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk h2
  · by_cases h4 : k % 4 = 1
    · exact riesel_step (p := 5) (m := 4) (r := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk h4
    · by_cases h3 : k % 3 = 2
      · exact riesel_step (p := 7) (m := 3) (r := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk h3
      · by_cases h8 : k % 8 = 7
        · exact riesel_step (p := 17) (m := 8) (r := 7) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk h8
        · by_cases h12 : k % 12 = 7
          · exact riesel_step (p := 13) (m := 12) (r := 7) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk h12
          · exact riesel_step (p := 241) (m := 24) (r := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk (by omega)

