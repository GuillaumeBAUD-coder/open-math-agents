import OMAStatements.S_oeis_a363228

-- Problem: A363228: Exponent of 4 in 9^n - 1.
-- Upstream: formal-conjectures statements/oeis-a363228.lean:0 (declaration OMA.S_oeis_a363228.main)
-- Credit: @thtsben2 (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.Proof_oeis_a363228

open OMA.S_oeis_a363228

private lemma fac2_eq_of_dvd_not_dvd {m k : ℕ} (hm : 0 < m)
    (h1 : 2 ^ k ∣ m) (h2 : ¬ 2 ^ (k + 1) ∣ m) : m.factorization 2 = k := by
  have hle : k ≤ m.factorization 2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hm.ne').mp h1
  have hlt : ¬ k + 1 ≤ m.factorization 2 := fun h =>
    h2 ((Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hm.ne').mpr h)
  omega

private lemma exp4_eq_div_two (m : ℕ) (hm : 0 < m) : exp4 m = m.factorization 2 / 2 := by
  unfold exp4
  let r : ℕ := m.factorization 2 / 2
  have hpow : 2 ^ m.factorization 2 ≤ m := Nat.le_of_dvd hm (Nat.ordProj_dvd m 2)
  have hlt : m.factorization 2 < 2 ^ m.factorization 2 := Nat.lt_two_pow_self
  have hr_le : r ≤ m := by omega
  have h4eq : ∀ k, (4 : ℕ) ^ k = 2 ^ (2 * k) := fun k => by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
  have hr_dvd : 4 ^ r ∣ m := by
    rw [h4eq]
    exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hm.ne').mpr (by omega)
  have hspec : 4 ^ Nat.findGreatest (fun k => 4 ^ k ∣ m) m ∣ m :=
    Nat.findGreatest_spec (P := fun k => 4 ^ k ∣ m) (Nat.zero_le m) (by norm_num)
  rw [h4eq] at hspec
  have hfg_le := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hm.ne').mp hspec
  have hle_fg := Nat.le_findGreatest (P := fun k => 4 ^ k ∣ m) hr_le hr_dvd
  omega

private lemma exp4_eq_zero_of_not_four_dvd {m : ℕ} (h : ¬ 4 ∣ m) : exp4 m = 0 := by
  unfold exp4
  by_contra hne
  have hpos : 0 < Nat.findGreatest (fun k => 4 ^ k ∣ m) m := Nat.pos_of_ne_zero hne
  have hspec : 4 ^ Nat.findGreatest (fun k => 4 ^ k ∣ m) m ∣ m :=
    Nat.findGreatest_spec (P := fun k => 4 ^ k ∣ m) (Nat.zero_le m) (by norm_num)
  have h4 : 4 ∣ 4 ^ Nat.findGreatest (fun k => 4 ^ k ∣ m) m := by
    have : 4 = 4 ^ 1 := (pow_one 4).symm
    rw [this]
    exact Nat.pow_dvd_pow 4 hpos
  exact h (h4.trans hspec)

private lemma nine_pow_mod_four (k : ℕ) : 9 ^ k % 4 = 1 := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [pow_succ, Nat.mul_mod, ih]

private lemma nine_pow_two_mul_mod_sixteen (q : ℕ) : 9 ^ (2 * q) % 16 = 1 := by
  induction q with
  | zero => norm_num
  | succ q ih =>
    rw [show 2 * (q + 1) = 2 * q + 2 by ring, pow_add, Nat.mul_mod, ih]
    norm_num

private lemma fac2_nine_pow_sub_one (n : ℕ) (hn : 1 ≤ n) :
    (9 ^ n - 1).factorization 2 = 3 + n.factorization 2 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have h9 : 9 ≤ 9 ^ n := by
      calc 9 = 9 ^ 1 := (pow_one 9).symm
        _ ≤ 9 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have hpos : 0 < 9 ^ n - 1 := by omega
    rcases Nat.mod_two_eq_zero_or_one n with heven | hodd
    · obtain ⟨k, hk⟩ : ∃ k, n = 2 * k := ⟨n / 2, by omega⟩
      have hk1 : 1 ≤ k := by omega
      have hkn : k < n := by omega
      have h9k : 1 ≤ 9 ^ k := Nat.one_le_pow k 9 (by norm_num)
      have hmul : 9 ^ n - 1 = (9 ^ k - 1) * (9 ^ k + 1) := by
        rw [hk, pow_mul']
        have h9k2 : 1 ≤ (9 ^ k) ^ 2 := Nat.one_le_pow 2 (9 ^ k) h9k
        zify [h9k, h9k2]
        ring
      have hmod4 : (9 ^ k + 1) % 4 = 2 := by
        have := nine_pow_mod_four k
        omega
      have hfac_add : (9 ^ k + 1).factorization 2 = 1 := by
        apply fac2_eq_of_dvd_not_dvd (by omega)
        · rw [pow_one]
          omega
        · rw [show (2 : ℕ) ^ (1 + 1) = 4 by norm_num]
          omega
      have h9k_pos : 0 < 9 ^ k - 1 := by
        have : 9 ≤ 9 ^ k := by
          calc 9 = 9 ^ 1 := (pow_one 9).symm
            _ ≤ 9 ^ k := Nat.pow_le_pow_right (by norm_num) hk1
        omega
      have hfac_prod : (9 ^ n - 1).factorization 2 =
          (9 ^ k - 1).factorization 2 + (9 ^ k + 1).factorization 2 := by
        rw [hmul, Nat.factorization_mul h9k_pos.ne' (by omega), Finsupp.add_apply]
      have hfac_n : n.factorization 2 = k.factorization 2 + 1 := by
        rw [hk, Nat.factorization_mul (by norm_num) (by omega), Finsupp.add_apply,
          Nat.Prime.factorization_self Nat.prime_two]
        omega
      rw [hfac_prod, ih k hkn hk1, hfac_add, hfac_n]
      omega
    · have hmod16 : 9 ^ n % 16 = 9 := by
        rw [show n = 2 * (n / 2) + 1 by omega, pow_add, pow_one, Nat.mul_mod,
          nine_pow_two_mul_mod_sixteen (n / 2)]
      have hsub_mod16 : (9 ^ n - 1) % 16 = 8 := by omega
      have hfac3 : (9 ^ n - 1).factorization 2 = 3 := by
        apply fac2_eq_of_dvd_not_dvd hpos
        · rw [show (2 : ℕ) ^ 3 = 8 by norm_num]
          omega
        · rw [show (2 : ℕ) ^ (3 + 1) = 16 by norm_num]
          omega
      have hndvd : ¬ 2 ∣ n := by omega
      rw [hfac3, Nat.factorization_eq_zero_of_not_dvd hndvd, add_zero]

private lemma fib_add_six_mod_four (m : ℕ) : Nat.fib (m + 6) % 4 = Nat.fib m % 4 := by
  have h := Nat.fib_add 5 m
  rw [show 5 + m + 1 = m + 6 by ring, show m + 1 = 1 + m by ring] at h
  have h5 : Nat.fib 5 = 5 := by norm_num [Nat.fib_add_two, Nat.fib_one, Nat.fib_two]
  have h6 : Nat.fib 6 = 8 := by norm_num [Nat.fib_add_two, Nat.fib_one, Nat.fib_two]
  rw [h5, h6] at h
  omega

private lemma fib_mod_four_eq (m : ℕ) : Nat.fib m % 4 = Nat.fib (m % 6) % 4 := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    by_cases hm : m < 6
    · rw [Nat.mod_eq_of_lt hm]
    · have hm6 : m - 6 < m := by omega
      have hstep := fib_add_six_mod_four (m - 6)
      rw [show m - 6 + 6 = m by omega] at hstep
      rw [hstep, ih (m - 6) hm6, show (m - 6) % 6 = m % 6 by omega]

private lemma fib_not_four_dvd {m : ℕ} (hm : ¬ 6 ∣ m) : ¬ 4 ∣ Nat.fib m := by
  have hmod := fib_mod_four_eq m
  have hcases : m % 6 = 1 ∨ m % 6 = 2 ∨ m % 6 = 3 ∨ m % 6 = 4 ∨ m % 6 = 5 := by omega
  rcases hcases with h | h | h | h | h <;> rw [h] at hmod
  · have hval : Nat.fib 1 = 1 := by norm_num [Nat.fib_one]
    omega
  · have hval : Nat.fib 2 = 1 := by norm_num [Nat.fib_two]
    omega
  · have hval : Nat.fib 3 = 2 := by norm_num [Nat.fib_add_two, Nat.fib_one, Nat.fib_two]
    omega
  · have hval : Nat.fib 4 = 3 := by norm_num [Nat.fib_add_two, Nat.fib_one, Nat.fib_two]
    omega
  · have hval : Nat.fib 5 = 5 := by norm_num [Nat.fib_add_two, Nat.fib_one, Nat.fib_two]
    omega

private def lucas : ℕ → ℕ
  | 0 => 2
  | 1 => 1
  | n + 2 => lucas (n + 1) + lucas n

private lemma lucas_pos (n : ℕ) : 0 < lucas n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | n
    · simp [lucas]
    · simp [lucas]
    · simp only [lucas]
      have := ih n (by omega)
      omega

private lemma lucas_add_fib (n : ℕ) : lucas n + Nat.fib n = 2 * Nat.fib (n + 1) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | n
    · simp [lucas]
    · simp [lucas, Nat.fib_two]
    · change lucas (n + 2) + Nat.fib (n + 2) = 2 * Nat.fib (n + 3)
      have ih1 : lucas (n + 1) + Nat.fib (n + 1) = 2 * Nat.fib (n + 2) := ih (n + 1) (by omega)
      have ih0 : lucas n + Nat.fib n = 2 * Nat.fib (n + 1) := ih n (by omega)
      have hl : lucas (n + 2) = lucas (n + 1) + lucas n := rfl
      have hf2 : Nat.fib (n + 2) = Nat.fib n + Nat.fib (n + 1) := Nat.fib_add_two
      have hf3 : Nat.fib (n + 3) = Nat.fib (n + 1) + Nat.fib (n + 2) := by
        rw [show n + 3 = (n + 1) + 2 by ring, Nat.fib_add_two, show n + 1 + 1 = n + 2 by ring]
      omega

private lemma fib_two_mul_lucas (n : ℕ) : Nat.fib (2 * n) = Nat.fib n * lucas n := by
  rw [Nat.fib_two_mul]
  have h := lucas_add_fib n
  rw [show 2 * Nat.fib (n + 1) - Nat.fib n = lucas n by omega]

private lemma lucas_add_six_mod_four (m : ℕ) : lucas (m + 6) % 4 = lucas m % 4 := by
  have h2 : lucas (m + 2) = lucas (m + 1) + lucas m := rfl
  have h3 : lucas (m + 3) = lucas (m + 2) + lucas (m + 1) := rfl
  have h4 : lucas (m + 4) = lucas (m + 3) + lucas (m + 2) := rfl
  have h5 : lucas (m + 5) = lucas (m + 4) + lucas (m + 3) := rfl
  have h6 : lucas (m + 6) = lucas (m + 5) + lucas (m + 4) := rfl
  omega

private lemma lucas_six_mul_mod_four (m : ℕ) : lucas (6 * m) % 4 = 2 := by
  induction m with
  | zero => simp [lucas]
  | succ m ih =>
    rw [show 6 * (m + 1) = 6 * m + 6 by ring, lucas_add_six_mod_four, ih]

private lemma fac2_lucas_six_mul (m : ℕ) : (lucas (6 * m)).factorization 2 = 1 := by
  apply fac2_eq_of_dvd_not_dvd (lucas_pos _)
  · rw [pow_one]
    have := lucas_six_mul_mod_four m
    omega
  · rw [show (2 : ℕ) ^ (1 + 1) = 4 by norm_num]
    have := lucas_six_mul_mod_four m
    omega

private lemma fib_add_twelve (m : ℕ) :
    Nat.fib (m + 12) = 144 * Nat.fib (m + 1) + 89 * Nat.fib m := by
  have h := Nat.fib_add 11 m
  rw [show 11 + m + 1 = m + 12 by ring, show m + 1 = 1 + m by ring] at h
  have h11 : Nat.fib 11 = 89 := by norm_num [Nat.fib_add_two, Nat.fib_one, Nat.fib_two]
  have h12 : Nat.fib 12 = 144 := by norm_num [Nat.fib_add_two, Nat.fib_one, Nat.fib_two]
  rw [h11, h12] at h
  rw [h, show 1 + m = m + 1 by ring]
  ring

private lemma fib_twelve_mul_add_six_mod_sixteen (q : ℕ) :
    Nat.fib (12 * q + 6) % 16 = 8 := by
  induction q with
  | zero =>
    norm_num [Nat.fib_add_two, Nat.fib_one, Nat.fib_two]
  | succ q ih =>
    rw [show 12 * (q + 1) + 6 = 12 * q + 6 + 12 by ring, fib_add_twelve,
      Nat.add_mod, Nat.mul_mod 144, Nat.mul_mod 89, ih]
    norm_num

private lemma fac2_fib_six_mul (n : ℕ) (hn : 1 ≤ n) :
    (Nat.fib (6 * n)).factorization 2 = 3 + n.factorization 2 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.mod_two_eq_zero_or_one n with heven | hodd
    · obtain ⟨k, hk⟩ : ∃ k, n = 2 * k := ⟨n / 2, by omega⟩
      have hk1 : 1 ≤ k := by omega
      have hkn : k < n := by omega
      have hmul : Nat.fib (6 * n) = Nat.fib (6 * k) * lucas (6 * k) := by
        rw [hk, show 6 * (2 * k) = 2 * (6 * k) by ring, fib_two_mul_lucas]
      have hfib_pos : 0 < Nat.fib (6 * k) := Nat.fib_pos.mpr (by omega)
      have hfac_prod : (Nat.fib (6 * n)).factorization 2 =
          (Nat.fib (6 * k)).factorization 2 + (lucas (6 * k)).factorization 2 := by
        rw [hmul, Nat.factorization_mul hfib_pos.ne' (lucas_pos _).ne', Finsupp.add_apply]
      have hfac_n : n.factorization 2 = k.factorization 2 + 1 := by
        rw [hk, Nat.factorization_mul (by norm_num) (by omega), Finsupp.add_apply,
          Nat.Prime.factorization_self Nat.prime_two]
        omega
      rw [hfac_prod, ih k hkn hk1, fac2_lucas_six_mul k, hfac_n]
      omega
    · have hmod16 : Nat.fib (6 * n) % 16 = 8 := by
        rw [show 6 * n = 12 * (n / 2) + 6 by omega]
        exact fib_twelve_mul_add_six_mod_sixteen (n / 2)
      have hfib_pos : 0 < Nat.fib (6 * n) := Nat.fib_pos.mpr (by omega)
      have hfac3 : (Nat.fib (6 * n)).factorization 2 = 3 := by
        apply fac2_eq_of_dvd_not_dvd hfib_pos
        · rw [show (2 : ℕ) ^ 3 = 8 by norm_num]
          omega
        · rw [show (2 : ℕ) ^ (3 + 1) = 16 by norm_num]
          omega
      have hndvd : ¬ 2 ∣ n := by omega
      rw [hfac3, Nat.factorization_eq_zero_of_not_dvd hndvd, add_zero]

end OMA.Proof_oeis_a363228

theorem OMA.solution : type_of% @OMA.S_oeis_a363228.main := by
  constructor
  · intro n hn
    unfold OMA.S_oeis_a363228.a
    have h9 : 9 ≤ 9 ^ n := by
      calc 9 = 9 ^ 1 := (pow_one 9).symm
        _ ≤ 9 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have h9_pos : 0 < 9 ^ n - 1 := by omega
    have hfib_pos : 0 < Nat.fib (6 * n) := Nat.fib_pos.mpr (by omega)
    rw [OMA.Proof_oeis_a363228.exp4_eq_div_two _ h9_pos,
      OMA.Proof_oeis_a363228.exp4_eq_div_two _ hfib_pos,
      OMA.Proof_oeis_a363228.fac2_nine_pow_sub_one n hn,
      OMA.Proof_oeis_a363228.fac2_fib_six_mul n hn]
  · intro m hm hndvd
    exact OMA.Proof_oeis_a363228.exp4_eq_zero_of_not_four_dvd
      (OMA.Proof_oeis_a363228.fib_not_four_dvd hndvd)
