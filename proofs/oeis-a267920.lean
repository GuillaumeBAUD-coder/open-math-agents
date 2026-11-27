import OMAStatements.S_oeis_a267920

open OMA.S_oeis_a267920

namespace OMA.Proof_oeis_a267920

private lemma bit_true : bit true = 1 := rfl
private lemma bit_false : bit false = 0 := rfl

private lemma rule_eq (l c r : Bool) : rule l c r = (l || !c) := by
  cases l <;> cases c <;> cases r <;> rfl

private lemma state_succ (k : ℕ) (x : ℤ) :
    state (k + 1) x = decide (x ≠ (k : ℤ)) := by
  induction k generalizing x with
  | zero =>
    simp only [state, step, initial, rule_eq]
    by_cases hx : x = 0
    · subst hx; decide
    · have h1 : decide (x = 0) = false := decide_eq_false hx
      have h2 : decide (x ≠ ((0 : ℕ) : ℤ)) = true := decide_eq_true (by omega)
      rw [h1, h2]
      cases decide (x - 1 = 0) <;> rfl
  | succ k ih =>
    rw [state, step, rule_eq, ih, ih]
    by_cases h1 : x - 1 = (k : ℤ)
    · have ha : decide (x - 1 ≠ (k : ℤ)) = false := decide_eq_false (by omega)
      have hb : decide (x ≠ (k : ℤ)) = true := decide_eq_true (by omega)
      have hc : decide (x ≠ ((k + 1 : ℕ) : ℤ)) = false := decide_eq_false (by omega)
      rw [ha, hb, hc]; rfl
    · have ha : decide (x - 1 ≠ (k : ℤ)) = true := decide_eq_true h1
      have hc : decide (x ≠ ((k + 1 : ℕ) : ℤ)) = true := decide_eq_true (by omega)
      rw [ha, hc]; rfl

private lemma encode_const_true (g : Row) (left : ℤ) (m : ℕ)
    (h : ∀ j : ℕ, j < m → g (left + (j : ℤ)) = true) :
    9 * encode g left m + 1 = 10 ^ m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have hm : g (left + (m : ℤ)) = true := h m (Nat.lt_succ_self m)
    have hprev : ∀ j : ℕ, j < m → g (left + (j : ℤ)) = true :=
      fun j hj => h j (Nat.lt_succ_of_lt hj)
    have ih' := ih hprev
    rw [encode, hm, bit_true]
    have hpow : 10 ^ (m + 1) = 10 * 10 ^ m := by ring
    omega

private lemma nine_mul_a_succ (k : ℕ) :
    9 * a (k + 1) + 91 = 10 ^ (2 * k + 3) := by
  have hm : 2 * (k + 1) + 1 = (2 * k + 1) + 2 := by omega
  rw [a, hm, encode, encode]
  have htop_val : state (k + 1) (-((k + 1 : ℕ) : ℤ) + ((2 * k + 1 + 1 : ℕ) : ℤ)) = true := by
    rw [state_succ]
    exact decide_eq_true (by omega)
  have hmid_val : state (k + 1) (-((k + 1 : ℕ) : ℤ) + ((2 * k + 1 : ℕ) : ℤ)) = false := by
    rw [state_succ]
    exact decide_eq_false (by omega)
  have hbot : ∀ j : ℕ, j < 2 * k + 1 →
      state (k + 1) (-((k + 1 : ℕ) : ℤ) + (j : ℤ)) = true := by
    intro j hj
    rw [state_succ]
    exact decide_eq_true (by omega)
  have henc := encode_const_true (state (k + 1)) (-((k + 1 : ℕ) : ℤ)) (2 * k + 1) hbot
  rw [htop_val, hmid_val, bit_true, bit_false]
  have hpow : 10 ^ (2 * k + 3) = 100 * 10 ^ (2 * k + 1) := by ring
  omega

private lemma a_zero : a 0 = 1 := rfl

private lemma a_one : a 1 = 101 := by
  have h := nine_mul_a_succ 0
  norm_num at h
  omega

private lemma a_two : a 2 = 11101 := by
  have h := nine_mul_a_succ 1
  norm_num at h
  omega

private lemma a_rec (n : ℕ) (hn : 2 < n) :
    (a n : ℤ) = 101 * (a (n - 1) : ℤ) - 100 * (a (n - 2) : ℤ) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  have h3n : 9 * a (k + 3) + 91 = 10 ^ (2 * k + 7) := by
    have h := nine_mul_a_succ (k + 2)
    have he : 2 * (k + 2) + 3 = 2 * k + 7 := by omega
    rw [he] at h
    exact h
  have h2n : 9 * a (k + 2) + 91 = 10 ^ (2 * k + 5) := by
    have h := nine_mul_a_succ (k + 1)
    have he : 2 * (k + 1) + 3 = 2 * k + 5 := by omega
    rw [he] at h
    exact h
  have h1n : 9 * a (k + 1) + 91 = 10 ^ (2 * k + 3) := nine_mul_a_succ k
  have h3 : (9 : ℤ) * (a (k + 3) : ℤ) + 91 = (10 : ℤ) ^ (2 * k + 7) := by exact_mod_cast h3n
  have h2 : (9 : ℤ) * (a (k + 2) : ℤ) + 91 = (10 : ℤ) ^ (2 * k + 5) := by exact_mod_cast h2n
  have h1 : (9 : ℤ) * (a (k + 1) : ℤ) + 91 = (10 : ℤ) ^ (2 * k + 3) := by exact_mod_cast h1n
  have hp1 : (10 : ℤ) ^ (2 * k + 5) = 100 * (10 : ℤ) ^ (2 * k + 3) := by ring
  have hp2 : (10 : ℤ) ^ (2 * k + 7) = 100 * (10 : ℤ) ^ (2 * k + 5) := by ring
  have hsub2 : k + 3 - 2 = k + 1 := by omega
  have hsub1 : k + 3 - 1 = k + 2 := by omega
  rw [hsub1, hsub2]
  linarith

private lemma series_eq :
    series * ((1 - PowerSeries.X) * (1 - 100 * PowerSeries.X)) =
      1 + 1000 * PowerSeries.X ^ 2 := by
  have h100 : (100 : PowerSeries ℤ) = PowerSeries.C 100 :=
    (map_ofNat (PowerSeries.C (R := ℤ)) 100).symm
  have h101 : (101 : PowerSeries ℤ) = PowerSeries.C 101 :=
    (map_ofNat (PowerSeries.C (R := ℤ)) 101).symm
  have h1000 : (1000 : PowerSeries ℤ) = PowerSeries.C 1000 :=
    (map_ofNat (PowerSeries.C (R := ℤ)) 1000).symm
  have hlhs :
      series * ((1 - PowerSeries.X) * (1 - 100 * PowerSeries.X)) =
        series - PowerSeries.C 101 * (PowerSeries.X * series) +
          PowerSeries.C 100 * (PowerSeries.X * (PowerSeries.X * series)) := by
    rw [← h100, ← h101]
    ring
  have hrhs :
      (1 + 1000 * PowerSeries.X ^ 2 : PowerSeries ℤ) =
        1 + PowerSeries.C 1000 * PowerSeries.X ^ 2 := by
    rw [← h1000]
  rw [hlhs, hrhs]
  apply PowerSeries.ext
  intro n
  rcases n with _ | _ | _ | k
  · simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_one,
      PowerSeries.coeff_X_pow, PowerSeries.coeff_zero_X_mul, series, PowerSeries.coeff_mk]
    rw [a_zero]
    norm_num
  · simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_one,
      PowerSeries.coeff_X_pow, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_zero_X_mul,
      series, PowerSeries.coeff_mk]
    have h1 : (0 : ℕ) + 1 = 1 := rfl
    simp only [h1, a_zero, a_one]
    norm_num
  · simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_one,
      PowerSeries.coeff_X_pow, PowerSeries.coeff_succ_X_mul,
      series, PowerSeries.coeff_mk]
    have h1 : (0 : ℕ) + 1 = 1 := rfl
    have h2 : (0 : ℕ) + 1 + 1 = 2 := rfl
    simp only [h2, h1, a_zero, a_one, a_two]
    norm_num
  · simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_one,
      PowerSeries.coeff_X_pow, PowerSeries.coeff_succ_X_mul,
      series, PowerSeries.coeff_mk]
    have hne0 : k + 1 + 1 + 1 ≠ 0 := by omega
    have hne2 : k + 1 + 1 + 1 ≠ 2 := by omega
    have hrec := a_rec (k + 1 + 1 + 1) (by omega)
    have hs1 : k + 1 + 1 + 1 - 1 = k + 1 + 1 := by omega
    have hs2 : k + 1 + 1 + 1 - 2 = k + 1 := by omega
    rw [hs1, hs2] at hrec
    rw [if_neg hne0, if_neg hne2]
    linarith

end OMA.Proof_oeis_a267920

theorem OMA.solution : type_of% @OMA.S_oeis_a267920.main := by
  exact ⟨OMA.Proof_oeis_a267920.a_rec, OMA.Proof_oeis_a267920.series_eq⟩
