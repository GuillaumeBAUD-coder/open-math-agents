import OMAStatements.S_oeis_a267921

namespace OMA.S_oeis_a267921_Proof

open OMA.S_oeis_a267921

private lemma bit_true : bit true = 1 := rfl
private lemma bit_false : bit false = 0 := rfl

private lemma rule_eq (l c r : Bool) : rule l c r = (l || !c) := by
  cases l <;> cases c <;> cases r <;> decide

private lemma state_succ (n : ℕ) (x : ℤ) : state (n + 1) x = decide (x ≠ (n : ℤ)) := by
  induction n generalizing x with
  | zero =>
    simp only [state, step, initial, rule_eq, Nat.cast_zero]
    by_cases hx : x = 0
    · subst hx
      decide
    · simp [hx]
  | succ n ih =>
    change step (state (n + 1)) x = decide (x ≠ ((n + 1 : ℕ) : ℤ))
    simp only [step, rule_eq, ih, Nat.cast_succ]
    by_cases hx : x = (n : ℤ) + 1
    · subst hx
      have h1 : (n : ℤ) + 1 - 1 = (n : ℤ) := by omega
      have h2 : (n : ℤ) + 1 ≠ (n : ℤ) := by omega
      rw [h1]
      simp [h2]
    · have h1 : x - 1 ≠ (n : ℤ) := by omega
      simp [h1, hx]

private lemma encode_all_true (g : Row) (left : ℤ) (m : ℕ)
    (h : ∀ k : ℕ, k < m → g (left + (k : ℤ)) = true) :
    encode g left m = 2 ^ m - 1 := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have hm : encode g left m = 2 ^ m - 1 := ih (fun k hk => h k (Nat.lt_succ_of_lt hk))
    have hlast : g (left + (m : ℤ)) = true := h m (Nat.lt_succ_self m)
    simp only [encode, hm, hlast, bit_true]
    have hpos : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    rw [pow_succ]
    omega

private lemma encode_add_two (g : Row) (left : ℤ) (m : ℕ) :
    encode g left (m + 2) =
      2 * (2 * encode g left m + bit (g (left + (m : ℤ)))) +
        bit (g (left + ((m + 1 : ℕ) : ℤ))) := rfl

private lemma a_zero : a 0 = 1 := by decide

private lemma a_succ (n : ℕ) : a (n + 1) = 2 ^ (2 * n + 3) - 3 := by
  unfold a
  have hlen : 2 * (n + 1) + 1 = (2 * n + 1) + 2 := by omega
  rw [hlen, encode_add_two]
  have hall : encode (state (n + 1)) (-((n + 1 : ℕ) : ℤ)) (2 * n + 1) = 2 ^ (2 * n + 1) - 1 := by
    apply encode_all_true
    intro k hk
    rw [state_succ]
    exact decide_eq_true (by omega)
  have hpen : state (n + 1) (-((n + 1 : ℕ) : ℤ) + ((2 * n + 1 : ℕ) : ℤ)) = false := by
    rw [state_succ]
    exact decide_eq_false (by omega)
  have hlast : state (n + 1) (-((n + 1 : ℕ) : ℤ) + (((2 * n + 1) + 1 : ℕ) : ℤ)) = true := by
    rw [state_succ]
    exact decide_eq_true (by omega)
  rw [hall, hpen, hlast, bit_false, bit_true]
  have hpos : 1 ≤ 2 ^ (2 * n + 1) := Nat.one_le_two_pow
  have hpow : 2 ^ (2 * n + 3) = 4 * 2 ^ (2 * n + 1) := by
    have : 2 * n + 3 = (2 * n + 1) + 2 := by omega
    rw [this, pow_add]
    ring
  omega

private lemma a_one : a 1 = 5 := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, a_succ]
  decide

private lemma a_two : a 2 = 29 := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, a_succ]
  decide

private lemma a_succ_int (n : ℕ) : (a (n + 1) : ℤ) = (2 : ℤ) ^ (2 * n + 3) - 3 := by
  rw [a_succ]
  have hle : 3 ≤ 2 ^ (2 * n + 3) := by
    have h1 : 2 ^ 3 ≤ 2 ^ (2 * n + 3) := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  rw [Nat.cast_sub hle]
  push_cast
  rfl

private lemma recurrence (n : ℕ) (hn : 2 < n) :
    (a n : ℤ) = 5 * (a (n - 1) : ℤ) - 4 * (a (n - 2) : ℤ) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  have h1 : k + 3 - 1 = k + 2 := by omega
  have h2 : k + 3 - 2 = k + 1 := by omega
  rw [h1, h2]
  have ha3 : (a (k + 3) : ℤ) = (2 : ℤ) ^ (2 * (k + 2) + 3) - 3 := a_succ_int (k + 2)
  have ha2 : (a (k + 2) : ℤ) = (2 : ℤ) ^ (2 * (k + 1) + 3) - 3 := a_succ_int (k + 1)
  have ha1 : (a (k + 1) : ℤ) = (2 : ℤ) ^ (2 * k + 3) - 3 := a_succ_int k
  rw [ha3, ha2, ha1]
  have hp1 : (2 : ℤ) ^ (2 * (k + 2) + 3) = 16 * (2 : ℤ) ^ (2 * k + 3) := by
    have : 2 * (k + 2) + 3 = (2 * k + 3) + 4 := by omega
    rw [this, pow_add]
    ring
  have hp2 : (2 : ℤ) ^ (2 * (k + 1) + 3) = 4 * (2 : ℤ) ^ (2 * k + 3) := by
    have : 2 * (k + 1) + 3 = (2 * k + 3) + 2 := by omega
    rw [this, pow_add]
    ring
  rw [hp1, hp2]
  ring

private lemma recurrence_succ3 (k : ℕ) :
    (a (k + 3) : ℤ) = 5 * (a (k + 2) : ℤ) - 4 * (a (k + 1) : ℤ) := by
  have h := recurrence (k + 3) (by omega)
  have h1 : k + 3 - 1 = k + 2 := by omega
  have h2 : k + 3 - 2 = k + 1 := by omega
  rw [h1, h2] at h
  exact h

private lemma coeff_zero_X_mul (φ : PowerSeries ℤ) :
    PowerSeries.coeff 0 (PowerSeries.X * φ) = 0 := by
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul, PowerSeries.constantCoeff_X, zero_mul]

private lemma gf_eq :
    series * ((1 - PowerSeries.X) * (1 - 4 * PowerSeries.X)) =
      1 + 8 * PowerSeries.X ^ 2 := by
  have hL : series * ((1 - PowerSeries.X) * (1 - 4 * PowerSeries.X)) =
      series - (5 : ℕ) • (PowerSeries.X * series) +
        (4 : ℕ) • (PowerSeries.X * (PowerSeries.X * series)) := by
    simp only [nsmul_eq_mul, Nat.cast_ofNat]
    ring
  have hR : (1 : PowerSeries ℤ) + 8 * PowerSeries.X ^ 2 =
      1 + (8 : ℕ) • (PowerSeries.X ^ 2) := by
    simp only [nsmul_eq_mul, Nat.cast_ofNat]
  rw [hL, hR]
  ext n
  simp only [map_add, map_sub, map_nsmul, PowerSeries.coeff_one, PowerSeries.coeff_X_pow]
  match n with
  | 0 =>
    simp only [coeff_zero_X_mul, series, PowerSeries.coeff_mk, a_zero, nsmul_eq_mul, Nat.cast_ofNat]
    rw [if_neg (show (0 : ℕ) ≠ 2 by omega)]
    simp only [ite_true]
    norm_num
  | 1 =>
    have h1 : PowerSeries.coeff 1 (PowerSeries.X * series) = PowerSeries.coeff 0 series :=
      PowerSeries.coeff_succ_X_mul 0 series
    have h2 : PowerSeries.coeff 1 (PowerSeries.X * (PowerSeries.X * series)) = 0 := by
      rw [PowerSeries.coeff_succ_X_mul 0, coeff_zero_X_mul]
    rw [h1, h2]
    simp only [series, PowerSeries.coeff_mk, a_zero, a_one, nsmul_eq_mul, Nat.cast_ofNat]
    rw [if_neg (show (1 : ℕ) ≠ 0 by omega), if_neg (show (1 : ℕ) ≠ 2 by omega)]
    norm_num
  | 2 =>
    have h1 : PowerSeries.coeff 2 (PowerSeries.X * series) = PowerSeries.coeff 1 series :=
      PowerSeries.coeff_succ_X_mul 1 series
    have h2 : PowerSeries.coeff 2 (PowerSeries.X * (PowerSeries.X * series)) =
        PowerSeries.coeff 0 series := by
      rw [PowerSeries.coeff_succ_X_mul 1, PowerSeries.coeff_succ_X_mul 0]
    rw [h1, h2]
    simp only [series, PowerSeries.coeff_mk, a_zero, a_one, a_two, nsmul_eq_mul, Nat.cast_ofNat]
    rw [if_neg (show (2 : ℕ) ≠ 0 by omega)]
    simp only [ite_true]
    norm_num
  | k + 3 =>
    have h1 : PowerSeries.coeff (k + 3) (PowerSeries.X * series) =
        PowerSeries.coeff (k + 2) series :=
      PowerSeries.coeff_succ_X_mul (k + 2) series
    have h2 : PowerSeries.coeff (k + 3) (PowerSeries.X * (PowerSeries.X * series)) =
        PowerSeries.coeff (k + 1) series := by
      rw [PowerSeries.coeff_succ_X_mul (k + 2), PowerSeries.coeff_succ_X_mul (k + 1)]
    rw [h1, h2]
    simp only [series, PowerSeries.coeff_mk, nsmul_eq_mul, Nat.cast_ofNat]
    rw [if_neg (show k + 3 ≠ 0 by omega), if_neg (show k + 3 ≠ 2 by omega)]
    have hrec := recurrence_succ3 k
    omega

end OMA.S_oeis_a267921_Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a267921.main :=
  ⟨OMA.S_oeis_a267921_Proof.recurrence, OMA.S_oeis_a267921_Proof.gf_eq⟩
