import OMAStatements.S_oeis_a124870

-- Problem: A124870, denominators of Re(((-1 - 3i)/10)^n).
-- Credit: @Dariusthedoggie
-- Proof idea: base^n = (P n + Q n i) / 10^n with integer P, Q. 5 never divides P n
-- (Q n = 3 P n mod 5 from n = 1 on), and for n >= 3, P n = 2^e * odd with 4 Q n divisible by 2^e;
-- since base^4 = (28 - 96 i) / 10^4, each step of 4 raises e by exactly 2. Hence
-- a(n) = 2^(n-e) * 5^n and a(n+4) = 2500 a(n); the series identity follows coefficientwise.

namespace OMA.P124870

open OMA.S_oeis_a124870 PowerSeries

/-- Numerators of the real and imaginary parts of base ^ n over 10 ^ n. -/
def PQ : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | n + 1 => (3 * (PQ n).2 - (PQ n).1, -3 * (PQ n).1 - (PQ n).2)

def P (n : ℕ) : ℤ := (PQ n).1

def Q (n : ℕ) : ℤ := (PQ n).2

lemma P_succ (n : ℕ) : P (n + 1) = 3 * Q n - P n := rfl

lemma Q_succ (n : ℕ) : Q (n + 1) = -3 * P n - Q n := rfl

lemma base_pow (n : ℕ) :
    base ^ n = (⟨(P n : ℚ) / 10 ^ n, (Q n : ℚ) / 10 ^ n⟩ : QI) := by
  induction n with
  | zero =>
    ext
    · show (1 : ℚ) = _
      simp [P, PQ]
    · show (0 : ℚ) = _
      simp [Q, PQ]
  | succ n ih =>
    rw [pow_succ, ih]
    ext
    · simp only [QuadraticAlgebra.re_mul, base, P_succ]
      push_cast
      field_simp
      ring
    · simp only [QuadraticAlgebra.im_mul, base, Q_succ]
      push_cast
      field_simp
      ring

lemma a_eq (n : ℕ) : a n = ((P n : ℚ) / 10 ^ n).den := by
  simp only [a, base_pow]

lemma five_aux (n : ℕ) : (5 : ℤ) ∣ Q (n + 1) - 3 * P (n + 1) := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [P_succ (n + 1), Q_succ (n + 1)]
    omega

lemma five (n : ℕ) : ¬ (5 : ℤ) ∣ P n := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [P_succ]
    rcases n with _ | n
    · decide
    · have := five_aux n
      omega

lemma step4 (m : ℕ) : P (m + 4) = 28 * P m + 96 * Q m ∧ Q (m + 4) = 28 * Q m - 96 * P m := by
  simp only [P_succ, Q_succ]
  constructor <;> ring

lemma den_of {m e : ℕ} {p : ℤ} (he : e ≤ m) (hP : P m = 2 ^ e * p) (hp : Odd p) :
    a m = 2 ^ (m - e) * 5 ^ m := by
  have h5 : ¬ (5 : ℤ) ∣ p := by
    intro h
    exact five m (hP ▸ Dvd.dvd.mul_left h _)
  have hq : (P m : ℚ) / 10 ^ m = ((p : ℤ) : ℚ) / (((2 ^ (m - e) * 5 ^ m : ℕ) : ℤ) : ℚ) := by
    rw [hP]
    obtain ⟨k, rfl⟩ : ∃ k, m = e + k := ⟨m - e, by omega⟩
    rw [show e + k - e = k by omega]
    push_cast
    field_simp
    rw [show (10 : ℚ) = 2 * 5 by norm_num, mul_pow]
    ring
  have hcop : Nat.Coprime p.natAbs (((2 ^ (m - e) * 5 ^ m : ℕ) : ℤ)).natAbs := by
    rw [Int.natAbs_natCast]
    apply Nat.Coprime.mul_right
    · exact Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr (Int.natAbs_odd.mpr hp))
    · apply Nat.Coprime.pow_right
      rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_five]
      intro h
      exact h5 (Int.ofNat_dvd_left.mpr h)
  have := Rat.den_div_eq_of_coprime (by positivity) hcop
  rw [a_eq, hq]
  exact_mod_cast this

lemma inv (m : ℕ) (hm : 3 ≤ m) :
    ∃ e : ℕ, ∃ p q : ℤ, e ≤ m ∧ P m = 2 ^ e * p ∧ 4 * Q m = 2 ^ e * q ∧ Odd p := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases Nat.lt_or_ge m 7 with h7 | h7
    · interval_cases m
      · exact ⟨1, 13, 36, by norm_num, by decide, by decide, ⟨6, by norm_num⟩⟩
      · exact ⟨2, 7, -96, by norm_num, by decide, by decide, ⟨3, by norm_num⟩⟩
      · exact ⟨2, -79, 12, by norm_num, by decide, by decide, ⟨-40, by norm_num⟩⟩
      · exact ⟨5, 11, 117, by norm_num, by decide, by decide, ⟨5, by norm_num⟩⟩
    · obtain ⟨e, p, q, he, hP, hQ, hp⟩ := ih (m - 4) (by omega) (by omega)
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 4 := ⟨m - 4, by omega⟩
      rw [show k + 4 - 4 = k by omega] at hP hQ he
      obtain ⟨s1, s2⟩ := step4 k
      refine ⟨e + 2, 7 * p + 6 * q, 7 * q - 96 * p, by omega, ?_, ?_, ?_⟩
      · rw [s1, pow_add]
        linear_combination 28 * hP + 24 * hQ
      · rw [s2, pow_add]
        linear_combination 28 * hQ - 384 * hP
      · obtain ⟨r, rfl⟩ := hp
        exact ⟨7 * r + 3 * q + 3, by ring⟩

lemma rec4 (m : ℕ) (hm : 3 ≤ m) : a (m + 4) = 2500 * a m := by
  obtain ⟨e, p, q, he, hP, hQ, hp⟩ := inv m hm
  obtain ⟨s1, s2⟩ := step4 m
  have hP4 : P (m + 4) = 2 ^ (e + 2) * (7 * p + 6 * q) := by
    rw [s1, pow_add]
    linear_combination 28 * hP + 24 * hQ
  have hp4 : Odd (7 * p + 6 * q) := by
    obtain ⟨r, rfl⟩ := hp
    exact ⟨7 * r + 3 * q + 3, by ring⟩
  rw [den_of (by omega) hP4 hp4, den_of he hP hp]
  rw [show m + 4 - (e + 2) = (m - e) + 2 by omega, pow_add, pow_add]
  ring

lemma vals : a 0 = 1 ∧ a 1 = 10 ∧ a 2 = 25 ∧ a 3 = 500 ∧ a 4 = 2500 ∧ a 5 = 25000 ∧
    a 6 = 31250 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [a_eq, show P 0 = 1 from rfl]; norm_num
  · rw [a_eq, show P 1 = -1 from rfl]; norm_num
  · rw [a_eq, show P 2 = -8 from rfl]; norm_num
  · rw [den_of (e := 1) (p := 13) (by norm_num) (by decide) ⟨6, by norm_num⟩]; norm_num
  · rw [den_of (e := 2) (p := 7) (by norm_num) (by decide) ⟨3, by norm_num⟩]; norm_num
  · rw [den_of (e := 2) (p := -79) (by norm_num) (by decide) ⟨-40, by norm_num⟩]; norm_num
  · rw [den_of (e := 5) (p := 11) (by norm_num) (by decide) ⟨5, by norm_num⟩]; norm_num

theorem main_proof :
    (∀ n : ℕ, 6 < n → a n = 2500 * a (n - 4)) ∧
    ((1 - PowerSeries.C 50 * PowerSeries.X ^ 2) *
      (1 + PowerSeries.C 50 * PowerSeries.X ^ 2)) * series =
        1 + PowerSeries.C 10 * PowerSeries.X + PowerSeries.C 25 * PowerSeries.X ^ 2 +
          PowerSeries.C 500 * PowerSeries.X ^ 3 - PowerSeries.C 31250 * PowerSeries.X ^ 6 := by
  obtain ⟨v0, v1, v2, v3, v4, v5, v6⟩ := vals
  refine ⟨?_, ?_⟩
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    rw [show m + 4 - 4 = m by omega]
    exact rec4 m (by omega)
  · have hc : (C (50 : ℚ)) ^ 2 = C 2500 := by rw [← map_pow]; norm_num
    have hl : (1 - C (50 : ℚ) * X ^ 2) * (1 + C 50 * X ^ 2) * series =
        series - C (2500 : ℚ) * (series * X ^ 4) := by
      rw [← hc]; ring
    rw [hl]
    ext n
    simp only [map_sub, map_add, coeff_C_mul, coeff_mul_X_pow', coeff_C_mul_X_pow, coeff_X,
      coeff_one, series, coeff_mk]
    rcases Nat.lt_or_ge n 7 with hn | hn
    · interval_cases n <;> simp [v0, v1, v2, v3, v4, v5, v6] <;> norm_num
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
      have hr := rec4 m (by omega)
      have c4 : 4 ≤ m + 4 := by omega
      have d0 : m + 4 ≠ 0 := by omega
      have d1 : m + 4 ≠ 1 := by omega
      have d2 : m + 4 ≠ 2 := by omega
      have d3 : m + 4 ≠ 3 := by omega
      have d6 : m + 4 ≠ 6 := by omega
      simp only [c4, d0, d1, d2, d3, d6, if_true, if_false, Nat.add_sub_cancel, hr, coeff_C]
      push_cast
      split_ifs <;> first | omega | ring

end OMA.P124870

theorem OMA.solution : type_of% @OMA.S_oeis_a124870.main := OMA.P124870.main_proof
