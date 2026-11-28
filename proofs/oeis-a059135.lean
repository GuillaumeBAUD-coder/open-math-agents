import OMAStatements.S_oeis_a059135

-- Problem: OEIS A059135, Barker's conjectures (closed form, recurrence, g.f.).
-- The k-th collapsed phrase sums to 7h + 4 with h = 3 v_2(k) + 1, i.e. 21 v_2(k) + 11. Summing over
-- k = 1..N gives 11 N + 21 v_2(N!), and by Legendre v_2(N!) = N - s_2(N). For N = 2^(n+1) - 1 the
-- binary digit sum is n + 1, so a(n) = 32 * 2^(n+1) - 21 n - 53. The recurrence and the g.f.
-- follow from the closed form.

namespace OMA.A059135
open OMA.S_oeis_a059135

theorem collapsed_eq (k : ℕ) : collapsed k = 21 * padicValNat 2 k + 11 := by
  simp only [collapsed, phrase, base, ruler, List.sum_cons, List.sum_nil]
  omega

theorem sum_val (N : ℕ) :
    ∑ k ∈ Finset.range N, padicValNat 2 (k + 1) = padicValNat 2 N.factorial := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, Nat.factorial_succ,
      padicValNat.mul (Nat.succ_ne_zero N) (Nat.factorial_ne_zero N)]
    ring

theorem digit_sum (m : ℕ) : (Nat.digits 2 (2 ^ m - 1)).sum = m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hpos : 0 < 2 ^ (m + 1) - 1 := by
      have := Nat.one_lt_two_pow (Nat.succ_ne_zero m); omega
    rw [Nat.digits_def' (by norm_num) hpos]
    have h1 : (2 ^ (m + 1) - 1) % 2 = 1 := by
      have := Nat.one_le_two_pow (n := m); rw [pow_succ]; omega
    have h2 : (2 ^ (m + 1) - 1) / 2 = 2 ^ m - 1 := by
      have := Nat.one_le_two_pow (n := m); rw [pow_succ]; omega
    rw [h1, h2, List.sum_cons, ih]; ring

theorem closed (n : ℕ) : (a n : ℤ) = -53 + 2 ^ (6 + n) - 21 * n := by
  have hs : a n = 11 * (2 ^ (n + 1) - 1) + 21 * padicValNat 2 (2 ^ (n + 1) - 1).factorial := by
    simp only [a, collapsed_eq, Finset.sum_add_distrib, ← Finset.mul_sum, sum_val,
      Finset.sum_const, Finset.card_range, smul_eq_mul]
    ring
  have hl := sub_one_mul_padicValNat_factorial (p := 2) (2 ^ (n + 1) - 1)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [digit_sum] at hl
  simp only [show 2 - 1 = 1 from rfl, one_mul] at hl
  have hlt : n + 1 < 2 ^ (n + 1) := Nat.lt_two_pow_self
  obtain ⟨t, ht⟩ : ∃ t, 2 ^ (n + 1) = t + n + 2 := ⟨2 ^ (n + 1) - n - 2, by omega⟩
  rw [hs, hl, ht, show t + n + 2 - 1 = t + n + 1 by omega, show t + n + 1 - (n + 1) = t by omega]
  have h2 : (2 : ℤ) ^ (n + 1) = t + n + 2 := by exact_mod_cast ht
  have : (2 : ℤ) ^ (6 + n) = 32 * 2 ^ (n + 1) := by
    rw [show 6 + n = 5 + (n + 1) by ring, pow_add]; norm_num
  rw [this, h2]
  push_cast
  ring

end OMA.A059135

open PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a059135.main := by
  have hc := OMA.A059135.closed
  have hrec : ∀ n : ℕ, 3 ≤ n → (OMA.S_oeis_a059135.a n : ℤ) =
      4 * OMA.S_oeis_a059135.a (n - 1) - 5 * OMA.S_oeis_a059135.a (n - 2) +
        2 * OMA.S_oeis_a059135.a (n - 3) := by
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
    rw [hc, show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega,
      show m + 3 - 3 = m by omega, hc, hc, hc]
    push_cast
    ring
  refine ⟨hc, hrec, ?_⟩
  have hq : ∀ n : ℕ, (OMA.S_oeis_a059135.a n : ℚ) = ((OMA.S_oeis_a059135.a n : ℤ) : ℚ) := by
    intro n; push_cast; rfl
  have hco : ∀ (f : PowerSeries ℚ) (c : ℚ) (k n : ℕ),
      coeff n (f * (C c * X ^ k)) = if k ≤ n then c * coeff (n - k) f else 0 := by
    intro f c k n
    rw [show f * (C c * X ^ k) = f * X ^ k * C c by ring, coeff_mul_C, coeff_mul_X_pow']
    split_ifs <;> simp [mul_comm]
  have hpoly : ((X : PowerSeries ℚ) - 1) ^ 2 * (2 * X - 1) =
      C 2 * X ^ 3 + C (-5) * X ^ 2 + C 4 * X ^ 1 + C (-1) * X ^ 0 := by
    simp only [map_ofNat, map_neg, map_one]; ring
  have hrhs : -(10 * (X : PowerSeries ℚ) + 11) = C (-10) * X ^ 1 + C (-11) * X ^ 0 := by
    simp only [map_neg, map_ofNat]; ring
  have v : ∀ n, (OMA.S_oeis_a059135.a n : ℚ) = -53 + 2 ^ (6 + n) - 21 * n := by
    intro n; rw [hq, hc]; push_cast; ring
  rw [hpoly, hrhs]
  ext n
  simp only [mul_add, map_add, coeff_mk, coeff_C_mul_X_pow, hco]
  rcases n with _ | _ | _ | m
  · simp [v]; norm_num
  · simp [v]; norm_num
  · simp [v]; norm_num
  · simp only [show 3 ≤ m + 3 by omega, show 2 ≤ m + 3 by omega, show 1 ≤ m + 3 by omega,
      show 0 ≤ m + 3 by omega, if_true, show m + 3 ≠ 1 by omega, show m + 3 ≠ 0 by omega, if_false,
      Nat.sub_zero]
    rw [show m + 3 - 3 = m by omega, show m + 3 - 2 = m + 1 by omega, show m + 3 - 1 = m + 2 by omega]
    simp only [v]
    push_cast
    ring
