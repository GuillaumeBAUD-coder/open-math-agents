import OMAStatements.S_oeis_a059133
import Mathlib

/-
A059133: a(n) is the sum of W(k) for 1 <= k < 2^(n+1), where W(k) = 6 v_2(k) + 4. Closed form
a(n) = 4 (5 * 2^n - 4) - 6 n, the recurrence and the generating function.

- v_add: v_2(m + 2^k) = v_2(m) when 2^k does not divide m.
- V: the sum of v_2(k) for 1 <= k < 2^N is 2^N - N - 1, by induction on N: the range splits into
  1..2^N - 1, the single number 2^N, and 2^N + 1..2^(N+1) - 1, where v_2(2^N + k) = v_2(k).
- key: hence the sum of W is 10 * 2^N - 6 N - 10.
The recurrence follows from the closed form, and the generating function identity is checked
coefficient by coefficient.
-/

namespace OMA.P059133

lemma v_add {k m : ℕ} (h0 : m ≠ 0) (h : ¬ 2 ^ k ∣ m) :
    padicValNat 2 (m + 2 ^ k) = padicValNat 2 m := by
  obtain ⟨a, b, hb, rfl⟩ := Nat.exists_eq_two_pow_mul_odd h0
  have hak : a < k := by
    by_contra hc
    exact h (Dvd.dvd.mul_right (pow_dvd_pow 2 (not_lt.1 hc)) b)
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hak
  have e : 2 ^ a * b + 2 ^ (a + d + 1) = 2 ^ a * (b + 2 * 2 ^ d) := by ring
  have h2 : ¬ 2 ∣ b := hb.not_two_dvd_nat
  rw [e, padicValNat.mul (by positivity) (by positivity), padicValNat.mul (by positivity) hb.pos.ne',
    padicValNat.eq_zero_of_not_dvd h2, padicValNat.eq_zero_of_not_dvd (n := b + 2 * 2 ^ d)]
  omega

lemma V (N : ℕ) : ∑ i ∈ Finset.range (2 ^ N - 1), padicValNat 2 (i + 1) + N + 1 = 2 ^ N := by
  induction N with
  | zero => simp
  | succ N ih =>
    obtain ⟨M, hM⟩ : ∃ M, 2 ^ N = M + 1 :=
      ⟨2 ^ N - 1, by have := Nat.one_le_two_pow (n := N); omega⟩
    have e : 2 ^ (N + 1) - 1 = (M + 1) + M := by
      rw [pow_succ, hM]
      omega
    rw [hM, Nat.add_sub_cancel] at ih
    have h2 : ∀ i ∈ Finset.range M, padicValNat 2 (M + 1 + i + 1) = padicValNat 2 (i + 1) := by
      intro i hi
      have hi' := Finset.mem_range.1 hi
      have e' : M + 1 + i + 1 = (i + 1) + 2 ^ N := by
        rw [hM]
        ring
      rw [e']
      exact v_add (by omega) fun hd => by
        have := Nat.le_of_dvd (by omega) hd
        omega
    have h3 : padicValNat 2 (M + 1) = N := by
      rw [← hM]
      simp
    rw [e, Finset.sum_range_add, Finset.sum_range_succ, Finset.sum_congr rfl h2, h3, pow_succ, hM]
    omega

lemma key (W : ℕ → ℕ) (hW : ∀ k, W k = 6 * padicValNat 2 k + 4) (N : ℕ) :
    ∑ i ∈ Finset.range (2 ^ N - 1), W (i + 1) + 6 * N + 10 = 10 * 2 ^ N := by
  have h := V N
  have h1 := Nat.one_le_two_pow (n := N)
  simp only [hW, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range,
    smul_eq_mul]
  omega

lemma main' (W : ℕ → ℕ)
    (hW : ∀ k, W k = ([2 * (padicValNat 2 k + 1) - 1, 2 * (padicValNat 2 k + 1),
      2 * (padicValNat 2 k + 1) - 1] : List ℕ).sum)
    (a : ℕ → ℕ) (ha : ∀ n, a n = ∑ i ∈ Finset.range (2 ^ (n + 1) - 1), W (i + 1)) :
    (∀ n : ℕ, (a n : ℤ) = 4 * (-4 + 5 * 2 ^ n) - 6 * n) ∧
    (∀ n : ℕ, 2 < n → (a n : ℤ) = 4 * a (n - 1) - 5 * a (n - 2) + 2 * a (n - 3)) ∧
    ((PowerSeries.X - 1) ^ 2 * (2 * PowerSeries.X - 1) * PowerSeries.mk (fun n => (a n : ℤ)) =
      -2 * (PowerSeries.X + 2)) := by
  have hW' : ∀ k, W k = 6 * padicValNat 2 k + 4 := fun k => by
    rw [hW]
    simp only [List.sum_cons, List.sum_nil]
    omega
  have hcl : ∀ n : ℕ, (a n : ℤ) = 4 * (-4 + 5 * 2 ^ n) - 6 * n := by
    intro n
    have h := key W hW' (n + 1)
    rw [← ha] at h
    have hz : (a n : ℤ) + 6 * ((n : ℤ) + 1) + 10 = 10 * 2 ^ (n + 1) := by exact_mod_cast h
    rw [pow_succ] at hz
    linarith
  refine ⟨hcl, ?_, ?_⟩
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
    rw [show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega,
      show m + 3 - 3 = m by omega, hcl, hcl, hcl, hcl]
    push_cast
    ring
  · have e2 : (PowerSeries.C (2 : ℤ) : PowerSeries ℤ) = 2 := map_ofNat _ 2
    have e4 : (PowerSeries.C (4 : ℤ) : PowerSeries ℤ) = 4 := map_ofNat _ 4
    have e5 : (PowerSeries.C (5 : ℤ) : PowerSeries ℤ) = 5 := map_ofNat _ 5
    have key2 : (PowerSeries.X - 1) ^ 2 * (2 * PowerSeries.X - 1) *
        PowerSeries.mk (fun n => (a n : ℤ)) =
        PowerSeries.C (2 : ℤ) * (PowerSeries.mk (fun n => (a n : ℤ)) * PowerSeries.X ^ 3) -
          PowerSeries.C (5 : ℤ) * (PowerSeries.mk (fun n => (a n : ℤ)) * PowerSeries.X ^ 2) +
          PowerSeries.C (4 : ℤ) * (PowerSeries.mk (fun n => (a n : ℤ)) * PowerSeries.X ^ 1) -
          PowerSeries.mk (fun n => (a n : ℤ)) := by
      rw [e2, e4, e5]
      ring
    have rhs : (-2 * (PowerSeries.X + 2) : PowerSeries ℤ) =
        -(PowerSeries.C (2 : ℤ) * ((1 : PowerSeries ℤ) * PowerSeries.X ^ 1)) -
          PowerSeries.C (4 : ℤ) := by
      rw [e2, e4]
      ring
    rw [key2, rhs]
    ext n
    simp only [map_add, map_sub, map_neg, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow',
      PowerSeries.coeff_mk, PowerSeries.coeff_C, PowerSeries.coeff_one]
    have h0 := hcl 0
    have h1 := hcl 1
    have h2 := hcl 2
    norm_num at h0 h1 h2
    rcases n with _ | _ | _ | k
    · simp [h0]
    · simp [h0, h1]
    · simp [h0, h1, h2]
    · have c1 : 1 ≤ k + 1 + 1 + 1 := by omega
      have c2 : 2 ≤ k + 1 + 1 + 1 := by omega
      have c3 : 3 ≤ k + 1 + 1 + 1 := by omega
      have c4 : ¬ (k + 1 + 1 + 1 = 0) := by omega
      have c5 : ¬ (k + 2 = 0) := by omega
      have e1 : k + 1 + 1 + 1 - 1 = k + 2 := by omega
      have e2' : k + 1 + 1 + 1 - 2 = k + 1 := by omega
      have e3 : k + 1 + 1 + 1 - 3 = k := by omega
      simp only [if_pos c1, if_pos c2, if_pos c3, if_neg c4, if_neg c5, e1, e2', e3]
      rw [hcl, hcl, hcl, hcl]
      push_cast
      ring

end OMA.P059133

theorem OMA.solution : type_of% @OMA.S_oeis_a059133.main :=
  OMA.P059133.main' OMA.S_oeis_a059133.W2c (fun _ => rfl) OMA.S_oeis_a059133.a (fun _ => rfl)
