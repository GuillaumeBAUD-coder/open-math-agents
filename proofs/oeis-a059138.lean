import OMAStatements.S_oeis_a059138

-- Credit: @Dariusthedoggie
-- Proof: collapsed2(k) = 36*v_2(k) + 18 and the sum of 2-adic valuations over 1..2^n-1 is 2^n - 1 - n, yielding the closed form, recurrence, and generating function

namespace OMA.P059138

open OMA.S_oeis_a059138 PowerSeries

private lemma collapsed2_eq (k : ℕ) : collapsed2 k = 36 * padicValNat 2 k + 18 := by
  unfold collapsed2 element ruler
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  omega

private lemma padicValNat_two_pow_add (m j : ℕ) (hj1 : 1 ≤ j) (hj2 : j < 2 ^ m) :
    padicValNat 2 (2 ^ m + j) = padicValNat 2 j := by
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hlt : padicValNat 2 j < m := by
    by_contra hge
    have hge' : m ≤ padicValNat 2 j := Nat.le_of_not_lt hge
    have hdvd : 2 ^ m ∣ j := (padicValNat_dvd_iff_le (by omega)).2 hge'
    have hle : 2 ^ m ≤ j := Nat.le_of_dvd (by omega) hdvd
    omega
  apply le_antisymm
  · by_contra hgt
    have hle : padicValNat 2 j + 1 ≤ padicValNat 2 (2 ^ m + j) := by omega
    have hdvd_sum : 2 ^ (padicValNat 2 j + 1) ∣ 2 ^ m + j :=
      (padicValNat_dvd_iff_le (by omega)).2 hle
    have hdvd_pow : 2 ^ (padicValNat 2 j + 1) ∣ 2 ^ m :=
      pow_dvd_pow 2 (by omega)
    have hdvd_j : 2 ^ (padicValNat 2 j + 1) ∣ j :=
      (Nat.dvd_add_right hdvd_pow).1 hdvd_sum
    have hcontra : padicValNat 2 j + 1 ≤ padicValNat 2 j :=
      (padicValNat_dvd_iff_le (by omega)).1 hdvd_j
    omega
  · have hdvd_j : 2 ^ padicValNat 2 j ∣ j :=
      (padicValNat_dvd_iff_le (by omega)).2 (le_refl _)
    have hdvd_pow : 2 ^ padicValNat 2 j ∣ 2 ^ m :=
      pow_dvd_pow 2 (by omega)
    have hdvd_sum : 2 ^ padicValNat 2 j ∣ 2 ^ m + j := dvd_add hdvd_pow hdvd_j
    exact (padicValNat_dvd_iff_le (by omega)).1 hdvd_sum

private lemma sum_padicValNat_two (n : ℕ) :
    ∑ k ∈ Finset.range (2 ^ n - 1), padicValNat 2 (k + 1) = 2 ^ n - 1 - n := by
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  induction n with
  | zero => simp
  | succ m ih =>
    have hpow_pos : 1 ≤ 2 ^ m := Nat.one_le_pow m 2 (by omega)
    have hpow_ge : m + 1 ≤ 2 ^ m := by
      clear ih
      induction m with
      | zero => norm_num
      | succ t iht =>
        have : 2 ^ (t + 1) = 2 ^ t + 2 ^ t := by ring
        have : 1 ≤ 2 ^ t := Nat.one_le_pow t 2 (by omega)
        omega
    have hsplit1 : 2 ^ (m + 1) - 1 = (2 ^ m - 1) + 2 ^ m := by
      have : 2 ^ (m + 1) = 2 ^ m + 2 ^ m := by ring
      omega
    rw [hsplit1, Finset.sum_range_add, ih]
    have hsum2 : ∑ x ∈ Finset.range (2 ^ m), padicValNat 2 (2 ^ m - 1 + x + 1) =
        ∑ x ∈ Finset.range 1, padicValNat 2 (2 ^ m - 1 + x + 1) +
        ∑ x ∈ Finset.range (2 ^ m - 1), padicValNat 2 (2 ^ m - 1 + (1 + x) + 1) := by
      have h := Finset.sum_range_add (fun x => padicValNat 2 (2 ^ m - 1 + x + 1)) 1 (2 ^ m - 1)
      have h1 : 1 + (2 ^ m - 1) = 2 ^ m := by omega
      rw [h1] at h
      exact h
    rw [hsum2]
    have hmid : ∑ x ∈ Finset.range 1, padicValNat 2 (2 ^ m - 1 + x + 1) = m := by
      simp only [Finset.sum_range_one, add_zero]
      have h1 : 2 ^ m - 1 + 1 = 2 ^ m := by omega
      rw [h1, padicValNat.prime_pow]
    have hright : ∑ x ∈ Finset.range (2 ^ m - 1), padicValNat 2 (2 ^ m - 1 + (1 + x) + 1) =
        ∑ x ∈ Finset.range (2 ^ m - 1), padicValNat 2 (x + 1) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.mem_range] at hx
      have h1 : 2 ^ m - 1 + (1 + x) + 1 = 2 ^ m + (x + 1) := by omega
      rw [h1]
      exact padicValNat_two_pow_add m (x + 1) (by omega) (by omega)
    rw [hmid, hright, ih]
    have : 2 ^ (m + 1) = 2 ^ m + 2 ^ m := by ring
    omega

private lemma a_closed (n : ℕ) : (a n : ℤ) = 18 * (-5 + 3 * 2 ^ (1 + n) - 2 * n) := by
  have hnat : a n = 36 * (2 ^ (n + 1) - 1 - (n + 1)) + 18 * (2 ^ (n + 1) - 1) := by
    unfold a
    have hcongr : ∑ k ∈ Finset.range (2 ^ (n + 1) - 1), collapsed2 (k + 1) =
        ∑ k ∈ Finset.range (2 ^ (n + 1) - 1), (36 * padicValNat 2 (k + 1) + 18) := by
      apply Finset.sum_congr rfl
      intro k _
      exact collapsed2_eq (k + 1)
    rw [hcongr, Finset.sum_add_distrib, ← Finset.mul_sum, sum_padicValNat_two]
    simp [mul_comm]
  have hge : n + 1 ≤ 2 ^ (n + 1) - 1 := by
    have h1 : n + 2 ≤ 2 ^ (n + 1) := by
      clear hnat; induction n with
      | zero => norm_num
      | succ k ih =>
        have h2 : 2 ^ (k + 1 + 1) = 2 ^ (k + 1) + 2 ^ (k + 1) := by ring
        have h3 : 1 ≤ 2 ^ (k + 1) := Nat.one_le_pow (k + 1) 2 (by omega)
        omega
    omega
  have hpos : 1 ≤ 2 ^ (n + 1) := Nat.one_le_pow (n + 1) 2 (by omega)
  rw [hnat]
  have hpow : (2 : ℤ) ^ (1 + n) = (2 : ℤ) ^ (n + 1) := by ring_nf
  rw [hpow]
  push_cast [Nat.cast_sub hge, Nat.cast_sub hpos]
  ring

private lemma a_rec (n : ℕ) (hn : 3 ≤ n) :
    (a n : ℤ) = 4 * a (n - 1) - 5 * a (n - 2) + 2 * a (n - 3) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  have h1 : k + 3 - 1 = k + 2 := by omega
  have h2 : k + 3 - 2 = k + 1 := by omega
  have h3 : k + 3 - 3 = k := by omega
  rw [h1, h2, h3, a_closed, a_closed, a_closed, a_closed]
  push_cast
  have hp1 : (2 : ℤ) ^ (1 + (k + 1)) = 2 * 2 ^ (1 + k) := by rw [show 1 + (k + 1) = (1 + k) + 1 by omega, pow_succ]; ring
  have hp2 : (2 : ℤ) ^ (1 + (k + 2)) = 4 * 2 ^ (1 + k) := by rw [show 1 + (k + 2) = (1 + k) + 2 by omega, pow_add]; ring
  have hp3 : (2 : ℤ) ^ (1 + (k + 3)) = 8 * 2 ^ (1 + k) := by rw [show 1 + (k + 3) = (1 + k) + 3 by omega, pow_add]; ring
  rw [hp1, hp2, hp3]
  ring

theorem main_proof :
    (∀ n : ℕ, (a n : ℤ) = 18 * (-5 + 3 * 2 ^ (1 + n) - 2 * n)) ∧
    (∀ n : ℕ, 3 ≤ n → (a n : ℤ) = 4 * a (n - 1) - 5 * a (n - 2) + 2 * a (n - 3)) ∧
    PowerSeries.mk (fun n => (a n : ℚ)) * ((X - 1) ^ 2 * (2 * X - 1)) = -18 * (X + 1) := by
  refine ⟨a_closed, a_rec, ?_⟩
  have hden : (((X - 1) ^ 2 * (2 * X - 1)) : ℚ⟦X⟧) =
      -1 + 4 * X - 5 * X ^ 2 + 2 * X ^ 3 := by ring
  rw [hden]
  ext n
  set F : ℚ⟦X⟧ := PowerSeries.mk (fun k => (a k : ℚ))
  have hcoeff_lhs : coeff n (F * (-1 + 4 * X - 5 * X ^ 2 + 2 * X ^ 3)) =
      -coeff n F + 4 * (if 1 ≤ n then coeff (n - 1) F else 0) -
        5 * (if 2 ≤ n then coeff (n - 2) F else 0) +
        2 * (if 3 ≤ n then coeff (n - 3) F else 0) := by
    have hexp : F * (-1 + 4 * X - 5 * X ^ 2 + 2 * X ^ 3) =
        -F + C 4 * (F * X ^ 1) - C 5 * (F * X ^ 2) + C 2 * (F * X ^ 3) := by
      simp [map_ofNat]; ring
    rw [hexp, map_add, map_sub, map_add, map_neg,
        coeff_C_mul, coeff_C_mul, coeff_C_mul,
        PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mul_X_pow']
  have hcoeff_rhs : coeff n (-18 * (X + 1) : ℚ⟦X⟧) =
      if n = 0 then -18 else if n = 1 then -18 else 0 := by
    have hexp : (-18 * (X + 1) : ℚ⟦X⟧) = C (-18) + C (-18) * X := by
      simp [map_neg, map_ofNat]; ring
    rw [hexp, map_add, coeff_C, coeff_C_mul, coeff_X]
    rcases n with _ | _ | k <;> simp
  rw [hcoeff_lhs, hcoeff_rhs]
  simp only [F, PowerSeries.coeff_mk]
  have haq : ∀ m : ℕ, (a m : ℚ) = 18 * (-5 + 3 * (2 : ℚ) ^ (1 + m) - 2 * m) := by
    intro m
    have hz := a_closed m
    exact_mod_cast hz
  rcases n with _ | _ | _ | k
  · simp [haq 0]; norm_num
  · simp [haq 0, haq 1]; norm_num
  · simp [haq 0, haq 1, haq 2]; norm_num
  · have hrec := a_rec (k + 3) (by omega)
    have hrecq : (a (k + 3) : ℚ) = 4 * a (k + 2) - 5 * a (k + 1) + 2 * a k := by
      exact_mod_cast hrec
    have hk : k + 1 + 1 + 1 = k + 3 := by omega
    rw [hk]
    simp only [show 1 ≤ k + 3 by omega, show 2 ≤ k + 3 by omega, show 3 ≤ k + 3 by omega,
               ↓reduceIte, show k + 3 - 1 = k + 2 by omega, show k + 3 - 2 = k + 1 by omega,
               show k + 3 - 3 = k by omega, show k + 3 ≠ 0 by omega, show k + 3 ≠ 1 by omega]
    linarith

end OMA.P059138

theorem OMA.solution : type_of% @OMA.S_oeis_a059138.main := OMA.P059138.main_proof
