import OMAStatements.S_oeis_a323695
import Mathlib

/-!
OEIS A323695: a(m) is odd exactly when m = k (k + 2).

Reduce the coefficients modulo 2. The n-th summand S_n satisfies
  S_n * (1 + x^(n+1))^(n+1) = x^n * (1 - x^(n+1))^n,
and modulo 2 this gives S_n * (1 + x^(n+1)) = x^n, because 1 - y = 1 + y there and power series
over the field with two elements have no zero divisors. Hence, modulo 2, the coefficient of x^j
in S_n is 1 if n + 1 divides j + 1 and 0 otherwise. Summing over n ≤ m, a(m) is congruent
modulo 2 to the number of divisors of m + 1, which is odd exactly when m + 1 is a square
(pair each divisor d with (m + 1) / d). Finally m + 1 = (k + 1)^2 means m = k (k + 2).
-/

namespace OMA.A323695

open OMA.S_oeis_a323695 PowerSeries

lemma summand_mul (n : ℕ) :
    summand n * (1 + X ^ (n + 1)) ^ (n + 1) = (X : PowerSeries ℤ) ^ n * (1 - X ^ (n + 1)) ^ n := by
  have hu : IsUnit ((1 + (X : PowerSeries ℤ) ^ (n + 1)) ^ (n + 1)) := by
    apply IsUnit.pow
    rw [PowerSeries.isUnit_iff_constantCoeff]
    simp
  unfold summand
  rw [mul_assoc, Ring.inverse_mul_cancel _ hu, mul_one]

lemma T_mul (n : ℕ) :
    PowerSeries.map (Int.castRingHom (ZMod 2)) (summand n) * (1 + X ^ (n + 1)) = X ^ n := by
  have h := congrArg (PowerSeries.map (Int.castRingHom (ZMod 2))) (summand_mul n)
  simp only [map_mul, map_pow, map_add, map_sub, map_one, PowerSeries.map_X] at h
  have hneg : (1 - (X : PowerSeries (ZMod 2)) ^ (n + 1)) = 1 + X ^ (n + 1) := by
    ext j
    simp only [map_sub, map_add]
    rw [sub_eq_add_neg, ZMod.neg_eq_self_mod_two]
  rw [hneg, pow_succ, ← mul_assoc] at h
  have hne : ((1 : PowerSeries (ZMod 2)) + X ^ (n + 1)) ^ n ≠ 0 := by
    apply pow_ne_zero
    intro h0
    have h1 := congrArg (PowerSeries.constantCoeff) h0
    simp at h1
  apply mul_right_cancel₀ hne
  rw [← h]
  ring

lemma coeff_T (n j : ℕ) :
    coeff j (PowerSeries.map (Int.castRingHom (ZMod 2)) (summand n)) =
      if (n + 1) ∣ (j + 1) then 1 else 0 := by
  have hrec : ∀ i, coeff i (PowerSeries.map (Int.castRingHom (ZMod 2)) (summand n)) +
      (if n + 1 ≤ i then
        coeff (i - (n + 1)) (PowerSeries.map (Int.castRingHom (ZMod 2)) (summand n)) else 0) =
      if i = n then 1 else 0 := by
    intro i
    have h := congrArg (coeff i) (T_mul n)
    rw [mul_add, mul_one, map_add, coeff_mul_X_pow', coeff_X_pow] at h
    exact h
  have hz : ∀ x : ZMod 2, x + 1 = 0 → x = 1 := by decide
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    have h := hrec j
    by_cases hj : n + 1 ≤ j
    · rw [if_pos hj, ih (j - (n + 1)) (by omega)] at h
      have hdvd : (n + 1 ∣ j - (n + 1) + 1) ↔ (n + 1 ∣ j + 1) := by
        have e : j + 1 = (j - (n + 1) + 1) + (n + 1) := by omega
        rw [e]
        exact Nat.dvd_add_self_right.symm
      have hjn : j ≠ n := by omega
      rw [if_neg hjn] at h
      by_cases hd : n + 1 ∣ j + 1
      · rw [if_pos hd]
        rw [if_pos (hdvd.mpr hd)] at h
        exact hz _ h
      · rw [if_neg hd]
        rw [if_neg (fun h' => hd (hdvd.mp h')), add_zero] at h
        exact h
    · rw [if_neg hj, add_zero] at h
      rw [h]
      by_cases hjn : j = n
      · subst hjn
        simp
      · rw [if_neg hjn, if_neg]
        intro hd
        have hle := Nat.le_of_dvd (by omega) hd
        omega

lemma card_divisors_mod2 (N : ℕ) (hN : 0 < N) :
    (∑ _d ∈ N.divisors, (1 : ZMod 2)) = if IsSquare N then 1 else 0 := by
  rw [← Finset.sum_filter_add_sum_filter_not N.divisors (fun d => d * d = N)]
  have h2 : ∑ _d ∈ N.divisors.filter (fun d => ¬ d * d = N), (1 : ZMod 2) = 0 := by
    apply Finset.sum_involution (fun d _ => N / d)
    · intro d hd
      decide
    · intro d hd _ h
      rw [Finset.mem_filter, Nat.mem_divisors] at hd
      apply hd.2
      have := Nat.mul_div_cancel' hd.1.1
      rw [h] at this
      exact this
    · intro d hd
      rw [Finset.mem_filter, Nat.mem_divisors] at hd ⊢
      refine ⟨⟨Nat.div_dvd_of_dvd hd.1.1, hd.1.2⟩, ?_⟩
      intro hsq
      apply hd.2
      have hmul := Nat.mul_div_cancel' hd.1.1
      have hpos : 0 < N / d := by
        rcases Nat.eq_zero_or_pos (N / d) with h0 | h0
        · rw [h0] at hsq
          omega
        · exact h0
      have hdd : d = N / d := by
        apply Nat.eq_of_mul_eq_mul_right hpos
        rw [hmul, hsq]
      rw [← hdd] at hmul
      exact hmul
    · intro d hd
      rw [Finset.mem_filter, Nat.mem_divisors] at hd
      exact Nat.div_div_self hd.1.1 hd.1.2
  rw [h2, add_zero]
  by_cases hsq : IsSquare N
  · obtain ⟨r, rfl⟩ := hsq
    rw [if_pos ⟨r, rfl⟩]
    have hset : (r * r).divisors.filter (fun d => d * d = r * r) = {r} := by
      ext d
      simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_singleton]
      constructor
      · rintro ⟨-, h⟩
        exact Nat.mul_self_inj.mp h
      · rintro rfl
        exact ⟨⟨Dvd.intro _ rfl, hN.ne'⟩, rfl⟩
    rw [hset]
    simp
  · rw [if_neg hsq]
    have hset : N.divisors.filter (fun d => d * d = N) = ∅ := by
      ext d
      simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
      intro _ h
      exact hsq ⟨d, h.symm⟩
    rw [hset]
    simp

lemma cast_a (m : ℕ) : ((a m : ℤ) : ZMod 2) = if IsSquare (m + 1) then 1 else 0 := by
  unfold a
  have h1 : ((coeff m (∑ n ∈ Finset.range (m + 1), summand n) : ℤ) : ZMod 2) =
      coeff m (PowerSeries.map (Int.castRingHom (ZMod 2))
        (∑ n ∈ Finset.range (m + 1), summand n)) := by
    rw [PowerSeries.coeff_map]
    rfl
  rw [h1, map_sum, map_sum]
  simp only [coeff_T]
  rw [← card_divisors_mod2 (m + 1) (Nat.succ_pos m)]
  rw [Nat.divisors, Finset.sum_filter, Finset.sum_Ico_eq_sum_range]
  apply Finset.sum_congr
  · simp
  · intro n _
    simp [add_comm]

end OMA.A323695

open OMA.S_oeis_a323695 OMA.A323695 in
theorem OMA.solution : type_of% @OMA.S_oeis_a323695.main := by
  intro m
  rw [← ZMod.intCast_eq_one_iff_odd, cast_a]
  constructor
  · intro h
    by_cases hsq : IsSquare (m + 1)
    · obtain ⟨r, hr⟩ := hsq
      have hr1 : 1 ≤ r := by
        rcases Nat.eq_zero_or_pos r with h0 | h0
        · subst h0
          simp at hr
        · exact h0
      obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
      refine ⟨k, ?_⟩
      have e : (k + 1) * (k + 1) = k * (k + 2) + 1 := by ring
      omega
    · rw [if_neg hsq] at h
      exact absurd h (by decide)
  · rintro ⟨k, rfl⟩
    rw [if_pos]
    exact ⟨k + 1, by ring⟩
