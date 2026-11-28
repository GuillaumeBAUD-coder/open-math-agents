import OMAStatements.S_oeis_a059135

-- Problem: A059135: A hierarchical sequence (S(W2{3}c) - see A059126).
-- Credit: @rtflynn
-- Proof idea: the k-th term depends only on v = padicValNat 2 k. Splitting 1..2N+1 into odd numbers
-- (v = 0) and 2j (v = 1 + v(j)) gives the sum over 1..2^m - 1 in closed form by induction on m;
-- the recurrence and the g.f. (comparing coefficients) follow from the closed form.

open PowerSeries OMA.S_oeis_a059135 in
theorem OMA.solution : type_of% @OMA.S_oeis_a059135.main := by
  have v_odd : ∀ j : ℕ, padicValNat 2 (2 * j + 1) = 0 := fun j =>
    padicValNat.eq_zero_of_not_dvd (by omega)
  have v_even : ∀ j : ℕ, padicValNat 2 (2 * (j + 1)) = padicValNat 2 (j + 1) + 1 := by
    intro j
    rw [padicValNat.mul (by norm_num) (by omega), padicValNat.self (by norm_num)]
    ring
  have split : ∀ (f : ℕ → ℚ) (N : ℕ),
      ∑ k ∈ Finset.range (2 * N + 1), f (padicValNat 2 (k + 1)) =
        ((N : ℚ) + 1) * f 0 + ∑ k ∈ Finset.range N, f (padicValNat 2 (k + 1) + 1) := by
    intro f N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [show 2 * (N + 1) + 1 = 2 * N + 1 + 1 + 1 by ring,
        Finset.sum_range_succ _ (2 * N + 1 + 1), Finset.sum_range_succ _ (2 * N + 1), ih,
        Finset.sum_range_succ _ N, show 2 * N + 1 + 1 = 2 * (N + 1) by ring, v_even N,
        v_odd (N + 1)]
      push_cast
      ring
  have hpow : ∀ m : ℕ, 2 ^ (m + 1) - 1 = 2 * (2 ^ m - 1) + 1 := by
    intro m
    have : 0 < 2 ^ m := by positivity
    rw [pow_succ]
    omega
  have hcast : ∀ m : ℕ, ((2 ^ m - 1 : ℕ) : ℚ) = 2 ^ m - 1 := by
    intro m
    have : 1 ≤ 2 ^ m := Nat.one_le_pow _ _ (by norm_num)
    rw [Nat.cast_sub this]
    push_cast
    ring
  have lin : ∀ (B A : ℚ) (m : ℕ),
      ∑ k ∈ Finset.range (2 ^ m - 1), (A + B * (padicValNat 2 (k + 1) : ℚ)) =
        A * (2 ^ m - 1) + B * (2 ^ m - m - 1) := by
    intro B A m
    induction m generalizing A with
    | zero => simp
    | succ m ih =>
      rw [hpow m, split (fun v => A + B * (v : ℚ)) (2 ^ m - 1)]
      have e : ∀ k : ℕ, A + B * ((padicValNat 2 (k + 1) + 1 : ℕ) : ℚ) =
          (A + B) + B * (padicValNat 2 (k + 1) : ℚ) := fun k => by push_cast; ring
      simp only [e]
      rw [ih (A + B), hcast m]
      push_cast
      ring
  have ha : ∀ n : ℕ, (a n : ℚ) = 64 * 2 ^ n - 21 * n - 53 := by
    intro n
    have e : (a n : ℚ) = ∑ k ∈ Finset.range (2 ^ (n + 1) - 1),
        ((11 : ℚ) + 21 * (padicValNat 2 (k + 1) : ℚ)) := by
      unfold a
      rw [Nat.cast_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [collapsed, phrase, base, ruler, Nat.add_sub_cancel, List.sum_cons, List.sum_nil]
      push_cast
      ring
    rw [e, lin]
    push_cast
    ring
  have hz : ∀ n : ℕ, (a n : ℤ) = -53 + 2 ^ (6 + n) - 21 * n := by
    intro n
    have h : ((a n : ℤ) : ℚ) = ((-53 + 2 ^ (6 + n) - 21 * n : ℤ) : ℚ) := by
      push_cast
      rw [ha]
      ring
    exact_mod_cast h
  refine ⟨hz, fun n hn => ?_, ?_⟩
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
    rw [show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega,
      show m + 3 - 3 = m by omega]
    simp only [hz]
    push_cast
    ring
  · have e : PowerSeries.mk (fun n => (a n : ℚ)) * ((X - 1) ^ 2 * (2 * X - 1)) =
        (C : ℚ →+* PowerSeries ℚ) 2 * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 3)
          - (C : ℚ →+* PowerSeries ℚ) 5 * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 2)
          + (C : ℚ →+* PowerSeries ℚ) 4 * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 1)
          - PowerSeries.mk (fun n => (a n : ℚ)) := by
      rw [map_ofNat (C : ℚ →+* PowerSeries ℚ) 2, map_ofNat (C : ℚ →+* PowerSeries ℚ) 5,
        map_ofNat (C : ℚ →+* PowerSeries ℚ) 4]
      ring
    have e2 : (-(10 * X + 11) : PowerSeries ℚ) =
        -((C : ℚ →+* PowerSeries ℚ) 10 * X ^ 1) - (C : ℚ →+* PowerSeries ℚ) 11 := by
      rw [map_ofNat (C : ℚ →+* PowerSeries ℚ) 10, map_ofNat (C : ℚ →+* PowerSeries ℚ) 11]
      ring
    rw [e, e2]
    ext m
    simp only [map_add, map_sub, map_neg, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow',
      PowerSeries.coeff_mk, PowerSeries.coeff_C]
    rcases Nat.lt_or_ge m 3 with hm | hm
    · interval_cases m <;> norm_num [ha]
    · obtain ⟨k, rfl⟩ : ∃ k, m = k + 3 := ⟨m - 3, by omega⟩
      rw [if_pos (show 3 ≤ k + 3 by omega), if_pos (show 2 ≤ k + 3 by omega),
        if_pos (show 1 ≤ k + 3 by omega), if_neg (show ¬ (k + 3 - 1 = 0) by omega),
        if_neg (show ¬ (k + 3 = 0) by omega), show k + 3 - 3 = k by omega,
        show k + 3 - 2 = k + 1 by omega, show k + 3 - 1 = k + 2 by omega]
      simp only [ha]
      push_cast
      ring

