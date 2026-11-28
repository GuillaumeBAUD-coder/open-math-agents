import OMAStatements.S_mo_481674

open PowerSeries

private def VanishesBelow (M : ℕ) (P : PowerSeries ℚ) : Prop :=
  ∀ k < M, coeff k P = 0

private lemma vanishesBelow_sub {M : ℕ} {P Q : PowerSeries ℚ}
    (hP : VanishesBelow M P) (hQ : VanishesBelow M Q) :
    VanishesBelow M (P - Q) := by
  intro k hk
  rw [map_sub, hP k hk, hQ k hk, sub_zero]

private lemma vanishesBelow_mul_right {M : ℕ} (P : PowerSeries ℚ) {Q : PowerSeries ℚ}
    (hQ : VanishesBelow M Q) :
    VanishesBelow M (P * Q) := by
  intro k hk
  rw [coeff_mul]
  apply Finset.sum_eq_zero
  intro p hp
  rw [Finset.mem_antidiagonal] at hp
  have h2 : p.2 < M := by omega
  rw [hQ p.2 h2, mul_zero]

private lemma vanishesBelow_pow {B : PowerSeries ℚ} (hB : B.constantCoeff = 0) :
    ∀ q : ℕ, VanishesBelow q (B ^ q) := by
  intro q
  induction q with
  | zero =>
    intro k hk
    exact absurd hk (Nat.not_lt_zero k)
  | succ q ih =>
    intro k hk
    rw [pow_succ', coeff_mul]
    apply Finset.sum_eq_zero
    intro p hp
    rw [Finset.mem_antidiagonal] at hp
    rcases Nat.eq_zero_or_pos p.1 with h1 | h1
    · rw [h1, coeff_zero_eq_constantCoeff_apply, hB, zero_mul]
    · have h2 : p.2 < q := by omega
      rw [ih p.2 h2, mul_zero]

private lemma vanishesBelow_derivative {M : ℕ} {P : PowerSeries ℚ}
    (hP : VanishesBelow (M + 1) P) :
    VanishesBelow M (derivative (R := ℚ) P) := by
  intro k hk
  rw [coeff_derivative, hP (k + 1) (by omega), zero_mul]

private lemma vanishesBelow_cancel_one_sub {B P : PowerSeries ℚ} {M : ℕ}
    (hB : B.constantCoeff = 0) (h : VanishesBelow M ((1 - B) * P)) :
    VanishesBelow M P := by
  intro k hk
  induction k using Nat.strong_induction_on with
  | h k ih =>
    have hk0 := h k hk
    rw [sub_mul, one_mul, map_sub, sub_eq_zero] at hk0
    have hBP : coeff k (B * P) = 0 := by
      rw [coeff_mul]
      apply Finset.sum_eq_zero
      intro p hp
      rw [Finset.mem_antidiagonal] at hp
      rcases Nat.eq_zero_or_pos p.1 with h1 | h1
      · rw [h1, coeff_zero_eq_constantCoeff_apply, hB, zero_mul]
      · have hp2 : p.2 < k := by omega
        rw [ih p.2 hp2 (by omega), mul_zero]
    rw [hk0, hBP]

private noncomputable def approxF (B : PowerSeries ℚ) (n M : ℕ) : PowerSeries ℚ :=
  (1 + B) * ∑ q ∈ Finset.range (M + 1), C (OMA.S_mo_481674.R n q : ℚ) * B ^ q

private lemma one_sub_mul_geom (B : PowerSeries ℚ) (M : ℕ) :
    (1 - B) * ∑ q ∈ Finset.range (M + 1), B ^ q = 1 - B ^ (M + 1) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    rw [pow_succ']
    ring

private lemma approxF_zero_diff (B : PowerSeries ℚ) (hB : B.constantCoeff = 0)
    (hODE : derivative (R := ℚ) B * (1 - B) = 1 + B) (M : ℕ) :
    VanishesBelow (M + 1) (derivative (R := ℚ) B - approxF B 0 M) := by
  apply vanishesBelow_cancel_one_sub hB
  have hsum : ∑ q ∈ Finset.range (M + 1), C (OMA.S_mo_481674.R 0 q : ℚ) * B ^ q =
      ∑ q ∈ Finset.range (M + 1), B ^ q := by
    apply Finset.sum_congr rfl
    intro q _
    simp [OMA.S_mo_481674.R]
  have h1 : (1 - B) * (derivative (R := ℚ) B - approxF B 0 M) =
      (1 + B) * B ^ (M + 1) := by
    unfold approxF
    rw [hsum, mul_sub]
    have hODE' : (1 - B) * derivative (R := ℚ) B = 1 + B := by
      rw [mul_comm]; exact hODE
    rw [hODE']
    have hmul : (1 - B) * ((1 + B) * ∑ q ∈ Finset.range (M + 1), B ^ q) =
        (1 + B) * ((1 - B) * ∑ q ∈ Finset.range (M + 1), B ^ q) := by ring
    rw [hmul, one_sub_mul_geom]
    ring
  rw [h1]
  exact vanishesBelow_mul_right (1 + B) (vanishesBelow_pow hB (M + 1))

private lemma derivative_sum_approx (B : PowerSeries ℚ) (n M : ℕ) :
    derivative (R := ℚ) (∑ q ∈ Finset.range (M + 2), C (OMA.S_mo_481674.R n q : ℚ) * B ^ q) =
      derivative (R := ℚ) B *
        ∑ q ∈ Finset.range (M + 1), C (((q + 1) * OMA.S_mo_481674.R n (q + 1) : ℕ) : ℚ) * B ^ q := by
  rw [map_sum]
  rw [Finset.sum_range_succ']
  simp only [pow_zero, mul_one, derivative_C, add_zero]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  rw [Derivation.leibniz, derivative_C, smul_zero, add_zero]
  rw [smul_eq_mul, derivative_pow]
  simp only [Nat.add_sub_cancel, Nat.cast_mul, Nat.cast_add, Nat.cast_one, map_mul, map_add,
    map_one, map_natCast]
  ring

private lemma diff_approx_identity (B : PowerSeries ℚ) (n M : ℕ) :
    ∑ q ∈ Finset.range (M + 2), C (OMA.S_mo_481674.R n q : ℚ) * B ^ q +
      (1 + B) * ∑ q ∈ Finset.range (M + 1),
        C (((q + 1) * OMA.S_mo_481674.R n (q + 1) : ℕ) : ℚ) * B ^ q -
      (1 - B) * ∑ q ∈ Finset.range (M + 1), C (OMA.S_mo_481674.R (n + 1) q : ℚ) * B ^ q =
    C ((OMA.S_mo_481674.R n (M + 1) + (M + 1) * OMA.S_mo_481674.R n (M + 1) +
        OMA.S_mo_481674.R (n + 1) M : ℕ) : ℚ) * B ^ (M + 1) := by
  induction M with
  | zero =>
    have hR0 : OMA.S_mo_481674.R (n + 1) 0 =
        OMA.S_mo_481674.R n 0 + OMA.S_mo_481674.R n 1 := by
      simp [OMA.S_mo_481674.R]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_one,
      mul_one, one_mul, Nat.cast_zero, Nat.cast_add, Nat.cast_mul, Nat.cast_one,
      map_zero, map_add, map_mul, map_one]
    rw [hR0]
    simp only [Nat.cast_add, map_add]
    ring
  | succ M ih =>
    have hR : OMA.S_mo_481674.R (n + 1) (M + 1) =
        OMA.S_mo_481674.R (n + 1) M +
          (M + 2) * (OMA.S_mo_481674.R n (M + 1) + OMA.S_mo_481674.R n (M + 2)) := by
      simp [OMA.S_mo_481674.R]
    have hs1 : ∑ q ∈ Finset.range (M + 3), C (OMA.S_mo_481674.R n q : ℚ) * B ^ q =
        ∑ q ∈ Finset.range (M + 2), C (OMA.S_mo_481674.R n q : ℚ) * B ^ q +
          C (OMA.S_mo_481674.R n (M + 2) : ℚ) * B ^ (M + 2) :=
      Finset.sum_range_succ _ (M + 2)
    have hs2 : ∑ q ∈ Finset.range (M + 2),
          C (((q + 1) * OMA.S_mo_481674.R n (q + 1) : ℕ) : ℚ) * B ^ q =
        ∑ q ∈ Finset.range (M + 1),
          C (((q + 1) * OMA.S_mo_481674.R n (q + 1) : ℕ) : ℚ) * B ^ q +
          C (((M + 2) * OMA.S_mo_481674.R n (M + 2) : ℕ) : ℚ) * B ^ (M + 1) :=
      Finset.sum_range_succ _ (M + 1)
    have hs3 : ∑ q ∈ Finset.range (M + 2), C (OMA.S_mo_481674.R (n + 1) q : ℚ) * B ^ q =
        ∑ q ∈ Finset.range (M + 1), C (OMA.S_mo_481674.R (n + 1) q : ℚ) * B ^ q +
          C (OMA.S_mo_481674.R (n + 1) (M + 1) : ℚ) * B ^ (M + 1) :=
      Finset.sum_range_succ _ (M + 1)
    change ∑ q ∈ Finset.range (M + 3), C (OMA.S_mo_481674.R n q : ℚ) * B ^ q +
        (1 + B) * ∑ q ∈ Finset.range (M + 2),
          C (((q + 1) * OMA.S_mo_481674.R n (q + 1) : ℕ) : ℚ) * B ^ q -
        (1 - B) * ∑ q ∈ Finset.range (M + 2), C (OMA.S_mo_481674.R (n + 1) q : ℚ) * B ^ q =
      C ((OMA.S_mo_481674.R n (M + 2) + (M + 2) * OMA.S_mo_481674.R n (M + 2) +
          OMA.S_mo_481674.R (n + 1) (M + 1) : ℕ) : ℚ) * B ^ (M + 2)
    rw [hs1, hs2, hs3]
    have h_rearrange :
        (∑ q ∈ Finset.range (M + 2), C (OMA.S_mo_481674.R n q : ℚ) * B ^ q +
            C (OMA.S_mo_481674.R n (M + 2) : ℚ) * B ^ (M + 2)) +
          (1 + B) * (∑ q ∈ Finset.range (M + 1),
              C (((q + 1) * OMA.S_mo_481674.R n (q + 1) : ℕ) : ℚ) * B ^ q +
            C (((M + 2) * OMA.S_mo_481674.R n (M + 2) : ℕ) : ℚ) * B ^ (M + 1)) -
          (1 - B) * (∑ q ∈ Finset.range (M + 1),
              C (OMA.S_mo_481674.R (n + 1) q : ℚ) * B ^ q +
            C (OMA.S_mo_481674.R (n + 1) (M + 1) : ℚ) * B ^ (M + 1)) =
        (∑ q ∈ Finset.range (M + 2), C (OMA.S_mo_481674.R n q : ℚ) * B ^ q +
            (1 + B) * ∑ q ∈ Finset.range (M + 1),
              C (((q + 1) * OMA.S_mo_481674.R n (q + 1) : ℕ) : ℚ) * B ^ q -
            (1 - B) * ∑ q ∈ Finset.range (M + 1),
              C (OMA.S_mo_481674.R (n + 1) q : ℚ) * B ^ q) +
          (C (OMA.S_mo_481674.R n (M + 2) : ℚ) * B ^ (M + 2) +
            (1 + B) * (C (((M + 2) * OMA.S_mo_481674.R n (M + 2) : ℕ) : ℚ) * B ^ (M + 1)) -
            (1 - B) * (C (OMA.S_mo_481674.R (n + 1) (M + 1) : ℚ) * B ^ (M + 1))) := by
      ring
    rw [h_rearrange, ih, hR]
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat,
      map_add, map_mul, map_one, map_ofNat]
    have hpow : B ^ (M + 2) = B ^ (M + 1) * B := pow_succ B (M + 1)
    rw [hpow]
    ring

private lemma approxF_succ_diff (B : PowerSeries ℚ) (hB : B.constantCoeff = 0)
    (hODE : derivative (R := ℚ) B * (1 - B) = 1 + B) (n M : ℕ) :
    VanishesBelow (M + 1) (derivative (R := ℚ) (approxF B n (M + 1)) - approxF B (n + 1) M) := by
  apply vanishesBelow_cancel_one_sub hB
  have hderiv : derivative (R := ℚ) (approxF B n (M + 1)) =
      derivative (R := ℚ) B * ∑ q ∈ Finset.range (M + 2), C (OMA.S_mo_481674.R n q : ℚ) * B ^ q +
        (1 + B) * (derivative (R := ℚ) B *
          ∑ q ∈ Finset.range (M + 1),
            C (((q + 1) * OMA.S_mo_481674.R n (q + 1) : ℕ) : ℚ) * B ^ q) := by
    unfold approxF
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    rw [map_add, derivative_one, zero_add]
    rw [derivative_sum_approx]
    ring
  have h1 : (1 - B) * (derivative (R := ℚ) (approxF B n (M + 1)) - approxF B (n + 1) M) =
      (1 + B) * (C ((OMA.S_mo_481674.R n (M + 1) + (M + 1) * OMA.S_mo_481674.R n (M + 1) +
        OMA.S_mo_481674.R (n + 1) M : ℕ) : ℚ) * B ^ (M + 1)) := by
    rw [hderiv]
    unfold approxF
    have hODE' : (1 - B) * derivative (R := ℚ) B = 1 + B := by
      rw [mul_comm]; exact hODE
    have h2 : (1 - B) * (derivative (R := ℚ) B *
          ∑ q ∈ Finset.range (M + 2), C (OMA.S_mo_481674.R n q : ℚ) * B ^ q +
        (1 + B) * (derivative (R := ℚ) B *
          ∑ q ∈ Finset.range (M + 1),
            C (((q + 1) * OMA.S_mo_481674.R n (q + 1) : ℕ) : ℚ) * B ^ q) -
        (1 + B) * ∑ q ∈ Finset.range (M + 1), C (OMA.S_mo_481674.R (n + 1) q : ℚ) * B ^ q) =
      (1 + B) * (∑ q ∈ Finset.range (M + 2), C (OMA.S_mo_481674.R n q : ℚ) * B ^ q +
        (1 + B) * ∑ q ∈ Finset.range (M + 1),
          C (((q + 1) * OMA.S_mo_481674.R n (q + 1) : ℕ) : ℚ) * B ^ q -
        (1 - B) * ∑ q ∈ Finset.range (M + 1), C (OMA.S_mo_481674.R (n + 1) q : ℚ) * B ^ q) := by
      calc (1 - B) * (derivative (R := ℚ) B *
              ∑ q ∈ Finset.range (M + 2), C (OMA.S_mo_481674.R n q : ℚ) * B ^ q +
            (1 + B) * (derivative (R := ℚ) B *
              ∑ q ∈ Finset.range (M + 1),
                C (((q + 1) * OMA.S_mo_481674.R n (q + 1) : ℕ) : ℚ) * B ^ q) -
            (1 + B) * ∑ q ∈ Finset.range (M + 1), C (OMA.S_mo_481674.R (n + 1) q : ℚ) * B ^ q)
          = ((1 - B) * derivative (R := ℚ) B) *
              ∑ q ∈ Finset.range (M + 2), C (OMA.S_mo_481674.R n q : ℚ) * B ^ q +
            (1 + B) * ((1 - B) * derivative (R := ℚ) B) *
              ∑ q ∈ Finset.range (M + 1),
                C (((q + 1) * OMA.S_mo_481674.R n (q + 1) : ℕ) : ℚ) * B ^ q -
            (1 + B) * ((1 - B) * ∑ q ∈ Finset.range (M + 1),
              C (OMA.S_mo_481674.R (n + 1) q : ℚ) * B ^ q) := by ring
        _ = (1 + B) *
              ∑ q ∈ Finset.range (M + 2), C (OMA.S_mo_481674.R n q : ℚ) * B ^ q +
            (1 + B) * (1 + B) *
              ∑ q ∈ Finset.range (M + 1),
                C (((q + 1) * OMA.S_mo_481674.R n (q + 1) : ℕ) : ℚ) * B ^ q -
            (1 + B) * ((1 - B) * ∑ q ∈ Finset.range (M + 1),
              C (OMA.S_mo_481674.R (n + 1) q : ℚ) * B ^ q) := by rw [hODE']
        _ = _ := by ring
    rw [h2, diff_approx_identity]
  rw [h1]
  exact vanishesBelow_mul_right (1 + B) (vanishesBelow_mul_right _ (vanishesBelow_pow hB (M + 1)))

private lemma approxF_main (B : PowerSeries ℚ) (hB : B.constantCoeff = 0)
    (hODE : derivative (R := ℚ) B * (1 - B) = 1 + B) :
    ∀ n M : ℕ, VanishesBelow (M + 1) ((derivative (R := ℚ))^[n + 1] B - approxF B n M) := by
  intro n
  induction n with
  | zero =>
    intro M
    simpa using approxF_zero_diff B hB hODE M
  | succ n ih =>
    intro M
    have h1 : VanishesBelow (M + 1)
        (derivative (R := ℚ) ((derivative (R := ℚ))^[n + 1] B - approxF B n (M + 1))) :=
      vanishesBelow_derivative (ih (M + 1))
    rw [map_sub, ← Function.iterate_succ_apply' (derivative (R := ℚ)) (n + 1) B] at h1
    have h2 : VanishesBelow (M + 1) (derivative (R := ℚ) (approxF B n (M + 1)) - approxF B (n + 1) M) :=
      approxF_succ_diff B hB hODE n M
    have h3 : (derivative (R := ℚ))^[n + 2] B - approxF B (n + 1) M =
        ((derivative (R := ℚ))^[n + 2] B - derivative (R := ℚ) (approxF B n (M + 1))) +
        (derivative (R := ℚ) (approxF B n (M + 1)) - approxF B (n + 1) M) := by ring
    rw [h3]
    intro k hk
    rw [map_add, h1 k hk, h2 k hk, add_zero]

theorem OMA.solution : type_of% @OMA.S_mo_481674.main := by
  intro B hB hODE n
  have h := approxF_main B hB hODE n 0 0 (by omega)
  rw [map_sub, sub_eq_zero] at h
  rw [coeff_zero_eq_constantCoeff_apply, constantCoeff_iterate_derivative] at h
  rw [h]
  unfold approxF
  have hsum : ∑ q ∈ Finset.range (0 + 1), C (OMA.S_mo_481674.R n q : ℚ) * B ^ q =
      C (OMA.S_mo_481674.R n 0 : ℚ) := by simp
  rw [hsum, coeff_mul_C, map_add, coeff_zero_one, coeff_zero_eq_constantCoeff_apply, hB, add_zero,
    one_mul]
