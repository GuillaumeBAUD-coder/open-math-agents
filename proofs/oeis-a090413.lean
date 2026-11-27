import OMAStatements.S_oeis_a090413

/-!
Proof of OEIS A090413: the generating function satisfies
(3*X - 8*X^2)*S^2 + (1 - 6*X)*S - 1 = 0, whose radical Q satisfies Q^2 = 1 + 4*X^2.
Differentiating via a self-contained dPs helper gives an exact
linear differential equation whose n-th coefficient is the claimed recurrence
for n >= 3.
-/

private noncomputable def dPs (f : PowerSeries ℚ) : PowerSeries ℚ :=
  PowerSeries.mk fun n => ((n + 1 : ℕ) : ℚ) * PowerSeries.coeff (n + 1) f

private lemma coeff_dPs (f : PowerSeries ℚ) (n : ℕ) :
    PowerSeries.coeff n (dPs f) = ((n + 1 : ℕ) : ℚ) * PowerSeries.coeff (n + 1) f := by
  simp [dPs]

private lemma dPs_C (c : ℚ) : dPs (PowerSeries.C c) = 0 := by
  ext n
  simp [coeff_dPs]

private lemma dPs_one : dPs (1 : PowerSeries ℚ) = 0 := by
  rw [← map_one PowerSeries.C]
  exact dPs_C 1

private lemma dPs_natCast (k : ℕ) : dPs (k : PowerSeries ℚ) = 0 := by
  rw [← map_natCast PowerSeries.C k]
  exact dPs_C (k : ℚ)

private lemma dPs_X : dPs (PowerSeries.X : PowerSeries ℚ) = 1 := by
  ext n
  simp only [coeff_dPs, PowerSeries.coeff_X, PowerSeries.coeff_one]
  cases n <;> simp

private lemma dPs_add (f g : PowerSeries ℚ) : dPs (f + g) = dPs f + dPs g := by
  ext n
  simp only [coeff_dPs, map_add]
  ring

private lemma dPs_sub (f g : PowerSeries ℚ) : dPs (f - g) = dPs f - dPs g := by
  ext n
  simp only [coeff_dPs, map_sub]
  ring

private lemma dPs_mul (f g : PowerSeries ℚ) : dPs (f * g) = dPs f * g + f * dPs g := by
  ext n
  rw [coeff_dPs, map_add, PowerSeries.coeff_mul, PowerSeries.coeff_mul, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => PowerSeries.coeff i f * PowerSeries.coeff j g) (n + 1),
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => PowerSeries.coeff i (dPs f) * PowerSeries.coeff j g) n,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => PowerSeries.coeff i f * PowerSeries.coeff j (dPs g)) n,
    Finset.mul_sum]
  have hsplit :
      ∑ k ∈ Finset.range (n + 2),
          ((n + 1 : ℕ) : ℚ) * (PowerSeries.coeff k f * PowerSeries.coeff (n + 1 - k) g) =
        ∑ k ∈ Finset.range (n + 2),
          (((k : ℚ) * PowerSeries.coeff k f) * PowerSeries.coeff (n + 1 - k) g +
            PowerSeries.coeff k f *
              (((n + 1 - k : ℕ) : ℚ) * PowerSeries.coeff (n + 1 - k) g)) := by
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk_le : k ≤ n + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hnat : (k : ℚ) + ((n + 1 - k : ℕ) : ℚ) = ((n + 1 : ℕ) : ℚ) := by
      exact_mod_cast Nat.add_sub_of_le hk_le
    rw [← hnat]
    ring
  rw [hsplit, Finset.sum_add_distrib]
  have h1 :
      ∑ k ∈ Finset.range (n + 2),
          ((k : ℚ) * PowerSeries.coeff k f) * PowerSeries.coeff (n + 1 - k) g =
        ∑ k ∈ Finset.range (n + 1), PowerSeries.coeff k (dPs f) * PowerSeries.coeff (n - k) g := by
    rw [Finset.sum_range_succ']
    simp only [Nat.cast_zero, zero_mul, add_zero]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [coeff_dPs, Nat.succ_sub_succ]
  have h2 :
      ∑ k ∈ Finset.range (n + 2),
          PowerSeries.coeff k f * (((n + 1 - k : ℕ) : ℚ) * PowerSeries.coeff (n + 1 - k) g) =
        ∑ k ∈ Finset.range (n + 1), PowerSeries.coeff k f * PowerSeries.coeff (n - k) (dPs g) := by
    rw [Finset.sum_range_succ]
    simp only [Nat.sub_self, Nat.cast_zero, zero_mul, mul_zero, add_zero]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk_le : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    rw [coeff_dPs, Nat.sub_add_comm hk_le]
  rw [h1, h2]

private lemma dPs_sq (f : PowerSeries ℚ) : dPs (f ^ 2) = 2 * f * dPs f := by
  rw [pow_two, dPs_mul]
  ring

open PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a090413.main := by
  have hsub : HasSubst (-(X : PowerSeries ℚ) ^ 2) :=
    HasSubst.of_constantCoeff_zero' (by simp)
  have hcatQ : (catalanSeries.map (Nat.castRingHom ℚ)) ^ 2 * X + 1 =
      catalanSeries.map (Nat.castRingHom ℚ) := by
    have h := congrArg (PowerSeries.map (Nat.castRingHom ℚ)) catalanSeries_sq_mul_X_add_one
    simpa [PowerSeries.map_X] using h
  have hcat : OMA.S_oeis_a090413.catNeg ^ 2 * (-(X : PowerSeries ℚ) ^ 2) + 1 =
      OMA.S_oeis_a090413.catNeg := by
    have h := congrArg (substAlgHom hsub) hcatQ
    rw [map_add, map_mul, map_pow, map_one, substAlgHom_X] at h
    simpa [coe_substAlgHom, OMA.S_oeis_a090413.catNeg] using h
  have hcc : constantCoeff (1 - 3 * (X : PowerSeries ℚ) * OMA.S_oeis_a090413.catNeg) ≠ 0 := by
    simp
  have hrel : OMA.S_oeis_a090413.series *
      (1 - 3 * (X : PowerSeries ℚ) * OMA.S_oeis_a090413.catNeg) =
      OMA.S_oeis_a090413.catNeg :=
    (PowerSeries.eq_mul_inv_iff_mul_eq hcc).mp rfl
  let S := OMA.S_oeis_a090413.series
  have hU : (1 + 3 * X * S) * OMA.S_oeis_a090413.catNeg = S := by
    linear_combination -hrel
  have hU2 : (1 + 3 * X * S) ^ 2 * OMA.S_oeis_a090413.catNeg ^ 2 = S ^ 2 := by
    rw [← mul_pow, hU]
  have hquad : (3 * X - 8 * X ^ 2) * S ^ 2 + (1 - 6 * X) * S - 1 = 0 := by
    have hmul := congrArg ((1 + 3 * X * S) ^ 2 * ·) hcat
    have h1 : (1 + 3 * X * S) ^ 2 * (OMA.S_oeis_a090413.catNeg ^ 2 * (-X ^ 2) + 1) =
        ((1 + 3 * X * S) ^ 2 * OMA.S_oeis_a090413.catNeg ^ 2) * (-X ^ 2) + (1 + 3 * X * S) ^ 2 := by
      ring
    have h2 : (1 + 3 * X * S) ^ 2 * OMA.S_oeis_a090413.catNeg =
        (1 + 3 * X * S) * ((1 + 3 * X * S) * OMA.S_oeis_a090413.catNeg) := by
      ring
    rw [h1, hU2, h2, hU] at hmul
    linear_combination -hmul
  let Q : PowerSeries ℚ := (6 * X - 16 * X ^ 2) * S + (1 - 6 * X)
  have hQ2 : Q ^ 2 = 1 + 4 * X ^ 2 := by
    dsimp [Q]
    linear_combination 4 * (3 * X - 8 * X ^ 2) * hquad
  have hd3X : dPs (3 * (X : PowerSeries ℚ)) = 3 := by
    rw [dPs_mul, ← Nat.cast_ofNat, dPs_natCast, dPs_X, Nat.cast_ofNat]
    ring
  have hd6X : dPs (6 * (X : PowerSeries ℚ)) = 6 := by
    rw [dPs_mul, ← Nat.cast_ofNat, dPs_natCast, dPs_X, Nat.cast_ofNat]
    ring
  have hd4X2 : dPs (4 * (X : PowerSeries ℚ) ^ 2) = 8 * X := by
    rw [dPs_mul, ← Nat.cast_ofNat, dPs_natCast, dPs_sq, dPs_X, Nat.cast_ofNat]
    ring
  have hd8X2 : dPs (8 * (X : PowerSeries ℚ) ^ 2) = 16 * X := by
    rw [dPs_mul, ← Nat.cast_ofNat, dPs_natCast, dPs_sq, dPs_X, Nat.cast_ofNat]
    ring
  have hd16X2 : dPs (16 * (X : PowerSeries ℚ) ^ 2) = 32 * X := by
    rw [dPs_mul, ← Nat.cast_ofNat, dPs_natCast, dPs_sq, dPs_X, Nat.cast_ofNat]
    ring
  have hdQ2 : Q * dPs Q = 4 * (X : PowerSeries ℚ) := by
    have h := congrArg dPs hQ2
    have hrhs : dPs (1 + 4 * (X : PowerSeries ℚ) ^ 2) = 8 * X := by
      rw [dPs_add, dPs_one, zero_add, hd4X2]
    rw [dPs_sq, hrhs] at h
    have h' := congrArg (C (1 / 2 : ℚ) * ·) h
    have hc2 : C (1 / 2 : ℚ) * (2 : PowerSeries ℚ) = 1 := by
      rw [← show (1 : PowerSeries ℚ) + 1 = 2 by norm_num, mul_add, mul_one,
        ← map_add, show (1 / 2 : ℚ) + 1 / 2 = 1 by norm_num, map_one]
    have hc8 : C (1 / 2 : ℚ) * (8 : PowerSeries ℚ) = 4 := by
      rw [show (8 : PowerSeries ℚ) = 4 * 2 by ring, ← mul_assoc,
        mul_comm (C (1 / 2 : ℚ)) 4, mul_assoc, hc2, mul_one]
    linear_combination h' - Q * dPs Q * hc2 + X * hc8
  have hdQ : dPs Q = (6 - 32 * X) * S + (6 * X - 16 * X ^ 2) * dPs S - 6 := by
    dsimp [Q]
    rw [dPs_add, dPs_mul, dPs_sub, hd6X, hd16X2, dPs_sub, dPs_one, hd6X]
    ring
  let L : PowerSeries ℚ :=
    dPs ((3 * X - 8 * X ^ 2) * S) + X ^ 3 * (12 * dPs S - 32 * dPs (X * S))
  have hL_eq : L = (3 - 16 * X - 32 * X ^ 3) * S +
      (3 * X - 8 * X ^ 2) * (1 + 4 * X ^ 2) * dPs S := by
    dsimp [L]
    rw [dPs_mul, dPs_sub, hd3X, hd8X2, dPs_mul, dPs_X]
    ring
  have h2L : 2 * L = 2 * (3 + 2 * X) := by
    dsimp [Q] at hdQ2 hQ2
    linear_combination 2 * hL_eq - (1 + 4 * X ^ 2) * hdQ -
      dPs Q * hQ2 + ((6 * X - 16 * X ^ 2) * S + (1 - 6 * X)) * hdQ2
  intro n hn
  have hC2 : (2 : PowerSeries ℚ) = C (2 : ℚ) := by
    rw [← Nat.cast_ofNat, ← map_natCast C, Nat.cast_ofNat]
  have hC3 : (3 : PowerSeries ℚ) = C (3 : ℚ) := by
    rw [← Nat.cast_ofNat, ← map_natCast C, Nat.cast_ofNat]
  have hC8 : (8 : PowerSeries ℚ) = C (8 : ℚ) := by
    rw [← Nat.cast_ofNat, ← map_natCast C, Nat.cast_ofNat]
  have hC12 : (12 : PowerSeries ℚ) = C (12 : ℚ) := by
    rw [← Nat.cast_ofNat, ← map_natCast C, Nat.cast_ofNat]
  have hC32 : (32 : PowerSeries ℚ) = C (32 : ℚ) := by
    rw [← Nat.cast_ofNat, ← map_natCast C, Nat.cast_ofNat]
  have hcoeff : coeff n (2 * L) = coeff n (2 * (3 + 2 * (X : PowerSeries ℚ))) :=
    congrArg (coeff n) h2L
  have hrhs : coeff n (C (2 : ℚ) * (3 + C (2 : ℚ) * (X : PowerSeries ℚ))) =
      2 * (coeff n (3 : PowerSeries ℚ) + 2 * coeff n X) := by
    rw [coeff_C_mul, map_add, coeff_C_mul]
  rw [hC2, coeff_C_mul, hrhs] at hcoeff
  have hc3 : coeff n (3 : PowerSeries ℚ) = 0 := by
    rw [hC3, coeff_C]
    by_cases h : n = 0
    · exfalso; omega
    · simp only [h, ↓reduceIte]
  have hcX : coeff n (X : PowerSeries ℚ) = 0 := by
    rw [coeff_X]
    by_cases h : n = 1
    · exfalso; omega
    · simp only [h, ↓reduceIte]
  rw [hc3, hcX] at hcoeff
  have hLn : coeff n L = 0 := by linarith
  dsimp [L] at hLn
  rw [map_add, coeff_dPs] at hLn
  have hc1 : coeff (n + 1) ((3 * X - 8 * X ^ 2) * S) =
      3 * OMA.S_oeis_a090413.term n - 8 * OMA.S_oeis_a090413.term (n - 1) := by
    rw [sub_mul, map_sub, mul_assoc, mul_assoc, hC3, hC8, coeff_C_mul, coeff_C_mul,
      coeff_succ_X_mul]
    obtain ⟨k, hk⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    rw [show X ^ 2 * S = X * (X * S) by ring, hk, coeff_succ_X_mul, coeff_succ_X_mul]
    rfl
  have hc2 : coeff n (X ^ 3 * (12 * dPs S - 32 * dPs (X * S))) =
      12 * ((n : ℚ) - 2) * OMA.S_oeis_a090413.term (n - 2) +
        32 * (2 - (n : ℚ)) * OMA.S_oeis_a090413.term (n - 3) := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
    rw [coeff_X_pow_mul, map_sub, hC12, hC32, coeff_C_mul, coeff_C_mul,
      coeff_dPs, coeff_dPs, coeff_succ_X_mul]
    simp only [OMA.S_oeis_a090413.term, S, show m + 3 - 2 = m + 1 by omega,
      show m + 3 - 3 = m by omega]
    push_cast
    ring
  rw [hc1, hc2] at hLn
  push_cast at hLn
  linear_combination hLn
