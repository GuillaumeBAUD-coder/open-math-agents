import OMAStatements.S_oeis_a055278

/-!
Proof of OEIS A055278: A055278 (n + 12) - A055278 n equals a cubic polynomial R n,
which is annihilated by (1 - X^2)*(1 - X^3)*(1 - X)^3. Thus the coefficient recurrence
above degree 8 is periodic with period 12 and vanishes after checking k = 0..11 and m = 0..7.
-/

private lemma A_add_twelve (n : ℕ) :
    OMA.S_oeis_a055278.A055278 (n + 12) =
      OMA.S_oeis_a055278.A055278 n + ((n : ℤ) ^ 3 + 13 * (n : ℤ) ^ 2 + 93 * (n : ℤ) + 241) := by
  unfold OMA.S_oeis_a055278.A055278
  have hpoly :
      3 * ((n + 12 : ℕ) : ℤ) ^ 4 - 20 * ((n + 12 : ℕ) : ℤ) ^ 3 +
          54 * ((n + 12 : ℕ) : ℤ) ^ 2 - 60 * ((n + 12 : ℕ) : ℤ) + 32 =
        (3 * (n : ℤ) ^ 4 - 20 * (n : ℤ) ^ 3 + 54 * (n : ℤ) ^ 2 - 60 * (n : ℤ) + 32) +
          ((n : ℤ) ^ 3 + 13 * (n : ℤ) ^ 2 + 93 * (n : ℤ) + 241) * 144 := by
    push_cast
    ring
  rw [hpoly, Int.add_mul_ediv_right _ _ (by decide)]

private def L_diff (k : ℕ) : ℤ :=
  OMA.S_oeis_a055278.A055278 (k + 12) - 3 * OMA.S_oeis_a055278.A055278 (k + 11) +
    2 * OMA.S_oeis_a055278.A055278 (k + 10) + OMA.S_oeis_a055278.A055278 (k + 9) -
    OMA.S_oeis_a055278.A055278 (k + 7) - 2 * OMA.S_oeis_a055278.A055278 (k + 6) +
    3 * OMA.S_oeis_a055278.A055278 (k + 5) - OMA.S_oeis_a055278.A055278 (k + 4)

private lemma L_diff_eq_zero (k : ℕ) : L_diff k = 0 := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases hk : k < 12
    · interval_cases k <;> norm_num [L_diff, OMA.S_oeis_a055278.A055278]
    · obtain ⟨m, rfl⟩ : ∃ m, k = m + 12 := ⟨k - 12, by omega⟩
      have hstep : L_diff (m + 12) = L_diff m := by
        unfold L_diff
        rw [show m + 12 + 12 = (m + 12) + 12 by rfl,
          show m + 12 + 11 = (m + 11) + 12 by omega,
          show m + 12 + 10 = (m + 10) + 12 by omega,
          show m + 12 + 9 = (m + 9) + 12 by omega,
          show m + 12 + 7 = (m + 7) + 12 by omega,
          show m + 12 + 6 = (m + 6) + 12 by omega,
          show m + 12 + 5 = (m + 5) + 12 by omega,
          show m + 12 + 4 = (m + 4) + 12 by omega]
        rw [A_add_twelve (m + 12), A_add_twelve (m + 11), A_add_twelve (m + 10),
          A_add_twelve (m + 9), A_add_twelve (m + 7), A_add_twelve (m + 6),
          A_add_twelve (m + 5), A_add_twelve (m + 4)]
        push_cast
        ring
      rw [hstep]
      exact ih m (by omega)

theorem OMA.solution : type_of% @OMA.S_oeis_a055278.main := by
  let F : PowerSeries ℤ := PowerSeries.mk fun n => OMA.S_oeis_a055278.A055278 (n + 4)
  let D : PowerSeries ℤ :=
    (1 - (PowerSeries.X : PowerSeries ℤ) ^ 2) *
      (1 - (PowerSeries.X : PowerSeries ℤ) ^ 3) *
      (1 - (PowerSeries.X : PowerSeries ℤ)) ^ 3
  have hZ : F * D = (PowerSeries.X : PowerSeries ℤ) ^ 3 + (PowerSeries.X : PowerSeries ℤ) ^ 2 + 1 := by
    have hC2 : (2 : PowerSeries ℤ) = PowerSeries.C (2 : ℤ) := by
      rw [← Nat.cast_ofNat, ← map_natCast (PowerSeries.C (R := ℤ)), Nat.cast_ofNat]
    have hC3 : (3 : PowerSeries ℤ) = PowerSeries.C (3 : ℤ) := by
      rw [← Nat.cast_ofNat, ← map_natCast (PowerSeries.C (R := ℤ)), Nat.cast_ofNat]
    have hFD : F * D = F - PowerSeries.C 3 * ((PowerSeries.X : PowerSeries ℤ) ^ 1 * F) +
        PowerSeries.C 2 * (PowerSeries.X ^ 2 * F) + PowerSeries.X ^ 3 * F - PowerSeries.X ^ 5 * F -
        PowerSeries.C 2 * (PowerSeries.X ^ 6 * F) + PowerSeries.C 3 * (PowerSeries.X ^ 7 * F) -
        PowerSeries.X ^ 8 * F := by
      dsimp [D]
      rw [← hC2, ← hC3]
      ring
    rw [hFD]
    ext m
    simp only [map_sub, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul',
      PowerSeries.coeff_X_pow, PowerSeries.coeff_one, PowerSeries.coeff_mk, F]
    rcases m with _ | _ | _ | _ | _ | _ | _ | _ | k
    · norm_num [OMA.S_oeis_a055278.A055278]
    · norm_num [OMA.S_oeis_a055278.A055278]
    · norm_num [OMA.S_oeis_a055278.A055278]
    · norm_num [OMA.S_oeis_a055278.A055278]
    · norm_num [OMA.S_oeis_a055278.A055278]
    · norm_num [OMA.S_oeis_a055278.A055278]
    · norm_num [OMA.S_oeis_a055278.A055278]
    · norm_num [OMA.S_oeis_a055278.A055278]
    · have h1 : 1 ≤ k + 8 := by omega
      have h2 : 2 ≤ k + 8 := by omega
      have h3 : 3 ≤ k + 8 := by omega
      have h5 : 5 ≤ k + 8 := by omega
      have h6 : 6 ≤ k + 8 := by omega
      have h7 : 7 ≤ k + 8 := by omega
      have h8 : 8 ≤ k + 8 := by omega
      have hne3 : k + 8 ≠ 3 := by omega
      have hne2 : k + 8 ≠ 2 := by omega
      have hne0 : k + 8 ≠ 0 := by omega
      simp only [h1, h2, h3, h5, h6, h7, h8, hne3, hne2, hne0, ↓reduceIte,
        show k + 8 - 1 + 4 = k + 11 by omega, show k + 8 - 2 + 4 = k + 10 by omega,
        show k + 8 - 3 + 4 = k + 9 by omega, show k + 8 - 5 + 4 = k + 7 by omega,
        show k + 8 - 6 + 4 = k + 6 by omega, show k + 8 - 7 + 4 = k + 5 by omega,
        show k + 8 - 8 + 4 = k + 4 by omega, show k + 8 + 4 = k + 12 by omega,
        add_zero]
      exact L_diff_eq_zero k
  have hQ := congrArg (PowerSeries.map (Int.castRingHom ℚ)) hZ
  have hFmap : F.map (Int.castRingHom ℚ) =
      PowerSeries.mk fun n => (OMA.S_oeis_a055278.A055278 (n + 4) : ℚ) := by
    ext n
    simp only [F, PowerSeries.coeff_map, PowerSeries.coeff_mk, Int.coe_castRingHom]
  have hDmap : D.map (Int.castRingHom ℚ) =
      (1 - (PowerSeries.X : PowerSeries ℚ) ^ 2) *
        (1 - (PowerSeries.X : PowerSeries ℚ) ^ 3) *
        (1 - (PowerSeries.X : PowerSeries ℚ)) ^ 3 := by
    dsimp [D]
    simp only [map_mul, map_pow, map_sub, map_one, PowerSeries.map_X]
  rw [map_mul, hFmap, hDmap] at hQ
  simpa only [map_add, map_pow, map_one, PowerSeries.map_X] using hQ
