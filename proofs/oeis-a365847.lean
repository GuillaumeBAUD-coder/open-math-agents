import OMAStatements.S_oeis_a365847
import Mathlib

namespace OMA.P_oeis_a365847

private theorem main_proved :
    ∀ (A B : PowerSeries ℚ),
      (PowerSeries.X * A) * (1 - PowerSeries.X * A) ^ 4 =
        PowerSeries.X * (1 + PowerSeries.X * A) ^ 4 →
      B = 1 + PowerSeries.X * B ^ 4 + PowerSeries.X * B ^ 5 →
      A = B ^ 4 := by
  intro A B hA hB
  -- Step 1: Show F := X * B^4 satisfies the same equation F * (1 - F)^4 = X * (1 + F)^4!
  have hB_rel : B * (1 - PowerSeries.X * B ^ 4) = 1 + PowerSeries.X * B ^ 4 := by
    calc B * (1 - PowerSeries.X * B ^ 4) = B - PowerSeries.X * B ^ 5 := by ring
      _ = 1 + PowerSeries.X * B ^ 4 := by linear_combination hB
  have hB4_eq : (PowerSeries.X * B ^ 4) * (1 - PowerSeries.X * B ^ 4) ^ 4 =
      PowerSeries.X * (1 + PowerSeries.X * B ^ 4) ^ 4 := by
    have h4 := congr_arg (· ^ 4) hB_rel
    rw [mul_pow] at h4
    calc (PowerSeries.X * B ^ 4) * (1 - PowerSeries.X * B ^ 4) ^ 4
        = PowerSeries.X * (B ^ 4 * (1 - PowerSeries.X * B ^ 4) ^ 4) := by ring
      _ = PowerSeries.X * (1 + PowerSeries.X * B ^ 4) ^ 4 := by rw [h4]
  -- Step 2: Cancel X from both equations: A * (1 - X*A)^4 = (1 + X*A)^4 and B^4 * (1 - X*B^4)^4 = (1 + X*B^4)^4!
  have hcancel_X : ∀ F G : PowerSeries ℚ, PowerSeries.X * F = PowerSeries.X * G → F = G := by
    intro F G h
    ext n
    have hn := congr_arg (PowerSeries.coeff (n + 1)) h
    rwa [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_succ_X_mul] at hn
  have hA' : A * (1 - PowerSeries.X * A) ^ 4 = (1 + PowerSeries.X * A) ^ 4 :=
    hcancel_X _ _ (by rw [← mul_assoc]; exact hA)
  have hB4' : B ^ 4 * (1 - PowerSeries.X * B ^ 4) ^ 4 = (1 + PowerSeries.X * B ^ 4) ^ 4 :=
    hcancel_X _ _ (by rw [← mul_assoc]; exact hB4_eq)
  -- Step 3: Uniqueness by strong induction on n: coeff n A = coeff n (B^4)!
  -- Note: A = (1 + X*A)^4 - A * ((1 - X*A)^4 - 1) = 1 + X * P(X, A)!
  have hrec : ∀ F : PowerSeries ℚ,
      F * (1 - PowerSeries.X * F) ^ 4 = (1 + PowerSeries.X * F) ^ 4 →
      F = 1 + PowerSeries.X * (4 * F + 4 * F ^ 2 + 6 * PowerSeries.X * F ^ 2 - 6 * PowerSeries.X * F ^ 3 +
        4 * PowerSeries.X ^ 2 * F ^ 3 + 4 * PowerSeries.X ^ 2 * F ^ 4 +
        PowerSeries.X ^ 3 * F ^ 4 - PowerSeries.X ^ 3 * F ^ 5) := by
    intro F hF
    linear_combination hF
  have hA_rec := hrec A hA'
  have hB_rec := hrec (B ^ 4) hB4'
  ext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hpow_agree : ∀ (r m : ℕ), m < n →
        PowerSeries.coeff m (A ^ r) = PowerSeries.coeff m ((B ^ 4) ^ r) := by
      intro r
      induction r with
      | zero => intro m _; simp
      | succ r ihr =>
        intro m hm
        rw [pow_succ, pow_succ, PowerSeries.coeff_mul, PowerSeries.coeff_mul,
          Finset.Nat.sum_antidiagonal_eq_sum_range_succ
            (f := fun i j => PowerSeries.coeff i (A ^ r) * PowerSeries.coeff j A),
          Finset.Nat.sum_antidiagonal_eq_sum_range_succ
            (f := fun i j => PowerSeries.coeff i ((B ^ 4) ^ r) * PowerSeries.coeff j (B ^ 4))]
        refine Finset.sum_congr rfl fun k hk => ?_
        have hkm : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        rw [ihr k (by omega), ih (m - k) (by omega)]
    have hXpow_agree : ∀ (s r m : ℕ), m < n →
        PowerSeries.coeff m (PowerSeries.X ^ s * A ^ r) =
        PowerSeries.coeff m (PowerSeries.X ^ s * (B ^ 4) ^ r) := by
      intro s r m hm
      rw [PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow_mul']
      split_ifs with hsm
      · exact hpow_agree r (m - s) (by omega)
      · rfl
    cases n with
    | zero =>
      rw [hA_rec, hB_rec]
      simp [PowerSeries.coeff_zero_eq_constantCoeff]
    | succ m =>
      rw [hA_rec, hB_rec]
      simp only [map_add, PowerSeries.coeff_succ_X_mul]
      congr 1
      have hterm : ∀ (c : ℚ) (s r : ℕ),
          PowerSeries.coeff m (PowerSeries.C c * (PowerSeries.X ^ s * A ^ r)) =
          PowerSeries.coeff m (PowerSeries.C c * (PowerSeries.X ^ s * (B ^ 4) ^ r)) := by
        intro c s r
        rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul, hXpow_agree s r m (Nat.lt_succ_self m)]
      have hC : ∀ (k : ℕ) (F : PowerSeries ℚ), (k : PowerSeries ℚ) * F = PowerSeries.C (k : ℚ) * F := by
        intro k F; rw [map_natCast]
      have h1 : 4 * A + 4 * A ^ 2 + 6 * PowerSeries.X * A ^ 2 - 6 * PowerSeries.X * A ^ 3 +
          4 * PowerSeries.X ^ 2 * A ^ 3 + 4 * PowerSeries.X ^ 2 * A ^ 4 +
          PowerSeries.X ^ 3 * A ^ 4 - PowerSeries.X ^ 3 * A ^ 5 =
          PowerSeries.C (4 : ℚ) * (PowerSeries.X ^ 0 * A ^ 1) +
          PowerSeries.C (4 : ℚ) * (PowerSeries.X ^ 0 * A ^ 2) +
          PowerSeries.C (6 : ℚ) * (PowerSeries.X ^ 1 * A ^ 2) -
          PowerSeries.C (6 : ℚ) * (PowerSeries.X ^ 1 * A ^ 3) +
          PowerSeries.C (4 : ℚ) * (PowerSeries.X ^ 2 * A ^ 3) +
          PowerSeries.C (4 : ℚ) * (PowerSeries.X ^ 2 * A ^ 4) +
          PowerSeries.C (1 : ℚ) * (PowerSeries.X ^ 3 * A ^ 4) -
          PowerSeries.C (1 : ℚ) * (PowerSeries.X ^ 3 * A ^ 5) := by
        simp only [pow_zero, pow_one, one_mul, map_one,
          show PowerSeries.C (6 : ℚ) = 6 from map_ofNat _ 6,
          show PowerSeries.C (4 : ℚ) = 4 from map_ofNat _ 4]
        ring
      have h2 : 4 * B ^ 4 + 4 * (B ^ 4) ^ 2 + 6 * PowerSeries.X * (B ^ 4) ^ 2 - 6 * PowerSeries.X * (B ^ 4) ^ 3 +
          4 * PowerSeries.X ^ 2 * (B ^ 4) ^ 3 + 4 * PowerSeries.X ^ 2 * (B ^ 4) ^ 4 +
          PowerSeries.X ^ 3 * (B ^ 4) ^ 4 - PowerSeries.X ^ 3 * (B ^ 4) ^ 5 =
          PowerSeries.C (4 : ℚ) * (PowerSeries.X ^ 0 * (B ^ 4) ^ 1) +
          PowerSeries.C (4 : ℚ) * (PowerSeries.X ^ 0 * (B ^ 4) ^ 2) +
          PowerSeries.C (6 : ℚ) * (PowerSeries.X ^ 1 * (B ^ 4) ^ 2) -
          PowerSeries.C (6 : ℚ) * (PowerSeries.X ^ 1 * (B ^ 4) ^ 3) +
          PowerSeries.C (4 : ℚ) * (PowerSeries.X ^ 2 * (B ^ 4) ^ 3) +
          PowerSeries.C (4 : ℚ) * (PowerSeries.X ^ 2 * (B ^ 4) ^ 4) +
          PowerSeries.C (1 : ℚ) * (PowerSeries.X ^ 3 * (B ^ 4) ^ 4) -
          PowerSeries.C (1 : ℚ) * (PowerSeries.X ^ 3 * (B ^ 4) ^ 5) := by
        simp only [pow_zero, pow_one, one_mul, map_one,
          show PowerSeries.C (6 : ℚ) = 6 from map_ofNat _ 6,
          show PowerSeries.C (4 : ℚ) = 4 from map_ofNat _ 4]
        ring
      rw [h1, h2]
      simp only [map_add, map_sub]
      rw [hterm 4 0 1, hterm 4 0 2, hterm 6 1 2, hterm 6 1 3, hterm 4 2 3, hterm 4 2 4, hterm 1 3 4, hterm 1 3 5]

end OMA.P_oeis_a365847

theorem OMA.solution : type_of% @OMA.S_oeis_a365847.main :=
  OMA.P_oeis_a365847.main_proved
