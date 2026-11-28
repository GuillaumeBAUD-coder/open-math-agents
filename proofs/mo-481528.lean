import OMAStatements.S_mo_481528

namespace OMA.Mo481528Proof

open PowerSeries

private abbrev Rseq := OMA.S_mo_481528.R

private def a0Coeff : ℕ → ℚ
  | 0 => 1
  | n + 1 => (Rseq n 0 : ℚ) / ((n + 1).factorial : ℚ)

private noncomputable def A0 : PowerSeries ℚ :=
  PowerSeries.mk a0Coeff

private noncomputable def B0 : PowerSeries ℚ :=
  PowerSeries.derivative (R := ℚ) A0

private noncomputable def H (q : ℕ) : PowerSeries ℚ :=
  PowerSeries.mk fun n => (Rseq n q : ℚ) / (n.factorial : ℚ)

private lemma A0_constantCoeff : A0.constantCoeff = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [A0, a0Coeff]

private lemma coeff_B0 (n : ℕ) :
    PowerSeries.coeff n B0 = (Rseq n 0 : ℚ) / (n.factorial : ℚ) := by
  rw [B0, PowerSeries.coeff_derivative, A0, PowerSeries.coeff_mk, a0Coeff]
  have hfac : ((n + 1).factorial : ℚ) = ((n + 1 : ℕ) : ℚ) * (n.factorial : ℚ) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  have hn1 : ((n + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  rw [hfac]
  field_simp
  push_cast
  ring

private lemma H_zero_eq_B0 : H 0 = B0 := by
  ext n
  rw [H, PowerSeries.coeff_mk, coeff_B0]

private lemma H_zero_sub_X_mul_H_one : H 0 - PowerSeries.X * H 1 = A0 := by
  ext n
  cases n with
  | zero =>
    simp only [map_sub, PowerSeries.coeff_zero_X_mul, sub_zero, H, PowerSeries.coeff_mk,
      A0, a0Coeff, Nat.factorial_zero, Nat.cast_one, div_one]
    simp [Rseq, OMA.S_mo_481528.R]
  | succ n =>
    simp only [map_sub, PowerSeries.coeff_succ_X_mul, H, PowerSeries.coeff_mk, A0, a0Coeff]
    have hR : Rseq (n + 1) 0 = Rseq n 0 + (n + 1) * Rseq n 1 := by
      simp [Rseq, OMA.S_mo_481528.R]
    have hfac : ((n + 1).factorial : ℚ) = ((n + 1 : ℕ) : ℚ) * (n.factorial : ℚ) := by
      rw [Nat.factorial_succ]
      push_cast
      ring
    have hn1 : ((n + 1 : ℕ) : ℚ) ≠ 0 := by positivity
    have hnf : (n.factorial : ℚ) ≠ 0 := by positivity
    rw [hR]
    push_cast
    rw [hfac]
    field_simp
    push_cast
    ring

private lemma H_succ_sub_H (q : ℕ) :
    H (q + 1) - H q = PowerSeries.X * (H (q + 1) + H (q + 2)) := by
  ext n
  cases n with
  | zero =>
    simp only [map_sub, PowerSeries.coeff_zero_X_mul, H, PowerSeries.coeff_mk,
      Nat.factorial_zero, Nat.cast_one, div_one]
    simp [Rseq, OMA.S_mo_481528.R]
  | succ n =>
    simp only [map_sub, map_add, PowerSeries.coeff_succ_X_mul, H, PowerSeries.coeff_mk]
    have hR : Rseq (n + 1) (q + 1) =
        Rseq (n + 1) q + (n + 1) * (Rseq n (q + 1) + Rseq n (q + 2)) := by
      simp [Rseq, OMA.S_mo_481528.R]
    have hfac : ((n + 1).factorial : ℚ) = ((n + 1 : ℕ) : ℚ) * (n.factorial : ℚ) := by
      rw [Nat.factorial_succ]
      push_cast
      ring
    have hn1 : ((n + 1 : ℕ) : ℚ) ≠ 0 := by positivity
    have hnf : (n.factorial : ℚ) ≠ 0 := by positivity
    rw [hR]
    push_cast
    rw [hfac]
    field_simp
    push_cast
    ring

private def yCoeff : ℕ → ℚ
  | 0 => 0
  | n + 1 => (if n = 0 then 1 else 0) + yCoeff n +
      ∑ i : Fin n, yCoeff (i.1 + 1) * yCoeff (n - i.1)

private lemma yCoeff_zero : yCoeff 0 = 0 := by
  rw [yCoeff.eq_1]

private lemma yCoeff_succ (n : ℕ) :
    yCoeff (n + 1) = (if n = 0 then 1 else 0) + yCoeff n +
      ∑ i : Fin n, yCoeff (i.1 + 1) * yCoeff (n - i.1) := by
  rw [yCoeff.eq_2]

private noncomputable def Y0 : PowerSeries ℚ :=
  PowerSeries.mk yCoeff

private lemma Y0_constantCoeff : Y0.constantCoeff = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Y0, PowerSeries.coeff_mk, yCoeff_zero]

private lemma Y0_mul_eq_zero {Z : PowerSeries ℚ} (h : Y0 * Z = 0) : Z = 0 := by
  ext n
  rw [map_zero]
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hcoeff := congr_arg (PowerSeries.coeff (n + 1)) h
    rw [map_zero, PowerSeries.coeff_mul] at hcoeff
    have hmem : (1, n) ∈ Finset.antidiagonal (n + 1) := by
      rw [Finset.mem_antidiagonal]
      omega
    rw [← Finset.add_sum_erase _ _ hmem] at hcoeff
    have hrest :
        ∑ p ∈ (Finset.antidiagonal (n + 1)).erase (1, n),
          PowerSeries.coeff p.1 Y0 * PowerSeries.coeff p.2 Z = 0 := by
      refine Finset.sum_eq_zero fun p hp => ?_
      rw [Finset.mem_erase, Finset.mem_antidiagonal] at hp
      rcases hp with ⟨hne, hsum⟩
      by_cases hp1 : p.1 = 0
      · rw [hp1, PowerSeries.coeff_zero_eq_constantCoeff_apply, Y0_constantCoeff, zero_mul]
      · have hp1_ne1 : p.1 ≠ 1 := by
          intro h1
          have h2 : p.2 = n := by omega
          exact hne (Prod.ext h1 h2)
        have hp2 : p.2 < n := by omega
        rw [ih p.2 hp2, mul_zero]
    rw [hrest, add_zero] at hcoeff
    have h1 : PowerSeries.coeff 1 Y0 = 1 := by
      rw [Y0, PowerSeries.coeff_mk, yCoeff_succ 0]
      simp [yCoeff_zero]
    rwa [h1, one_mul] at hcoeff

private lemma Y0_eq : Y0 = PowerSeries.X + PowerSeries.X * Y0 + Y0 ^ 2 := by
  ext m
  cases m with
  | zero =>
    simp [Y0, yCoeff_zero, sq]
  | succ n =>
    simp only [map_add, PowerSeries.coeff_X, PowerSeries.coeff_succ_X_mul, sq]
    rw [PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => PowerSeries.coeff i Y0 * PowerSeries.coeff j Y0) (n + 1)]
    have hx : (if n + 1 = 1 then (1 : ℚ) else 0) = if n = 0 then 1 else 0 := by
      split_ifs with h1 h2 h2 <;> first | rfl | omega
    rw [hx]
    conv_lhs => rw [Y0, PowerSeries.coeff_mk, yCoeff_succ]
    have hy : PowerSeries.coeff n Y0 = yCoeff n := by
      rw [Y0, PowerSeries.coeff_mk]
    rw [hy]
    have hsum :
        ∑ k ∈ Finset.range (n + 2),
          PowerSeries.coeff k Y0 * PowerSeries.coeff (n + 1 - k) Y0 =
        ∑ i : Fin n, yCoeff (i.1 + 1) * yCoeff (n - i.1) := by
      simp only [Y0, PowerSeries.coeff_mk]
      rw [Finset.sum_range_succ, Nat.sub_self, yCoeff_zero, mul_zero, add_zero]
      cases n with
      | zero => simp [yCoeff_zero]
      | succ m =>
        rw [Finset.sum_range_succ', Nat.sub_zero, yCoeff_zero, zero_mul, add_zero]
        rw [Fin.sum_univ_eq_sum_range (fun i => yCoeff (i + 1) * yCoeff (m + 1 - i)) (m + 1)]
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [Finset.mem_range] at hi
        have hsub : m + 1 + 1 - (i + 1) = m + 1 - i := by omega
        rw [hsub]
    rw [hsum]

private lemma Y0_mul_one_sub : Y0 * (1 - Y0) = (1 + Y0) * PowerSeries.X := by
  calc
    Y0 * (1 - Y0) = Y0 - Y0 ^ 2 := by ring
    _ = (PowerSeries.X + PowerSeries.X * Y0 + Y0 ^ 2) - Y0 ^ 2 := by rw [← Y0_eq]
    _ = (1 + Y0) * PowerSeries.X := by ring

private lemma step_telescope (k : ℕ) (hk : 1 ≤ k) :
    Y0 * H (k - 1) - PowerSeries.X * H k =
      Y0 * (Y0 * H k - PowerSeries.X * H (k + 1)) := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le' hk
  simp only [Nat.add_sub_cancel]
  have hH : H q = H (q + 1) - PowerSeries.X * (H (q + 1) + H (q + 2)) := by
    rw [← H_succ_sub_H q]
    ring
  have hY2 : Y0 ^ 2 = Y0 - (1 + Y0) * PowerSeries.X := by
    have := Y0_mul_one_sub
    calc
      Y0 ^ 2 = Y0 - Y0 * (1 - Y0) := by ring
      _ = Y0 - (1 + Y0) * PowerSeries.X := by rw [this]
  calc
    Y0 * H q - PowerSeries.X * H (q + 1)
        = Y0 * (H (q + 1) - PowerSeries.X * (H (q + 1) + H (q + 2))) -
            PowerSeries.X * H (q + 1) := by rw [hH]
    _ = (Y0 - (1 + Y0) * PowerSeries.X) * H (q + 1) - Y0 * PowerSeries.X * H (q + 2) := by ring
    _ = Y0 ^ 2 * H (q + 1) - Y0 * PowerSeries.X * H (q + 2) := by rw [← hY2]
    _ = Y0 * (Y0 * H (q + 1) - PowerSeries.X * H (q + 1 + 1)) := by ring

private lemma mul_Y0_pow_eq (N : ℕ) (hN : 1 ≤ N) :
    Y0 * A0 - (1 + Y0) * PowerSeries.X * B0 =
      Y0 ^ N * (Y0 * H (N - 1) - PowerSeries.X * H N) := by
  induction N, hN using Nat.le_induction with
  | base =>
    simp only [Nat.sub_self, pow_one]
    have h0 := H_zero_eq_B0
    have h1 := H_zero_sub_X_mul_H_one
    have hY := Y0_mul_one_sub
    calc
      Y0 * A0 - (1 + Y0) * PowerSeries.X * B0
          = Y0 * (H 0 - PowerSeries.X * H 1) - (1 + Y0) * PowerSeries.X * H 0 := by
            rw [h1, h0]
      _ = (Y0 - (1 + Y0) * PowerSeries.X) * H 0 - Y0 * PowerSeries.X * H 1 := by ring
      _ = (Y0 - Y0 * (1 - Y0)) * H 0 - Y0 * PowerSeries.X * H 1 := by rw [← hY]
      _ = Y0 * (Y0 * H 0 - PowerSeries.X * H 1) := by ring
  | succ k hk ih =>
    calc
      Y0 * A0 - (1 + Y0) * PowerSeries.X * B0
          = Y0 ^ k * (Y0 * H (k - 1) - PowerSeries.X * H k) := ih
      _ = Y0 ^ k * (Y0 * (Y0 * H k - PowerSeries.X * H (k + 1))) := by
          rw [step_telescope k hk]
      _ = Y0 ^ (k + 1) * (Y0 * H (k + 1 - 1) - PowerSeries.X * H (k + 1)) := by
          have hsub : k + 1 - 1 = k := by omega
          rw [hsub, pow_succ]
          ring

private lemma coeff_Y0_pow_mul_eq_zero (Z : PowerSeries ℚ) :
    ∀ m n : ℕ, n < m → PowerSeries.coeff n (Y0 ^ m * Z) = 0 := by
  intro m
  induction m with
  | zero =>
    intro n hn
    omega
  | succ m ih =>
    intro n hn
    rw [pow_succ', mul_assoc, PowerSeries.coeff_mul]
    refine Finset.sum_eq_zero fun p hp => ?_
    rw [Finset.mem_antidiagonal] at hp
    by_cases hp1 : p.1 = 0
    · rw [hp1, PowerSeries.coeff_zero_eq_constantCoeff_apply, Y0_constantCoeff, zero_mul]
    · have hp2 : p.2 < m := by omega
      rw [ih p.2 hp2, mul_zero]

private lemma A0_ode_rel : Y0 * A0 = (1 + Y0) * PowerSeries.X * B0 := by
  rw [← sub_eq_zero]
  ext n
  rw [map_zero]
  have h := congr_arg (PowerSeries.coeff n) (mul_Y0_pow_eq (n + 1) (by omega))
  rw [coeff_Y0_pow_mul_eq_zero _ (n + 1) n (by omega)] at h
  exact h

private lemma A0_eq_one_sub_Y0_mul_B0 : A0 = (1 - Y0) * B0 := by
  rw [← sub_eq_zero]
  apply Y0_mul_eq_zero
  calc
    Y0 * (A0 - (1 - Y0) * B0) = Y0 * A0 - Y0 * (1 - Y0) * B0 := by ring
    _ = (1 + Y0) * PowerSeries.X * B0 - (1 + Y0) * PowerSeries.X * B0 := by
      rw [A0_ode_rel, Y0_mul_one_sub]
    _ = 0 := sub_self _

private lemma A0_satisfies_ode :
    B0 * (A0 - 2 * PowerSeries.X * B0) = A0 * (A0 - PowerSeries.X * B0) := by
  have hA := A0_eq_one_sub_Y0_mul_B0
  have hY := Y0_mul_one_sub
  rw [hA]
  calc
    B0 * ((1 - Y0) * B0 - 2 * PowerSeries.X * B0)
        = (1 - Y0 - 2 * PowerSeries.X) * B0 ^ 2 := by ring
    _ = (1 - 2 * Y0 + (Y0 - (1 + Y0) * PowerSeries.X) - (1 - Y0) * PowerSeries.X) * B0 ^ 2 := by
        ring
    _ = (1 - 2 * Y0 + (Y0 - Y0 * (1 - Y0)) - (1 - Y0) * PowerSeries.X) * B0 ^ 2 := by
        rw [← hY]
    _ = (1 - Y0) * B0 * ((1 - Y0) * B0 - PowerSeries.X * B0) := by ring

private lemma ode_coeff_unique (A : PowerSeries ℚ) (hA0 : A.constantCoeff = 1)
    (hODE :
      let B := PowerSeries.derivative (R := ℚ) A
      B * (A - 2 * PowerSeries.X * B) = A * (A - PowerSeries.X * B)) :
    ∀ k : ℕ, PowerSeries.coeff k A = PowerSeries.coeff k A0 := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    cases k with
    | zero =>
      rw [PowerSeries.coeff_zero_eq_constantCoeff_apply,
        PowerSeries.coeff_zero_eq_constantCoeff_apply, hA0, A0_constantCoeff]
    | succ m =>
      set B := PowerSeries.derivative (R := ℚ) A
      have hB_lt : ∀ j < m, PowerSeries.coeff j B = PowerSeries.coeff j B0 := by
        intro j hj
        rw [PowerSeries.coeff_derivative, B0, PowerSeries.coeff_derivative, ih (j + 1) (by omega)]
      have hcA := congr_arg (PowerSeries.coeff m) hODE
      have hcA0 := congr_arg (PowerSeries.coeff m) A0_satisfies_ode
      have hLHS :
          PowerSeries.coeff m (B * (A - 2 * PowerSeries.X * B)) -
            PowerSeries.coeff m (B0 * (A0 - 2 * PowerSeries.X * B0)) =
          PowerSeries.coeff m B - PowerSeries.coeff m B0 := by
        have hBA :
            PowerSeries.coeff m (B * A) - PowerSeries.coeff m (B0 * A0) =
              PowerSeries.coeff m B - PowerSeries.coeff m B0 := by
          rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul, ← Finset.sum_sub_distrib]
          have hmem : (m, 0) ∈ Finset.antidiagonal m := by simp
          rw [← Finset.add_sum_erase _ _ hmem]
          have hrest :
              ∑ p ∈ (Finset.antidiagonal m).erase (m, 0),
                (PowerSeries.coeff p.1 B * PowerSeries.coeff p.2 A -
                  PowerSeries.coeff p.1 B0 * PowerSeries.coeff p.2 A0) = 0 := by
            refine Finset.sum_eq_zero fun p hp => ?_
            rw [Finset.mem_erase, Finset.mem_antidiagonal] at hp
            have hp1 : p.1 < m := by
              rcases hp with ⟨hne, hsum⟩
              by_contra hge
              have h1 : p.1 = m := by omega
              have h2 : p.2 = 0 := by omega
              exact hne (Prod.ext h1 h2)
            have hp2 : p.2 ≤ m := by omega
            rw [hB_lt p.1 hp1, ih p.2 (by omega), sub_self]
          rw [hrest, add_zero]
          have h0A : PowerSeries.coeff 0 A = 1 := by
            rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, hA0]
          have h0A0 : PowerSeries.coeff 0 A0 = 1 := by
            rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, A0_constantCoeff]
          rw [h0A, h0A0, mul_one, mul_one]
        have hXBB :
            PowerSeries.coeff m (2 * PowerSeries.X * B * B) =
              PowerSeries.coeff m (2 * PowerSeries.X * B0 * B0) := by
          have h2 : ∀ f : PowerSeries ℚ,
              2 * PowerSeries.X * f * f = 2 • (PowerSeries.X * (f * f)) := by
            intro f
            simp only [nsmul_eq_mul, Nat.cast_ofNat]
            ring
          rw [h2 B, h2 B0, map_nsmul, map_nsmul]
          congr 1
          cases m with
          | zero => simp
          | succ m' =>
            rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_succ_X_mul,
              PowerSeries.coeff_mul, PowerSeries.coeff_mul]
            refine Finset.sum_congr rfl fun p hp => ?_
            rw [Finset.mem_antidiagonal] at hp
            rw [hB_lt p.1 (by omega), hB_lt p.2 (by omega)]
        have hexp : ∀ f g : PowerSeries ℚ, f * (g - 2 * PowerSeries.X * f) =
            f * g - 2 * PowerSeries.X * f * f := fun f g => by ring
        rw [hexp B A, hexp B0 A0, map_sub, map_sub]
        calc
          PowerSeries.coeff m (B * A) - PowerSeries.coeff m (2 * PowerSeries.X * B * B) -
              (PowerSeries.coeff m (B0 * A0) - PowerSeries.coeff m (2 * PowerSeries.X * B0 * B0))
              = (PowerSeries.coeff m (B * A) - PowerSeries.coeff m (B0 * A0)) -
                (PowerSeries.coeff m (2 * PowerSeries.X * B * B) -
                  PowerSeries.coeff m (2 * PowerSeries.X * B0 * B0)) := by ring
          _ = PowerSeries.coeff m B - PowerSeries.coeff m B0 := by rw [hBA, hXBB, sub_self, sub_zero]
      have hRHS :
          PowerSeries.coeff m (A * (A - PowerSeries.X * B)) =
            PowerSeries.coeff m (A0 * (A0 - PowerSeries.X * B0)) := by
        have hAA : PowerSeries.coeff m (A * A) = PowerSeries.coeff m (A0 * A0) := by
          rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
          refine Finset.sum_congr rfl fun p hp => ?_
          rw [Finset.mem_antidiagonal] at hp
          rw [ih p.1 (by omega), ih p.2 (by omega)]
        have hXAB :
            PowerSeries.coeff m (PowerSeries.X * (A * B)) =
              PowerSeries.coeff m (PowerSeries.X * (A0 * B0)) := by
          cases m with
          | zero => simp
          | succ m' =>
            rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_succ_X_mul,
              PowerSeries.coeff_mul, PowerSeries.coeff_mul]
            refine Finset.sum_congr rfl fun p hp => ?_
            rw [Finset.mem_antidiagonal] at hp
            rw [ih p.1 (by omega), hB_lt p.2 (by omega)]
        have hexp : ∀ f g : PowerSeries ℚ, f * (f - PowerSeries.X * g) =
            f * f - PowerSeries.X * (f * g) := fun f g => by ring
        rw [hexp A B, hexp A0 B0, map_sub, map_sub, hAA, hXAB]
      have hBm : PowerSeries.coeff m B = PowerSeries.coeff m B0 := by
        have hsub : PowerSeries.coeff m B - PowerSeries.coeff m B0 = 0 := by
          rw [← hLHS, hcA, hcA0, hRHS, sub_self]
        exact sub_eq_zero.mp hsub
      rw [PowerSeries.coeff_derivative, B0, PowerSeries.coeff_derivative] at hBm
      have hm1 : ((m : ℚ) + 1) ≠ 0 := by positivity
      exact mul_right_cancel₀ hm1 hBm

end OMA.Mo481528Proof

theorem OMA.solution : type_of% @OMA.S_mo_481528.main := by
  intro A hA0 B hODE n
  have hcoeff := OMA.Mo481528Proof.ode_coeff_unique A hA0 hODE (n + 1)
  rw [hcoeff, OMA.Mo481528Proof.A0, PowerSeries.coeff_mk, OMA.Mo481528Proof.a0Coeff]
  have hfac : (((n + 1).factorial : ℕ) : ℚ) ≠ 0 := by positivity
  field_simp
