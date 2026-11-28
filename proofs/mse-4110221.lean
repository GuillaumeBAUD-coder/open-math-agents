import OMAStatements.S_mse_4110221

namespace OMA.S_mse_4110221_proof

open OMA.S_mse_4110221 Filter Topology

/-! Section 1: Connect `(riemannZeta 3).re` to `S = ∑' n, 1 / (2n + 1)^3` -/

private noncomputable def oddZeta3 : ℝ :=
  ∑' n : ℕ, (1 : ℝ) / (2 * (n : ℝ) + 1) ^ 3

private lemma summable_inv_pow_two : Summable fun n : ℕ => (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2 := by
  have h := (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two
  exact h.summable

private lemma summable_inv_pow_three : Summable fun n : ℕ => (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 3 := by
  refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun n => ?_) summable_inv_pow_two
  have h1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
  have hpow : ((n + 1 : ℕ) : ℝ) ^ 2 ≤ ((n + 1 : ℕ) : ℝ) ^ 3 :=
    pow_le_pow_right₀ h1 (by omega)
  exact one_div_le_one_div_of_le (by positivity) hpow

private lemma summable_oddZeta3 : Summable fun n : ℕ => (1 : ℝ) / (2 * (n : ℝ) + 1) ^ 3 := by
  have h := summable_inv_pow_three.comp_injective
    (show Function.Injective (fun k : ℕ => 2 * k) from fun _ _ h => by dsimp only at h; omega)
  refine h.congr fun k => ?_
  simp only [Function.comp_def]
  push_cast
  ring

private lemma riemannZeta_three_re :
    (riemannZeta 3).re = ∑' n : ℕ, (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 3 := by
  have hre : (1 : ℝ) < (3 : ℂ).re := by norm_num
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hre]
  have hs : Summable fun n : ℕ => (1 : ℂ) / ((n : ℂ) + 1) ^ (3 : ℂ) := by
    have h := (Complex.summable_one_div_nat_cpow.mpr hre).comp_injective Nat.succ_injective
    simpa [Function.comp_def] using h
  rw [Complex.re_tsum hs]
  congr 1
  ext n
  have hcast : ((n : ℂ) + 1) ^ (3 : ℂ) = ((((n + 1 : ℕ) : ℝ) ^ 3 : ℝ) : ℂ) := by
    rw [show (3 : ℂ) = ((3 : ℕ) : ℂ) by norm_num, Complex.cpow_natCast]
    push_cast
    ring
  rw [hcast, ← Complex.ofReal_one, ← Complex.ofReal_div, Complex.ofReal_re]

private lemma oddZeta3_eq : oddZeta3 = (7 / 8 : ℝ) * (riemannZeta 3).re := by
  have hodd : Summable fun k : ℕ => (1 : ℝ) / (((2 * k + 1 : ℕ) : ℝ)) ^ 3 := by
    have h := summable_inv_pow_three.comp_injective
      (show Function.Injective (fun k : ℕ => 2 * k) from fun _ _ h => by dsimp only at h; omega)
    simpa only [Function.comp_def] using h
  have heven : Summable fun k : ℕ => (1 : ℝ) / (((2 * k + 1 + 1 : ℕ) : ℝ)) ^ 3 := by
    have h := summable_inv_pow_three.comp_injective
      (show Function.Injective (fun k : ℕ => 2 * k + 1) from fun _ _ h => by dsimp only at h; omega)
    simpa only [Function.comp_def] using h
  have hsplit := tsum_even_add_odd (f := fun n : ℕ => (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 3) hodd heven
  have h1 : (∑' k : ℕ, (1 : ℝ) / (((2 * k + 1 : ℕ) : ℝ)) ^ 3) = oddZeta3 := by
    unfold oddZeta3
    congr 1
    ext k
    push_cast
    ring
  have h2 : (∑' k : ℕ, (1 : ℝ) / (((2 * k + 1 + 1 : ℕ) : ℝ)) ^ 3) =
      (1 / 8 : ℝ) * (riemannZeta 3).re := by
    rw [riemannZeta_three_re, ← tsum_mul_left]
    congr 1
    ext k
    push_cast
    field_simp
    ring
  rw [h1, h2, ← riemannZeta_three_re] at hsplit
  linarith

private lemma oddZeta3_pos : 0 < oddZeta3 := by
  unfold oddZeta3
  have h0 : (0 : ℝ) < (1 : ℝ) / (2 * ((0 : ℕ) : ℝ) + 1) ^ 3 := by norm_num
  exact lt_of_lt_of_le h0 (summable_oddZeta3.le_tsum 0 fun _ _ => by positivity)

/-! Section 2: Convergents `(y, x)`, `(Y, X)`, `tail` positivity, and `cf N = y (N + 2) / x (N + 2)` -/

private noncomputable def y : ℕ → ℝ
  | 0 => 1
  | 1 => 1
  | m + 2 => (v (m + 1) * y (m + 1) - ((m + 1 : ℕ) : ℝ) ^ 3 * y m) / ((m + 2 : ℕ) : ℝ) ^ 3

private noncomputable def x : ℕ → ℝ
  | 0 => 0
  | 1 => 1
  | m + 2 => (v (m + 1) * x (m + 1) - ((m + 1 : ℕ) : ℝ) ^ 3 * x m) / ((m + 2 : ℕ) : ℝ) ^ 3

private lemma y_succ_succ (m : ℕ) :
    y (m + 2) = (v (m + 1) * y (m + 1) - ((m + 1 : ℕ) : ℝ) ^ 3 * y m) / ((m + 2 : ℕ) : ℝ) ^ 3 := rfl

private lemma x_succ_succ (m : ℕ) :
    x (m + 2) = (v (m + 1) * x (m + 1) - ((m + 1 : ℕ) : ℝ) ^ 3 * x m) / ((m + 2 : ℕ) : ℝ) ^ 3 := rfl

private noncomputable def Y (m : ℕ) : ℝ := ((Nat.factorial m : ℝ) ^ 3) * y m

private noncomputable def X (m : ℕ) : ℝ := ((Nat.factorial m : ℝ) ^ 3) * x m

private lemma Y_rec (m : ℕ) : Y (m + 2) = v (m + 1) * Y (m + 1) - u (m + 1) * Y m := by
  unfold Y u
  rw [y_succ_succ]
  have hfac2 : (Nat.factorial (m + 2) : ℝ) = ((m + 2 : ℕ) : ℝ) * (Nat.factorial (m + 1) : ℝ) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  have hfac1 : (Nat.factorial (m + 1) : ℝ) = ((m + 1 : ℕ) : ℝ) * (Nat.factorial m : ℝ) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  have hm2 : ((m + 2 : ℕ) : ℝ) ≠ 0 := by positivity
  rw [hfac2, mul_pow, hfac1, mul_pow]
  field_simp [hm2]

private lemma X_rec (m : ℕ) : X (m + 2) = v (m + 1) * X (m + 1) - u (m + 1) * X m := by
  unfold X u
  rw [x_succ_succ]
  have hfac2 : (Nat.factorial (m + 2) : ℝ) = ((m + 2 : ℕ) : ℝ) * (Nat.factorial (m + 1) : ℝ) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  have hfac1 : (Nat.factorial (m + 1) : ℝ) = ((m + 1 : ℕ) : ℝ) * (Nat.factorial m : ℝ) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  have hm2 : ((m + 2 : ℕ) : ℝ) ≠ 0 := by positivity
  rw [hfac2, mul_pow, hfac1, mul_pow]
  field_simp [hm2]

private lemma tail_gt : ∀ d k : ℕ, 1 ≤ k → ((k + 1 : ℕ) : ℝ) ^ 3 < tail k d := by
  intro d
  induction d with
  | zero =>
    intro k hk
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    unfold tail v
    push_cast
    nlinarith [sq_nonneg ((k : ℝ) - 1)]
  | succ d ih =>
    intro k hk
    have hnext : ((k + 2 : ℕ) : ℝ) ^ 3 < tail (k + 1) d := ih (k + 1) (by omega)
    have hnext_pos : (0 : ℝ) < tail (k + 1) d := lt_trans (by positivity) hnext
    have hdiv : u (k + 1) / tail (k + 1) d < u (k + 1) / ((k + 2 : ℕ) : ℝ) ^ 3 := by
      unfold u
      exact div_lt_div_of_pos_left (by positivity) (by positivity) hnext
    have hstep : ((k + 1 : ℕ) : ℝ) ^ 3 < v k - u (k + 1) / ((k + 2 : ℕ) : ℝ) ^ 3 := by
      have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      have hden : (0 : ℝ) < ((k + 2 : ℕ) : ℝ) ^ 3 := by positivity
      have hkey : (0 : ℝ) < (v k - ((k + 1 : ℕ) : ℝ) ^ 3) * ((k + 2 : ℕ) : ℝ) ^ 3 - u (k + 1) := by
        unfold v u
        push_cast
        have hpoly :
            ((2 * (k : ℝ) + 1) * (3 * (k : ℝ) ^ 2 + 3 * (k : ℝ) + 1) - ((k : ℝ) + 1) ^ 3) *
              ((k : ℝ) + 2) ^ 3 - ((k : ℝ) + 1) ^ 6 =
            4 * (k : ℝ) ^ 6 + 30 * (k : ℝ) ^ 5 + 83 * (k : ℝ) ^ 4 + 104 * (k : ℝ) ^ 3 +
              57 * (k : ℝ) ^ 2 + 10 * (k : ℝ) - 1 := by ring
        rw [hpoly]
        have h1 : (1 : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
        have h2 : (1 : ℝ) ≤ (k : ℝ) ^ 3 := by nlinarith
        have h3 : (1 : ℝ) ≤ (k : ℝ) ^ 4 := by nlinarith
        have h4 : (1 : ℝ) ≤ (k : ℝ) ^ 5 := by nlinarith
        have h5 : (1 : ℝ) ≤ (k : ℝ) ^ 6 := by nlinarith
        linarith
      have hdiv2 : u (k + 1) / ((k + 2 : ℕ) : ℝ) ^ 3 < v k - ((k + 1 : ℕ) : ℝ) ^ 3 := by
        rw [div_lt_iff₀ hden]
        linarith
      linarith
    unfold tail
    linarith

private noncomputable def Tprod : ℕ → ℕ → ℝ
  | _, 0 => 1
  | k, d + 1 => tail (k + 1) d * Tprod (k + 1) d

private lemma Tprod_pos : ∀ d k : ℕ, 1 ≤ k → 0 < Tprod k d := by
  intro d
  induction d with
  | zero =>
    intro _ _
    unfold Tprod
    norm_num
  | succ d ih =>
    intro k hk
    unfold Tprod
    exact mul_pos (lt_trans (by positivity) (tail_gt d (k + 1) (by omega))) (ih (k + 1) (by omega))

private lemma rec_eval_tail {Z : ℕ → ℝ}
    (hZ : ∀ m : ℕ, Z (m + 2) = v (m + 1) * Z (m + 1) - u (m + 1) * Z m) :
    ∀ d k : ℕ, 1 ≤ k →
      Z (k + d + 1) = Tprod k d * (tail k d * Z k - u k * Z (k - 1)) := by
  intro d
  induction d with
  | zero =>
    intro k hk
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    simp only [add_zero, Tprod, tail, Nat.add_sub_cancel, one_mul]
    exact hZ m
  | succ d ih =>
    intro k hk
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    have h1 := ih (m + 2) (by omega)
    have hidx : m + 2 + d + 1 = m + 1 + (d + 1) + 1 := by omega
    rw [hidx, show m + 2 - 1 = m + 1 by omega] at h1
    rw [h1, hZ m]
    have ht_pos : (0 : ℝ) < tail (m + 2) d := lt_trans (by positivity) (tail_gt d (m + 2) (by omega))
    have ht_ne : tail (m + 2) d ≠ 0 := ne_of_gt ht_pos
    simp only [Tprod, tail, Nat.add_sub_cancel]
    field_simp [ht_ne]
    ring

private lemma cf_eq_div (N : ℕ) : cf N = y (N + 2) / x (N + 2) := by
  have hY := rec_eval_tail Y_rec N 1 (le_refl 1)
  have hX := rec_eval_tail X_rec N 1 (le_refl 1)
  have hidx : 1 + N + 1 = N + 2 := by omega
  rw [hidx] at hY hX
  have hY0 : Y 0 = 1 := by simp [Y, y]
  have hY1 : Y 1 = 1 := by simp [Y, y]
  have hX0 : X 0 = 0 := by simp [X, x]
  have hX1 : X 1 = 1 := by simp [X, x]
  rw [hY0, hY1] at hY
  rw [hX0, hX1] at hX
  have hTp : Tprod 1 N ≠ 0 := ne_of_gt (Tprod_pos N 1 (le_refl 1))
  have ht : tail 1 N ≠ 0 := ne_of_gt (lt_trans (by positivity) (tail_gt N 1 (le_refl 1)))
  have hfac : ((Nat.factorial (N + 2) : ℝ) ^ 3) ≠ 0 := by positivity
  have hdiv : Y (N + 2) / X (N + 2) = y (N + 2) / x (N + 2) := by
    unfold Y X
    exact mul_div_mul_left _ _ hfac
  rw [← hdiv, hY, hX]
  unfold cf
  field_simp [hTp, ht]
  ring

/-! Section 3: Exponential growth `y m ≥ 2^(m - 1)` for `m ≥ 1` -/

private lemma y_growth : ∀ m : ℕ, 0 < y m ∧ y m ≤ y (m + 1) ∧ (1 ≤ m → 2 * y m ≤ y (m + 1)) := by
  intro m
  induction m with
  | zero =>
    refine ⟨by simp [y], by simp [y], fun h => by omega⟩
  | succ m ih =>
    rcases ih with ⟨hym_pos, hym_le, _⟩
    have hm1 : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos m
    have hpoly :
        (2 : ℝ) * ((m + 2 : ℕ) : ℝ) ^ 3 ≤ v (m + 1) - ((m + 1 : ℕ) : ℝ) ^ 3 := by
      unfold v
      push_cast
      have hdiff :
          (2 * ((m : ℝ) + 1) + 1) * (3 * ((m : ℝ) + 1) ^ 2 + 3 * ((m : ℝ) + 1) + 1) -
            ((m : ℝ) + 1) ^ 3 - 2 * ((m : ℝ) + 2) ^ 3 =
          3 * (m : ℝ) ^ 3 + 12 * (m : ℝ) ^ 2 + 14 * (m : ℝ) + 4 := by ring
      have hnn : (0 : ℝ) ≤ 3 * (m : ℝ) ^ 3 + 12 * (m : ℝ) ^ 2 + 14 * (m : ℝ) + 4 := by positivity
      linarith
    have hy_pos : 0 < y (m + 1) := lt_of_lt_of_le hym_pos hym_le
    have h2le : 2 * y (m + 1) ≤ y (m + 2) := by
      rw [y_succ_succ, le_div_iff₀ (by positivity : (0 : ℝ) < ((m + 2 : ℕ) : ℝ) ^ 3)]
      have h1 : ((m + 1 : ℕ) : ℝ) ^ 3 * y m ≤ ((m + 1 : ℕ) : ℝ) ^ 3 * y (m + 1) :=
        mul_le_mul_of_nonneg_left hym_le (by positivity)
      nlinarith
    exact ⟨hy_pos, by linarith, fun _ => h2le⟩

private lemma y_ge_pow_two : ∀ m : ℕ, 1 ≤ m → (2 : ℝ) ^ (m - 1) ≤ y m := by
  intro m
  induction m with
  | zero => intro h; omega
  | succ m ih =>
    intro _
    rcases eq_or_lt_of_le (Nat.zero_le m) with rfl | hm
    · simp [y]
    · have h1 : (2 : ℝ) ^ (m - 1) ≤ y m := ih hm
      have h2 : 2 * y m ≤ y (m + 1) := (y_growth m).2.2 hm
      have hpow : (2 : ℝ) ^ m = 2 * (2 : ℝ) ^ (m - 1) := by
        conv_lhs => rw [← Nat.sub_add_cancel hm, pow_succ']
      rw [Nat.add_sub_cancel, hpow]
      linarith

private lemma tendsto_inv_y_zero : Tendsto (fun m : ℕ => (1 : ℝ) / y m) atTop (𝓝 0) := by
  have hpow : Tendsto (fun m : ℕ => ((1 / 2 : ℝ) ^ m) * 2) atTop (𝓝 (0 * 2)) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).mul_const 2
  rw [zero_mul] at hpow
  refine squeeze_zero' (eventually_atTop.mpr ⟨1, fun m hm => by
    have := (y_growth m).1
    positivity⟩) (eventually_atTop.mpr ⟨1, fun m hm => ?_⟩) hpow
  have hy := y_ge_pow_two m hm
  have h1 : (1 : ℝ) / y m ≤ 1 / (2 : ℝ) ^ (m - 1) :=
    one_div_le_one_div_of_le (by positivity) hy
  have h2 : (1 : ℝ) / (2 : ℝ) ^ (m - 1) = (1 / 2 : ℝ) ^ m * 2 := by
    have hpow2 : (2 : ℝ) ^ m = 2 * (2 : ℝ) ^ (m - 1) := by
      conv_lhs => rw [← Nat.sub_add_cancel hm, pow_succ']
    rw [one_div_pow, hpow2]
    field_simp
  linarith

/-! Section 4: Rational function `F`, logarithmic derivative `R`, and Zeilberger certificate `H` -/

private noncomputable def Pnum (m : ℕ) (t : ℝ) : ℝ :=
  ∏ i ∈ Finset.range m, (t + (i : ℝ) / 2)

private noncomputable def Pden (m : ℕ) (t : ℝ) : ℝ :=
  ∏ j ∈ Finset.range (m + 1), (t + (j : ℝ))

private noncomputable def F (m : ℕ) (t : ℝ) : ℝ :=
  (Pnum m t / Pden m t) ^ 2

private noncomputable def L (m : ℕ) (t : ℝ) : ℝ :=
  (∑ j ∈ Finset.range (m + 1), 1 / (t + (j : ℝ))) -
    (∑ i ∈ Finset.range m, 1 / (t + (i : ℝ) / 2))

private noncomputable def R (m : ℕ) (t : ℝ) : ℝ :=
  (1 / 8 : ℝ) * F m t * L m t

private lemma Pnum_pos (m : ℕ) {t : ℝ} (ht : 0 < t) : 0 < Pnum m t :=
  Finset.prod_pos fun _ _ => by positivity

private lemma Pden_pos (m : ℕ) {t : ℝ} (ht : 0 < t) : 0 < Pden m t :=
  Finset.prod_pos fun _ _ => by positivity

private lemma F_pos (m : ℕ) {t : ℝ} (ht : 0 < t) : 0 < F m t :=
  sq_pos_of_pos (div_pos (Pnum_pos m ht) (Pden_pos m ht))

private lemma Pnum_shift (m : ℕ) (t : ℝ) :
    t * (t + 1 / 2) * Pnum m (t + 1) =
      Pnum m t * (t + (m : ℝ) / 2) * (t + ((m : ℝ) + 1) / 2) := by
  induction m with
  | zero =>
    simp only [Pnum, Finset.prod_range_zero, Nat.cast_zero, zero_div, add_zero, one_mul, mul_one,
      zero_add]
  | succ m ih =>
    unfold Pnum at ih ⊢
    rw [Finset.prod_range_succ, Finset.prod_range_succ]
    push_cast
    linear_combination (t + 1 + (m : ℝ) / 2) * ih

private lemma Pden_shift (m : ℕ) (t : ℝ) :
    t * Pden m (t + 1) = Pden m t * (t + (m : ℝ) + 1) := by
  unfold Pden
  have h1 : ∏ j ∈ Finset.range (m + 2), (t + (j : ℝ)) =
      (∏ j ∈ Finset.range (m + 1), (t + ((j + 1 : ℕ) : ℝ))) * (t + ((0 : ℕ) : ℝ)) :=
    Finset.prod_range_succ' (fun j => t + (j : ℝ)) (m + 1)
  have h2 : ∏ j ∈ Finset.range (m + 2), (t + (j : ℝ)) =
      (∏ j ∈ Finset.range (m + 1), (t + (j : ℝ))) * (t + ((m + 1 : ℕ) : ℝ)) :=
    Finset.prod_range_succ (fun j => t + (j : ℝ)) (m + 1)
  have h3 : (∏ j ∈ Finset.range (m + 1), (t + ((j + 1 : ℕ) : ℝ))) =
      ∏ j ∈ Finset.range (m + 1), (t + 1 + (j : ℝ)) := by
    refine Finset.prod_congr rfl fun j _ => ?_
    push_cast
    ring
  rw [h3] at h1
  have h4 := h1.symm.trans h2
  push_cast at h4
  linarith

private lemma F_shift (m : ℕ) {t : ℝ} (ht : 0 < t) :
    F m (t + 1) =
      F m t * (((t + (m : ℝ) / 2) * (t + ((m : ℝ) + 1) / 2)) /
        ((t + 1 / 2) * (t + (m : ℝ) + 1))) ^ 2 := by
  unfold F
  rw [← mul_pow]
  congr 1
  have ht0 : t ≠ 0 := ne_of_gt ht
  have ht12 : t + 1 / 2 ≠ 0 := by linarith
  have htm1 : t + (m : ℝ) + 1 ≠ 0 := by positivity
  have hd0 : Pden m t ≠ 0 := ne_of_gt (Pden_pos m ht)
  have hd1 : Pden m (t + 1) ≠ 0 := ne_of_gt (Pden_pos m (by linarith))
  have hpn := Pnum_shift m t
  have hpd := Pden_shift m t
  have hpn' : Pnum m (t + 1) =
      Pnum m t * (t + (m : ℝ) / 2) * (t + ((m : ℝ) + 1) / 2) / (t * (t + 1 / 2)) := by
    rw [eq_div_iff (mul_ne_zero ht0 ht12)]
    linarith
  have hpd' : Pden m (t + 1) = Pden m t * (t + (m : ℝ) + 1) / t := by
    rw [eq_div_iff ht0]
    linarith
  rw [hpn', hpd']
  field_simp [ht0, ht12, htm1, hd0]

private lemma F_succ (m : ℕ) {t : ℝ} (ht : 0 < t) :
    F (m + 1) t = F m t * ((t + (m : ℝ) / 2) / (t + (m : ℝ) + 1)) ^ 2 := by
  unfold F Pnum Pden
  rw [Finset.prod_range_succ, Finset.prod_range_succ, ← mul_pow]
  congr 1
  have hd0 : (∏ j ∈ Finset.range (m + 1), (t + (j : ℝ))) ≠ 0 := ne_of_gt (Pden_pos m ht)
  have htm1 : t + (m : ℝ) + 1 ≠ 0 := by positivity
  push_cast
  field_simp [hd0, htm1]
  ring

private lemma hasDerivAt_prod_linear (c : ℕ → ℝ) (n : ℕ) {t : ℝ}
    (h : ∀ i < n, t + c i ≠ 0) :
    HasDerivAt (fun s : ℝ => ∏ i ∈ Finset.range n, (s + c i))
      ((∏ i ∈ Finset.range n, (t + c i)) * ∑ i ∈ Finset.range n, 1 / (t + c i)) t := by
  induction n with
  | zero =>
    simp only [Finset.prod_range_zero, Finset.sum_range_zero, mul_zero]
    exact hasDerivAt_const t 1
  | succ n ih =>
    have h_ih := ih fun i hi => h i (Nat.lt_succ_of_lt hi)
    have hne : t + c n ≠ 0 := h n (Nat.lt_succ_self n)
    have hlast : HasDerivAt (fun s : ℝ => s + c n) 1 t := (hasDerivAt_id t).add_const (c n)
    have hprod : (fun s : ℝ => ∏ i ∈ Finset.range (n + 1), (s + c i)) =
        fun s : ℝ => (∏ i ∈ Finset.range n, (s + c i)) * (s + c n) := by
      ext s
      exact Finset.prod_range_succ _ n
    rw [hprod]
    refine (h_ih.fun_mul hlast).congr_deriv ?_
    rw [Finset.prod_range_succ, Finset.sum_range_succ]
    field_simp [hne]

private lemma hasDerivAt_F (m : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (F m) (-2 * F m t * L m t) t := by
  have hd_num : HasDerivAt (Pnum m)
      (Pnum m t * ∑ i ∈ Finset.range m, 1 / (t + (i : ℝ) / 2)) t :=
    hasDerivAt_prod_linear (fun i => (i : ℝ) / 2) m (fun _ _ => by positivity)
  have hd_den : HasDerivAt (Pden m)
      (Pden m t * ∑ j ∈ Finset.range (m + 1), 1 / (t + (j : ℝ))) t :=
    hasDerivAt_prod_linear (fun j => (j : ℝ)) (m + 1) (fun _ _ => by positivity)
  have hd_pos : 0 < Pden m t := Pden_pos m ht
  have hd_ne : Pden m t ≠ 0 := ne_of_gt hd_pos
  have hd_div := hd_num.fun_div hd_den hd_ne
  refine (hd_div.fun_pow 2).congr_deriv ?_
  unfold F L
  set S1 : ℝ := ∑ i ∈ Finset.range m, 1 / (t + (i : ℝ) / 2)
  set S2 : ℝ := ∑ j ∈ Finset.range (m + 1), 1 / (t + (j : ℝ))
  have hsub : (Pnum m t * S1 * Pden m t - Pnum m t * (Pden m t * S2)) / Pden m t ^ 2 =
      Pnum m t * (S1 - S2) / Pden m t := by
    rw [show Pnum m t * S1 * Pden m t - Pnum m t * (Pden m t * S2) =
        Pden m t * (Pnum m t * (S1 - S2)) by ring, pow_two, mul_div_mul_left _ _ hd_ne]
  rw [hsub]
  ring

private noncomputable def Qpoly (m t : ℝ) : ℝ :=
  -(7 * m ^ 3 + 16 * m ^ 2 * t + m ^ 2 + 8 * m * t ^ 2 + 8 * m * t - 3 * m + 4 * t ^ 2 - 1)

private noncomputable def Q (m : ℕ) (t : ℝ) : ℝ :=
  Qpoly (m : ℝ) t * (2 * t - 1) ^ 2 / ((m : ℝ) + 2 * t - 1) ^ 2

private noncomputable def Q' (m : ℕ) (t : ℝ) : ℝ :=
  -4 * (2 * t - 1) *
    (7 * (m : ℝ) ^ 4 + 24 * (m : ℝ) ^ 3 * t - 3 * (m : ℝ) ^ 3 + 32 * (m : ℝ) ^ 2 * t ^ 2 -
      8 * (m : ℝ) ^ 2 * t - (m : ℝ) ^ 2 + 16 * (m : ℝ) * t ^ 3 - 6 * (m : ℝ) * t + (m : ℝ) +
      8 * t ^ 3 - 8 * t ^ 2 + 2 * t) / ((m : ℝ) + 2 * t - 1) ^ 3

private noncomputable def H (m : ℕ) (t : ℝ) : ℝ :=
  Q m t * F m t

private noncomputable def H' (m : ℕ) (t : ℝ) : ℝ :=
  Q' m t * F m t + Q m t * (-2 * F m t * L m t)

private noncomputable def G (m : ℕ) (t : ℝ) : ℝ :=
  -(1 / 16 : ℝ) * H' m t

private lemma hasDerivAt_Q (k : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (Q (k + 1)) (Q' (k + 1) t) t := by
  set m : ℝ := ((k + 1 : ℕ) : ℝ)
  have hm1 : 1 ≤ m := by dsimp only [m]; exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
  have hden_pos : 0 < m + 2 * t - 1 := by linarith
  have hden_ne : m + 2 * t - 1 ≠ 0 := ne_of_gt hden_pos
  have hdt : HasDerivAt (fun s : ℝ => s) 1 t := hasDerivAt_id t
  have hdt2 : HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t := by
    refine (hasDerivAt_pow 2 t).congr_deriv ?_
    norm_num
  have hd_poly : HasDerivAt (fun s : ℝ => Qpoly m s)
      (-(16 * m ^ 2 + 16 * m * t + 8 * m + 8 * t)) t := by
    unfold Qpoly
    have h1 := (((((((hasDerivAt_const t (7 * m ^ 3)).fun_add (hdt.const_mul (16 * m ^ 2))).fun_add
      (hasDerivAt_const t (m ^ 2))).fun_add (hdt2.const_mul (8 * m))).fun_add
      (hdt.const_mul (8 * m))).fun_sub (hasDerivAt_const t (3 * m))).fun_add
      (hdt2.const_mul 4)).fun_sub (hasDerivAt_const t 1)
    refine h1.neg.congr_deriv ?_
    ring
  have hd_lin1 : HasDerivAt (fun s : ℝ => 2 * s - 1) 2 t := by
    refine ((hdt.const_mul 2).sub_const 1).congr_deriv ?_
    ring
  have hd_sq1 : HasDerivAt (fun s : ℝ => (2 * s - 1) ^ 2) (4 * (2 * t - 1)) t := by
    refine (hd_lin1.fun_pow 2).congr_deriv ?_
    ring
  have hd_lin2 : HasDerivAt (fun s : ℝ => m + 2 * s - 1) 2 t := by
    refine (((hasDerivAt_const t m).fun_add (hdt.const_mul 2)).sub_const 1).congr_deriv ?_
    ring
  have hd_sq2 : HasDerivAt (fun s : ℝ => (m + 2 * s - 1) ^ 2) (4 * (m + 2 * t - 1)) t := by
    refine (hd_lin2.fun_pow 2).congr_deriv ?_
    ring
  have hQeq : Q (k + 1) = fun s : ℝ => Qpoly m s * (2 * s - 1) ^ 2 / (m + 2 * s - 1) ^ 2 := rfl
  rw [hQeq]
  refine ((hd_poly.fun_mul hd_sq1).fun_div hd_sq2 (pow_ne_zero 2 hden_ne)).congr_deriv ?_
  unfold Q' Qpoly
  change _ = -4 * (2 * t - 1) *
    (7 * m ^ 4 + 24 * m ^ 3 * t - 3 * m ^ 3 + 32 * m ^ 2 * t ^ 2 -
      8 * m ^ 2 * t - m ^ 2 + 16 * m * t ^ 3 - 6 * m * t + m +
      8 * t ^ 3 - 8 * t ^ 2 + 2 * t) / (m + 2 * t - 1) ^ 3
  field_simp [hden_ne]
  ring

private lemma hasDerivAt_H (k : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (H (k + 1)) (H' (k + 1) t) t :=
  (hasDerivAt_Q k ht).fun_mul (hasDerivAt_F (k + 1) ht)

private lemma F_zeilberger (k : ℕ) {t : ℝ} (ht : 0 < t) :
    ((k + 2 : ℕ) : ℝ) ^ 3 * F (k + 2) t - v (k + 1) * F (k + 1) t +
      ((k + 1 : ℕ) : ℝ) ^ 3 * F k t = H (k + 1) (t + 1) - H (k + 1) t := by
  have hk_nn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hFp1 : F (k + 2) t = F (k + 1) t * ((t + ((k : ℝ) + 1) / 2) / (t + (k : ℝ) + 2)) ^ 2 := by
    have h := F_succ (k + 1) ht
    push_cast at h
    simpa only [add_assoc, show (1 : ℝ) + 1 = 2 by norm_num] using h
  have hFm1 : F k t = F (k + 1) t * ((t + (k : ℝ) + 1) / (t + (k : ℝ) / 2)) ^ 2 := by
    have h := F_succ k ht
    rw [h]
    have hnum : t + (k : ℝ) / 2 ≠ 0 := by positivity
    have hden : t + (k : ℝ) + 1 ≠ 0 := by positivity
    rw [mul_assoc, ← mul_pow]
    have hmul : (t + (k : ℝ) / 2) / (t + (k : ℝ) + 1) * ((t + (k : ℝ) + 1) / (t + (k : ℝ) / 2)) = 1 := by
      field_simp [hnum, hden]
    rw [hmul, one_pow, mul_one]
  have hFsh : F (k + 1) (t + 1) =
      F (k + 1) t * (((t + ((k : ℝ) + 1) / 2) * (t + ((k : ℝ) + 2) / 2)) /
        ((t + 1 / 2) * (t + (k : ℝ) + 2))) ^ 2 := by
    have h := F_shift (k + 1) ht
    push_cast at h
    have heq1 : ((k : ℝ) + 1 + 1) = (k : ℝ) + 2 := by ring
    have heq2 : t + ((k : ℝ) + 1) + 1 = t + (k : ℝ) + 2 := by ring
    rw [heq1, heq2] at h
    exact h
  unfold H
  rw [hFp1, hFm1, hFsh]
  unfold v Q Qpoly
  push_cast
  have heq_d1 : (k : ℝ) + 1 + 2 * (t + 1) - 1 = (k : ℝ) + 2 * t + 2 := by ring
  have heq_d2 : (k : ℝ) + 1 + 2 * t - 1 = (k : ℝ) + 2 * t := by ring
  rw [heq_d1, heq_d2]
  have h1 : (k : ℝ) + t + 2 ≠ 0 := by positivity
  have h2 : (k : ℝ) + 2 * t ≠ 0 := by positivity
  have h3 : (k : ℝ) + 2 * t + 2 ≠ 0 := by positivity
  have h4 : 2 * t + 1 ≠ 0 := by positivity
  field_simp
  ring

private lemma R_zeilberger (k : ℕ) {t : ℝ} (ht : 0 < t) :
    ((k + 2 : ℕ) : ℝ) ^ 3 * R (k + 2) t - v (k + 1) * R (k + 1) t +
      ((k + 1 : ℕ) : ℝ) ^ 3 * R k t = G (k + 1) (t + 1) - G (k + 1) t := by
  have hd_lhs : HasDerivAt
      (fun s : ℝ => ((k + 2 : ℕ) : ℝ) ^ 3 * F (k + 2) s - v (k + 1) * F (k + 1) s +
        ((k + 1 : ℕ) : ℝ) ^ 3 * F k s)
      (((k + 2 : ℕ) : ℝ) ^ 3 * (-2 * F (k + 2) t * L (k + 2) t) -
        v (k + 1) * (-2 * F (k + 1) t * L (k + 1) t) +
        ((k + 1 : ℕ) : ℝ) ^ 3 * (-2 * F k t * L k t)) t :=
    (((hasDerivAt_F (k + 2) ht).const_mul _).fun_sub
      ((hasDerivAt_F (k + 1) ht).const_mul _)).fun_add
      ((hasDerivAt_F k ht).const_mul _)
  have hd_H1 : HasDerivAt (fun s : ℝ => H (k + 1) (s + 1)) (H' (k + 1) (t + 1)) t := by
    refine ((hasDerivAt_H k (by linarith : 0 < t + 1)).comp (h := fun s : ℝ => s + 1) t
      ((hasDerivAt_id t).add_const 1)).congr_deriv ?_
    ring
  have hd_rhs : HasDerivAt (fun s : ℝ => H (k + 1) (s + 1) - H (k + 1) s)
      (H' (k + 1) (t + 1) - H' (k + 1) t) t :=
    hd_H1.fun_sub (hasDerivAt_H k ht)
  have hev : (fun s : ℝ => ((k + 2 : ℕ) : ℝ) ^ 3 * F (k + 2) s - v (k + 1) * F (k + 1) s +
        ((k + 1 : ℕ) : ℝ) ^ 3 * F k s) =ᶠ[nhds t]
      (fun s : ℝ => H (k + 1) (s + 1) - H (k + 1) s) :=
    Filter.eventually_of_mem (Ioi_mem_nhds ht) fun s hs => F_zeilberger k hs
  have heq := (hd_rhs.congr_of_eventuallyEq hev).unique hd_lhs
  unfold R G
  linarith

private lemma G_half_eq_zero (k : ℕ) : G (k + 1) (1 / 2) = 0 := by
  unfold G H' Q Q'
  norm_num

/-! Section 5: Asymptotic `G (k + 1) t → 0` as `t → ∞` -/

private lemma tendsto_add_div_self (c : ℝ) :
    Tendsto (fun t : ℝ => (t + c) / t) atTop (𝓝 1) := by
  have h : Tendsto (fun t : ℝ => 1 + c * t⁻¹) atTop (𝓝 (1 + c * 0)) :=
    tendsto_const_nhds.add (tendsto_const_nhds.mul tendsto_inv_atTop_zero)
  rw [mul_zero, add_zero] at h
  refine h.congr' (eventually_atTop.mpr ⟨1, fun t ht => ?_⟩)
  have ht0 : t ≠ 0 := by linarith
  field_simp [ht0]

private lemma tendsto_add_div_add (a b : ℝ) :
    Tendsto (fun t : ℝ => (t + a) / (t + b)) atTop (𝓝 1) := by
  have h := (tendsto_add_div_self a).div (tendsto_add_div_self b) one_ne_zero
  rw [div_one] at h
  refine h.congr' (eventually_atTop.mpr ⟨1, fun t ht => ?_⟩)
  dsimp only [Pi.div_apply]
  have ht0 : t ≠ 0 := by linarith
  field_simp [ht0]

private lemma tendsto_one_div_add_zero (c : ℝ) :
    Tendsto (fun t : ℝ => (1 : ℝ) / (t + c)) atTop (𝓝 0) := by
  have h : Tendsto (fun t : ℝ => (t + c)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_id.atTop_add tendsto_const_nhds)
  simpa only [one_div] using h

private lemma tendsto_inv_pow_zero (d : ℕ) (hd : 1 ≤ d) :
    Tendsto (fun t : ℝ => (t⁻¹) ^ d) atTop (𝓝 0) := by
  have h0 : Tendsto (fun t : ℝ => t⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have h := h0.pow d
  rw [zero_pow (by omega)] at h
  exact h

private lemma tendsto_sq_mul_F (m : ℕ) :
    Tendsto (fun t : ℝ => t ^ 2 * F m t) atTop (𝓝 1) := by
  have hprod : Tendsto (fun t : ℝ => ∏ i ∈ Finset.range m, (t + (i : ℝ) / 2) / (t + (i : ℝ)))
      atTop (𝓝 1) := by
    have h := tendsto_finsetProd (Finset.range m) (fun i _ => tendsto_add_div_add ((i : ℝ) / 2) (i : ℝ))
    simpa only [Finset.prod_const_one] using h
  have hlast : Tendsto (fun t : ℝ => t / (t + (m : ℝ))) atTop (𝓝 1) := by
    simpa only [add_zero] using tendsto_add_div_add 0 (m : ℝ)
  have hsq := (hprod.mul hlast).pow 2
  rw [mul_one, one_pow] at hsq
  refine hsq.congr' (eventually_atTop.mpr ⟨1, fun t ht => ?_⟩)
  dsimp only [Pi.pow_apply, Pi.mul_apply]
  unfold F Pnum Pden
  rw [Finset.prod_range_succ, Finset.prod_div_distrib]
  have hd1 : (∏ i ∈ Finset.range m, (t + (i : ℝ))) ≠ 0 :=
    ne_of_gt (Finset.prod_pos fun _ _ => by positivity)
  have htm : t + (m : ℝ) ≠ 0 := by positivity
  field_simp [hd1, htm]

private lemma tendsto_L_corr (m : ℕ) :
    Tendsto (fun t : ℝ => -2 * L m t + 2 / t) atTop (𝓝 0) := by
  have hsum : Tendsto (fun t : ℝ =>
      2 * ∑ i ∈ Finset.range m, ((1 : ℝ) / (t + (i : ℝ) / 2) - 1 / (t + ((i : ℝ) + 1))))
      atTop (𝓝 0) := by
    have h1 := tendsto_finsetSum (Finset.range m) fun i _ =>
      (tendsto_one_div_add_zero ((i : ℝ) / 2)).sub (tendsto_one_div_add_zero ((i : ℝ) + 1))
    simpa only [sub_self, Finset.sum_const_zero, mul_zero] using h1.const_mul 2
  refine hsum.congr' (eventually_atTop.mpr ⟨1, fun t ht => ?_⟩)
  dsimp only
  unfold L
  rw [Finset.sum_range_succ', Finset.sum_sub_distrib]
  have hshift : (∑ i ∈ Finset.range m, (1 : ℝ) / (t + ((i + 1 : ℕ) : ℝ))) =
      ∑ i ∈ Finset.range m, (1 : ℝ) / (t + ((i : ℝ) + 1)) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    push_cast
    rfl
  rw [hshift]
  simp only [Nat.cast_zero, add_zero]
  ring

private lemma tendsto_Q_div_sq (k : ℕ) :
    Tendsto (fun t : ℝ => Q (k + 1) t / t ^ 2) atTop (𝓝 (-(8 * ((k + 1 : ℕ) : ℝ) + 4))) := by
  set m : ℝ := ((k + 1 : ℕ) : ℝ)
  have hden : Tendsto (fun t : ℝ => ((k : ℝ) * t⁻¹ + 2) ^ 2) atTop (𝓝 4) := by
    have h := ((tendsto_const_nhds (x := (k : ℝ))).mul tendsto_inv_atTop_zero).add
      (tendsto_const_nhds (x := (2 : ℝ)))
    have h2 := h.pow 2
    norm_num at h2
    exact h2
  have hnum : Tendsto (fun t : ℝ =>
      (-(7 * m ^ 3 * (t⁻¹) ^ 2 + 16 * m ^ 2 * t⁻¹ + m ^ 2 * (t⁻¹) ^ 2 + 8 * m +
        8 * m * t⁻¹ - 3 * m * (t⁻¹) ^ 2 + 4 - (t⁻¹) ^ 2)) * (2 - t⁻¹) ^ 2)
      atTop (𝓝 (-(8 * m + 4) * 4)) := by
    have h1 := (((((((tendsto_inv_pow_zero 2 (by omega)).const_mul (7 * m ^ 3)).add
      (tendsto_inv_atTop_zero.const_mul (16 * m ^ 2))).add
      ((tendsto_inv_pow_zero 2 (by omega)).const_mul (m ^ 2))).add
      (tendsto_const_nhds (x := 8 * m))).add
      (tendsto_inv_atTop_zero.const_mul (8 * m))).sub
      ((tendsto_inv_pow_zero 2 (by omega)).const_mul (3 * m))).add
      (tendsto_const_nhds (x := (4 : ℝ))) |>.sub (tendsto_inv_pow_zero 2 (by omega)) |>.neg
    have h2 := ((tendsto_const_nhds (x := (2 : ℝ))).sub tendsto_inv_atTop_zero).pow 2
    have hmul := h1.mul h2
    have hlim : -(7 * m ^ 3 * 0 + 16 * m ^ 2 * 0 + m ^ 2 * 0 + 8 * m + 8 * m * 0 - 3 * m * 0 +
        4 - 0) * (2 - 0) ^ 2 = -(8 * m + 4) * 4 := by ring
    rwa [hlim] at hmul
  have hq := hnum.div hden (by norm_num)
  rw [mul_div_cancel_right₀ _ (by norm_num : (4 : ℝ) ≠ 0)] at hq
  refine hq.congr' (eventually_atTop.mpr ⟨1, fun t ht => ?_⟩)
  dsimp only [Pi.div_apply]
  unfold Q Qpoly
  have hm_eq : m = (k : ℝ) + 1 := by dsimp only [m]; push_cast; ring
  have ht_pos : 0 < t := by linarith
  have hk_nn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  rw [show ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 by push_cast; ring,
    show (k : ℝ) + 1 + 2 * t - 1 = (k : ℝ) + 2 * t by ring, hm_eq]
  field_simp

private lemma tendsto_Q_corr_div_sq (k : ℕ) :
    Tendsto (fun t : ℝ => (Q' (k + 1) t - 2 / t * Q (k + 1) t) / t ^ 2) atTop (𝓝 0) := by
  set m : ℝ := ((k + 1 : ℕ) : ℝ)
  have hden : Tendsto (fun t : ℝ => ((k : ℝ) * t⁻¹ + 2) ^ 3) atTop (𝓝 8) := by
    have h := ((tendsto_const_nhds (x := (k : ℝ))).mul tendsto_inv_atTop_zero).add
      (tendsto_const_nhds (x := (2 : ℝ)))
    have h3 := h.pow 3
    norm_num at h3
    exact h3
  have hnum : Tendsto (fun t : ℝ =>
      (64 * m ^ 2 + 32 * m) * (t⁻¹) ^ 2 +
      (48 * m ^ 3 - 176 * m ^ 2 - 128 * m - 16) * (t⁻¹) ^ 3 +
      (-168 * m ^ 3 + 72 * m ^ 2 + 120 * m + 24) * (t⁻¹) ^ 4 +
      (-28 * m ^ 4 + 96 * m ^ 3 + 16 * m ^ 2 - 40 * m - 12) * (t⁻¹) ^ 5 +
      (14 * m ^ 4 - 12 * m ^ 3 - 8 * m ^ 2 + 4 * m + 2) * (t⁻¹) ^ 6) atTop (𝓝 0) := by
    have h1 := ((((tendsto_inv_pow_zero 2 (by omega)).const_mul (64 * m ^ 2 + 32 * m)).add
      ((tendsto_inv_pow_zero 3 (by omega)).const_mul (48 * m ^ 3 - 176 * m ^ 2 - 128 * m - 16))).add
      ((tendsto_inv_pow_zero 4 (by omega)).const_mul (-168 * m ^ 3 + 72 * m ^ 2 + 120 * m + 24))).add
      ((tendsto_inv_pow_zero 5 (by omega)).const_mul (-28 * m ^ 4 + 96 * m ^ 3 + 16 * m ^ 2 - 40 * m - 12)) |>.add
      ((tendsto_inv_pow_zero 6 (by omega)).const_mul (14 * m ^ 4 - 12 * m ^ 3 - 8 * m ^ 2 + 4 * m + 2))
    simpa only [mul_zero, add_zero] using h1
  have hq := hnum.div hden (by norm_num)
  rw [zero_div] at hq
  refine hq.congr' (eventually_atTop.mpr ⟨1, fun t ht => ?_⟩)
  dsimp only [Pi.div_apply]
  unfold Q' Q Qpoly
  have hm_eq : m = (k : ℝ) + 1 := by dsimp only [m]; push_cast; ring
  have ht_pos : 0 < t := by linarith
  have hk_nn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  rw [show ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 by push_cast; ring,
    show (k : ℝ) + 1 + 2 * t - 1 = (k : ℝ) + 2 * t by ring, hm_eq]
  field_simp
  ring

private lemma tendsto_G_zero (k : ℕ) :
    Tendsto (fun n : ℕ => G (k + 1) ((n : ℝ) + 1 / 2)) atTop (𝓝 0) := by
  have hH' : Tendsto (H' (k + 1)) atTop (𝓝 0) := by
    have h := (tendsto_sq_mul_F (k + 1)).mul
      ((tendsto_Q_corr_div_sq k).add ((tendsto_Q_div_sq k).mul (tendsto_L_corr (k + 1))))
    rw [mul_zero, add_zero, mul_zero] at h
    refine h.congr' (eventually_atTop.mpr ⟨1, fun t ht => ?_⟩)
    have ht0 : t ≠ 0 := by linarith
    unfold H'
    field_simp [ht0]
    ring
  have hG : Tendsto (G (k + 1)) atTop (𝓝 0) := by
    have h := hH'.const_mul (-(1 / 16 : ℝ))
    rw [mul_zero] at h
    exact h
  exact hG.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)

/-! Section 6: Uniform bound, summability, telescoping recurrence, and convergence -/

private lemma F_le_inv_sq (m : ℕ) {t : ℝ} (ht : 0 < t) :
    F m t ≤ 1 / (t + (m : ℝ)) ^ 2 := by
  unfold F Pnum Pden
  rw [Finset.prod_range_succ]
  have hle : Pnum m t ≤ ∏ j ∈ Finset.range m, (t + (j : ℝ)) := by
    induction m with
    | zero => simp [Pnum]
    | succ k ih =>
      unfold Pnum at ih ⊢
      rw [Finset.prod_range_succ, Finset.prod_range_succ]
      exact mul_le_mul ih (by linarith [Nat.cast_nonneg (α := ℝ) k]) (by positivity)
        (le_of_lt (Finset.prod_pos fun _ _ => by positivity))
  have hd_pos : 0 < ∏ j ∈ Finset.range m, (t + (j : ℝ)) :=
    Finset.prod_pos fun _ _ => by positivity
  have htm_pos : 0 < t + (m : ℝ) := by positivity
  have hdiv : Pnum m t / ((∏ j ∈ Finset.range m, (t + (j : ℝ))) * (t + (m : ℝ))) ≤
      1 / (t + (m : ℝ)) := by
    rw [div_le_div_iff₀ (mul_pos hd_pos htm_pos) htm_pos]
    nlinarith
  have hdiv_nn : 0 ≤ Pnum m t / ((∏ j ∈ Finset.range m, (t + (j : ℝ))) * (t + (m : ℝ))) :=
    div_nonneg (le_of_lt (Pnum_pos m ht)) (le_of_lt (mul_pos hd_pos htm_pos))
  calc
    (Pnum m t / ((∏ j ∈ Finset.range m, (t + (j : ℝ))) * (t + (m : ℝ)))) ^ 2
      ≤ (1 / (t + (m : ℝ))) ^ 2 := pow_le_pow_left₀ hdiv_nn hdiv 2
    _ = 1 / (t + (m : ℝ)) ^ 2 := by rw [one_div_pow]

private lemma abs_L_le (m : ℕ) {t : ℝ} (ht : 0 < t) :
    |L m t| ≤ (2 * (m : ℝ) + 1) / t := by
  unfold L
  have h1 : |∑ j ∈ Finset.range (m + 1), (1 : ℝ) / (t + (j : ℝ))| ≤ ((m + 1 : ℕ) : ℝ) / t := by
    calc
      |∑ j ∈ Finset.range (m + 1), (1 : ℝ) / (t + (j : ℝ))|
        ≤ ∑ j ∈ Finset.range (m + 1), |(1 : ℝ) / (t + (j : ℝ))| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j ∈ Finset.range (m + 1), (1 : ℝ) / t := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [abs_of_pos (by positivity)]
        exact one_div_le_one_div_of_le ht (by linarith [Nat.cast_nonneg (α := ℝ) j])
      _ = ((m + 1 : ℕ) : ℝ) / t := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring
  have h2 : |∑ i ∈ Finset.range m, (1 : ℝ) / (t + (i : ℝ) / 2)| ≤ (m : ℝ) / t := by
    calc
      |∑ i ∈ Finset.range m, (1 : ℝ) / (t + (i : ℝ) / 2)|
        ≤ ∑ i ∈ Finset.range m, |(1 : ℝ) / (t + (i : ℝ) / 2)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ Finset.range m, (1 : ℝ) / t := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [abs_of_pos (by positivity)]
        exact one_div_le_one_div_of_le ht (by linarith [Nat.cast_nonneg (α := ℝ) i])
      _ = (m : ℝ) / t := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring
  have htri : |(∑ j ∈ Finset.range (m + 1), (1 : ℝ) / (t + (j : ℝ))) -
      (∑ i ∈ Finset.range m, (1 : ℝ) / (t + (i : ℝ) / 2))| ≤
      |∑ j ∈ Finset.range (m + 1), (1 : ℝ) / (t + (j : ℝ))| +
      |∑ i ∈ Finset.range m, (1 : ℝ) / (t + (i : ℝ) / 2)| := abs_sub _ _
  have hsum_eq : ((m + 1 : ℕ) : ℝ) / t + (m : ℝ) / t = (2 * (m : ℝ) + 1) / t := by
    push_cast
    ring
  linarith

private lemma abs_R_zero_le (m : ℕ) : |R m ((0 : ℕ) + 1 / 2)| ≤ 1 := by
  unfold R
  have ht : (0 : ℝ) < (0 : ℕ) + 1 / 2 := by norm_num
  have hF_nn : 0 ≤ F m ((0 : ℕ) + 1 / 2) := le_of_lt (F_pos m ht)
  have hF_le := F_le_inv_sq m ht
  have hL_le := abs_L_le m ht
  rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 8), abs_of_nonneg hF_nn]
  have h1 : (1 / 8 : ℝ) * F m ((0 : ℕ) + 1 / 2) * |L m ((0 : ℕ) + 1 / 2)| ≤
      (1 / 8 : ℝ) * (1 / ((0 : ℕ) + 1 / 2 + (m : ℝ)) ^ 2) * ((2 * (m : ℝ) + 1) / ((0 : ℕ) + 1 / 2)) := by
    have hmul1 : (1 / 8 : ℝ) * F m ((0 : ℕ) + 1 / 2) ≤
        (1 / 8 : ℝ) * (1 / ((0 : ℕ) + 1 / 2 + (m : ℝ)) ^ 2) :=
      mul_le_mul_of_nonneg_left hF_le (by norm_num)
    exact mul_le_mul hmul1 hL_le (abs_nonneg _) (by positivity)
  have h2 : (1 / 8 : ℝ) * (1 / ((0 : ℕ) + 1 / 2 + (m : ℝ)) ^ 2) *
      ((2 * (m : ℝ) + 1) / ((0 : ℕ) + 1 / 2)) = 1 / (2 * (m : ℝ) + 1) := by
    have hpos : 2 * (m : ℝ) + 1 ≠ 0 := by positivity
    simp only [Nat.cast_zero, zero_add]
    field_simp [hpos]
    ring
  have h3 : (1 : ℝ) / (2 * (m : ℝ) + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]
    linarith [Nat.cast_nonneg (α := ℝ) m]
  linarith

private lemma abs_R_succ_le (m n : ℕ) :
    |R m (((n + 1 : ℕ) : ℝ) + 1 / 2)| ≤ (1 / 4 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2 := by
  unfold R
  set t : ℝ := ((n + 1 : ℕ) : ℝ) + 1 / 2
  have ht : 0 < t := by positivity
  have hF_nn : 0 ≤ F m t := le_of_lt (F_pos m ht)
  have hF_le := F_le_inv_sq m ht
  have hL_le := abs_L_le m ht
  rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 8), abs_of_nonneg hF_nn]
  have h1 : (1 / 8 : ℝ) * F m t * |L m t| ≤
      (1 / 8 : ℝ) * (1 / (t + (m : ℝ)) ^ 2) * ((2 * (m : ℝ) + 1) / t) := by
    have hmul1 : (1 / 8 : ℝ) * F m t ≤ (1 / 8 : ℝ) * (1 / (t + (m : ℝ)) ^ 2) :=
      mul_le_mul_of_nonneg_left hF_le (by norm_num)
    exact mul_le_mul hmul1 hL_le (abs_nonneg _) (by positivity)
  have h2 : ((2 * (m : ℝ) + 1) / 2) * ((n + 1 : ℕ) : ℝ) ^ 2 ≤ (t + (m : ℝ)) ^ 2 * t := by
    have ha : (2 * (m : ℝ) + 1) / 2 ≤ t + (m : ℝ) := by
      dsimp only [t]
      linarith [Nat.cast_nonneg (α := ℝ) (n + 1)]
    have hb : ((n + 1 : ℕ) : ℝ) ≤ t + (m : ℝ) := by
      dsimp only [t]
      linarith [Nat.cast_nonneg (α := ℝ) m]
    have hc : ((n + 1 : ℕ) : ℝ) ≤ t := by
      dsimp only [t]
      linarith
    have hab : ((2 * (m : ℝ) + 1) / 2) * ((n + 1 : ℕ) : ℝ) ≤ (t + (m : ℝ)) * (t + (m : ℝ)) :=
      mul_le_mul ha hb (by positivity) (by positivity)
    have habc := mul_le_mul hab hc (by positivity) (by positivity)
    nlinarith
  have h3 : (1 / 8 : ℝ) * (1 / (t + (m : ℝ)) ^ 2) * ((2 * (m : ℝ) + 1) / t) ≤
      (1 / 4 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2 := by
    have hEq : (1 / 8 : ℝ) * (1 / (t + (m : ℝ)) ^ 2) * ((2 * (m : ℝ) + 1) / t) =
        ((2 * (m : ℝ) + 1) / 8) / ((t + (m : ℝ)) ^ 2 * t) := by
      field_simp
    rw [hEq, div_le_div_iff₀ (by positivity) (by positivity)]
    linarith
  linarith

private lemma summable_R (m : ℕ) : Summable fun n : ℕ => R m ((n : ℝ) + 1 / 2) := by
  rw [← summable_nat_add_iff 1]
  refine Summable.of_norm_bounded (g := fun n : ℕ => (1 / 4 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2) ?_ ?_
  · have h := summable_inv_pow_two.mul_left (1 / 4 : ℝ)
    refine h.congr fun n => ?_
    ring
  · intro n
    rw [Real.norm_eq_abs]
    exact abs_R_succ_le m n

private noncomputable def r (m : ℕ) : ℝ :=
  ∑' n : ℕ, R m ((n : ℝ) + 1 / 2)

private lemma abs_r_le (m : ℕ) : |r m| ≤ 1 + (1 / 4 : ℝ) * (Real.pi ^ 2 / 6) := by
  unfold r
  have hs := summable_R m
  have habs_s : Summable fun n : ℕ => |R m ((n : ℝ) + 1 / 2)| := hs.abs
  have hle1 : |∑' n : ℕ, R m ((n : ℝ) + 1 / 2)| ≤ ∑' n : ℕ, |R m ((n : ℝ) + 1 / 2)| := by
    simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hs.norm
  rw [habs_s.tsum_eq_zero_add] at hle1
  have htail_s : Summable fun n : ℕ => (1 / 4 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2 := by
    refine (summable_inv_pow_two.mul_left (1 / 4 : ℝ)).congr fun n => ?_
    ring
  have htail_le : (∑' n : ℕ, |R m (((n + 1 : ℕ) : ℝ) + 1 / 2)|) ≤
      ∑' n : ℕ, (1 / 4 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2 :=
    (habs_s.comp_injective Nat.succ_injective).tsum_le_tsum (abs_R_succ_le m) htail_s
  have htail_eq : (∑' n : ℕ, (1 / 4 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2) =
      (1 / 4 : ℝ) * (Real.pi ^ 2 / 6) := by
    have hzeta := ((hasSum_nat_add_iff' 1).mpr hasSum_zeta_two).tsum_eq
    norm_num at hzeta
    rw [← hzeta, ← tsum_mul_left]
    congr 1
    ext n
    push_cast
    rw [div_eq_mul_inv]
  have h0 := abs_R_zero_le m
  linarith

private lemma r_zero : r 0 = oddZeta3 := by
  unfold r oddZeta3
  congr 1
  ext n
  unfold R F L Pnum Pden
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, Finset.sum_range_succ,
    Finset.sum_range_zero, Nat.cast_zero, add_zero, sub_zero, one_mul, zero_add]
  have hne : (n : ℝ) + 1 / 2 ≠ 0 := by positivity
  have hne2 : 2 * (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp [hne, hne2]
  ring

private lemma r_one : r 1 = oddZeta3 - 1 := by
  have hshift : r 1 = ∑' n : ℕ, (1 : ℝ) / (2 * ((n + 1 : ℕ) : ℝ) + 1) ^ 3 := by
    unfold r
    congr 1
    ext n
    unfold R F L Pnum Pden
    simp only [Finset.prod_range_succ, Finset.prod_range_zero, Finset.sum_range_succ,
      Finset.sum_range_zero, Nat.cast_zero, Nat.cast_one, zero_div, add_zero, one_mul, zero_add]
    have hne1 : (n : ℝ) + 1 / 2 ≠ 0 := by positivity
    have hne2 : (n : ℝ) + 1 / 2 + 1 ≠ 0 := by positivity
    have hne3 : 2 * ((n + 1 : ℕ) : ℝ) + 1 ≠ 0 := by positivity
    push_cast
    field_simp [hne1, hne2, hne3]
    ring
  rw [hshift]
  have h0 := summable_oddZeta3.tsum_eq_zero_add
  unfold oddZeta3
  rw [h0]
  norm_num

private lemma r_rec (k : ℕ) :
    ((k + 2 : ℕ) : ℝ) ^ 3 * r (k + 2) - v (k + 1) * r (k + 1) +
      ((k + 1 : ℕ) : ℝ) ^ 3 * r k = 0 := by
  have h1 := ((summable_R (k + 2)).hasSum.tendsto_sum_nat).const_mul (((k + 2 : ℕ) : ℝ) ^ 3)
  have h2 := ((summable_R (k + 1)).hasSum.tendsto_sum_nat).const_mul (v (k + 1))
  have h3 := ((summable_R k).hasSum.tendsto_sum_nat).const_mul (((k + 1 : ℕ) : ℝ) ^ 3)
  have hlhs := (h1.sub h2).add h3
  have hcomb : ∀ N : ℕ,
      ((k + 2 : ℕ) : ℝ) ^ 3 * (∑ n ∈ Finset.range N, R (k + 2) ((n : ℝ) + 1 / 2)) -
        v (k + 1) * (∑ n ∈ Finset.range N, R (k + 1) ((n : ℝ) + 1 / 2)) +
        ((k + 1 : ℕ) : ℝ) ^ 3 * (∑ n ∈ Finset.range N, R k ((n : ℝ) + 1 / 2)) =
      G (k + 1) ((N : ℝ) + 1 / 2) := by
    intro N
    have hsum :
        ((k + 2 : ℕ) : ℝ) ^ 3 * (∑ n ∈ Finset.range N, R (k + 2) ((n : ℝ) + 1 / 2)) -
          v (k + 1) * (∑ n ∈ Finset.range N, R (k + 1) ((n : ℝ) + 1 / 2)) +
          ((k + 1 : ℕ) : ℝ) ^ 3 * (∑ n ∈ Finset.range N, R k ((n : ℝ) + 1 / 2)) =
        ∑ n ∈ Finset.range N,
          (G (k + 1) (((n + 1 : ℕ) : ℝ) + 1 / 2) - G (k + 1) ((n : ℝ) + 1 / 2)) := by
      simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun n _ => ?_
      have hrz := R_zeilberger k (by positivity : (0 : ℝ) < (n : ℝ) + 1 / 2)
      have hcast : ((n + 1 : ℕ) : ℝ) + 1 / 2 = (n : ℝ) + 1 / 2 + 1 := by
        push_cast
        ring
      rw [hcast]
      exact hrz
    rw [hsum, Finset.sum_range_sub (fun n : ℕ => G (k + 1) ((n : ℝ) + 1 / 2)) N]
    simp only [Nat.cast_zero, zero_add, G_half_eq_zero, sub_zero]
  have hlhs' : Tendsto (fun N : ℕ => G (k + 1) ((N : ℝ) + 1 / 2)) atTop
      (𝓝 (((k + 2 : ℕ) : ℝ) ^ 3 * r (k + 2) - v (k + 1) * r (k + 1) +
        ((k + 1 : ℕ) : ℝ) ^ 3 * r k)) :=
    hlhs.congr hcomb
  exact tendsto_nhds_unique hlhs' (tendsto_G_zero k)

private lemma r_eq_lincomb : ∀ m : ℕ, r m = y m * oddZeta3 - x m := by
  intro m
  have hpair : ∀ n : ℕ, r n = y n * oddZeta3 - x n ∧ r (n + 1) = y (n + 1) * oddZeta3 - x (n + 1) := by
    intro n
    induction n with
    | zero =>
      refine ⟨?_, ?_⟩
      · simp only [y, x, one_mul, sub_zero]
        exact r_zero
      · simp only [y, x, one_mul]
        exact r_one
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      have hrec := r_rec n
      have hne : ((n + 2 : ℕ) : ℝ) ^ 3 ≠ 0 := by positivity
      have hr2 : r (n + 2) =
          (v (n + 1) * r (n + 1) - ((n + 1 : ℕ) : ℝ) ^ 3 * r n) / ((n + 2 : ℕ) : ℝ) ^ 3 := by
        rw [eq_div_iff hne]
        linarith
      rw [hr2, ih.1, ih.2, y_succ_succ, x_succ_succ]
      field_simp [hne]
      ring
  exact (hpair m).1

private lemma tendsto_x_div_y : Tendsto (fun m : ℕ => x m / y m) atTop (𝓝 oddZeta3) := by
  set C : ℝ := 1 + (1 / 4 : ℝ) * (Real.pi ^ 2 / 6)
  have hr_div_y : Tendsto (fun m : ℕ => r m / y m) atTop (𝓝 0) := by
    have hhi : Tendsto (fun m : ℕ => C * (1 / y m)) atTop (𝓝 (C * 0)) :=
      tendsto_inv_y_zero.const_mul C
    have hlo : Tendsto (fun m : ℕ => -(C * (1 / y m))) atTop (𝓝 (-(C * 0))) := hhi.neg
    rw [mul_zero] at hhi hlo
    rw [neg_zero] at hlo
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlo hhi (fun m => ?_) (fun m => ?_)
    · have hy_pos := (y_growth m).1
      have hrb := abs_le.mp (abs_r_le m)
      have h1 : -(C * (1 / y m)) = (-C) / y m := by ring
      rw [h1]
      exact div_le_div_of_nonneg_right hrb.1 (le_of_lt hy_pos)
    · have hy_pos := (y_growth m).1
      have hrb := abs_le.mp (abs_r_le m)
      have h1 : C * (1 / y m) = C / y m := by ring
      rw [h1]
      exact div_le_div_of_nonneg_right hrb.2 (le_of_lt hy_pos)
  have hsub : Tendsto (fun m : ℕ => oddZeta3 - r m / y m) atTop (𝓝 (oddZeta3 - 0)) :=
    tendsto_const_nhds.sub hr_div_y
  rw [sub_zero] at hsub
  refine hsub.congr fun m => ?_
  have hy_ne : y m ≠ 0 := ne_of_gt (y_growth m).1
  have hlin := r_eq_lincomb m
  field_simp [hy_ne]
  linarith

end OMA.S_mse_4110221_proof

theorem OMA.solution : type_of% @OMA.S_mse_4110221.main := by
  have hinv := OMA.S_mse_4110221_proof.tendsto_x_div_y.inv₀
    (ne_of_gt OMA.S_mse_4110221_proof.oddZeta3_pos)
  have hshift := hinv.comp (Filter.tendsto_add_atTop_nat 2)
  have htarget : OMA.S_mse_4110221_proof.oddZeta3⁻¹ =
      8 / (7 * (riemannZeta 3).re) := by
    rw [OMA.S_mse_4110221_proof.oddZeta3_eq]
    have hpos : (0 : ℝ) < (riemannZeta 3).re := by
      have h := OMA.S_mse_4110221_proof.oddZeta3_pos
      rw [OMA.S_mse_4110221_proof.oddZeta3_eq] at h
      linarith
    have hne : (riemannZeta 3).re ≠ 0 := ne_of_gt hpos
    field_simp [hne]
  rw [htarget] at hshift
  refine hshift.congr fun N => ?_
  simp only [Function.comp_def, inv_div]
  exact (OMA.S_mse_4110221_proof.cf_eq_div N).symm
