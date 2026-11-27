import OMAStatements.S_oeis_a007598

/-!
# Proof of OEIS A007598: Three Fibonacci reciprocal-series identities

We prove all three reciprocal Fibonacci identities using d'Ocagne's identity
`F_{n+m+1} * F_n - F_{n+1} * F_{n+m} = (-1)^(n+1) * F_m`, Catalan's identity
`F_{n+r}^2 - F_n * F_{n+2r} = (-1)^n * F_r^2`, and telescoping partial sums
with `F_{n+1} / F_n → φ`.
-/

namespace OMA.OeisA007598Proof

open Filter Finset BigOperators Real
open scoped Topology

private lemma fib_pos_real {n : ℕ} (hn : 0 < n) : (0 : ℝ) < (Nat.fib n : ℝ) := by
  exact_mod_cast Nat.fib_pos.mpr hn

private lemma fib_ne_zero_real {n : ℕ} (hn : 0 < n) : (Nat.fib n : ℝ) ≠ 0 :=
  (fib_pos_real hn).ne'

private lemma fib_ge_succ (n : ℕ) : n + 1 ≤ Nat.fib (n + 2) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => decide
    | 1 => decide
    | k + 2 =>
      have h1 := ih k (by omega)
      have h2 := ih (k + 1) (by omega)
      have hrec : Nat.fib (k + 2 + 2) = Nat.fib (k + 2) + Nat.fib (k + 1 + 2) := by
        simpa [Nat.add_assoc] using Nat.fib_add_two (n := k + 2)
      omega

private lemma docagne (m n : ℕ) :
    (Nat.fib (n + m + 1) : ℝ) * (Nat.fib n : ℝ) -
      (Nat.fib (n + 1) : ℝ) * (Nat.fib (n + m) : ℝ) =
      (-1 : ℝ) ^ (n + 1) * (Nat.fib m : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : (Nat.fib (n + 1 + m + 1) : ℝ) =
        (Nat.fib (n + m) : ℝ) + (Nat.fib (n + m + 1) : ℝ) := by
      have := Nat.fib_add_two (n := n + m)
      have heq : n + 1 + m + 1 = n + m + 2 := by omega
      rw [heq, this]; push_cast; ring
    have h2 : (Nat.fib (n + 1 + 1) : ℝ) = (Nat.fib n : ℝ) + (Nat.fib (n + 1) : ℝ) := by
      have := Nat.fib_add_two (n := n)
      rw [show n + 1 + 1 = n + 2 by omega, this]; push_cast; ring
    have h3 : n + 1 + m = n + m + 1 := by omega
    rw [h1, h2, h3]
    linear_combination -ih

private lemma fib_add_real (a b : ℕ) :
    (Nat.fib (a + b + 1) : ℝ) =
      (Nat.fib a : ℝ) * (Nat.fib b : ℝ) + (Nat.fib (a + 1) : ℝ) * (Nat.fib (b + 1) : ℝ) := by
  have := Nat.fib_add (m := a) (n := b)
  exact_mod_cast this

private lemma catalan (r n : ℕ) :
    (Nat.fib (n + r) : ℝ) ^ 2 - (Nat.fib n : ℝ) * (Nat.fib (n + 2 * r) : ℝ) =
      (-1 : ℝ) ^ n * (Nat.fib r : ℝ) ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 := fib_add_real (n + r) (n + r)
    have h2 := fib_add_real n (n + 2 * r)
    have heq : n + r + (n + r) + 1 = n + (n + 2 * r) + 1 := by omega
    rw [heq] at h1
    have h3 : n + 1 + r = n + r + 1 := by omega
    have h4 : n + 1 + 2 * r = n + 2 * r + 1 := by omega
    rw [h3, h4]
    linear_combination -h1 + h2 - ih

private noncomputable def ratio (n : ℕ) : ℝ := (Nat.fib (n + 1) : ℝ) / (Nat.fib n : ℝ)

private lemma tendsto_ratio : Tendsto ratio atTop (𝓝 goldenRatio) := by
  have h0 : Tendsto (fun n : ℕ => goldenConj ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_abs_lt_one (abs_lt.mpr ⟨neg_one_lt_goldenConj,
      goldenConj_neg.trans zero_lt_one⟩)
  rw [Metric.tendsto_atTop] at h0 ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := h0 ε hε
  refine ⟨max N 1, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_right N 1) hn
  have hnN : N ≤ n := le_trans (le_max_left N 1) hn
  have hfib_pos : (1 : ℝ) ≤ (Nat.fib n : ℝ) := by
    exact_mod_cast Nat.fib_pos.mpr (by omega)
  have hdiff : ratio n - goldenRatio = goldenConj ^ n / (Nat.fib n : ℝ) := by
    unfold ratio
    have hne : (Nat.fib n : ℝ) ≠ 0 := by linarith
    rw [div_sub' hne, mul_comm (Nat.fib n : ℝ) goldenRatio, fib_succ_sub_goldenRatio_mul_fib]
  rw [Real.dist_eq, hdiff, abs_div, abs_of_pos (by linarith : (0 : ℝ) < (Nat.fib n : ℝ))]
  have hle : |goldenConj ^ n| / (Nat.fib n : ℝ) ≤ |goldenConj ^ n| :=
    div_le_self (abs_nonneg _) hfib_pos
  have hlt := hN n hnN
  rw [Real.dist_eq, sub_zero] at hlt
  exact lt_of_le_of_lt hle hlt

private lemma sum_telescope_shift (g : ℕ → ℝ) (d N : ℕ) :
    ∑ i ∈ range N, (g (i + d) - g i) =
      ∑ j ∈ range d, g (N + j) - ∑ j ∈ range d, g j := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, ih]
    have hshift : ∑ j ∈ range d, g (N + 1 + j) - ∑ j ∈ range d, g (N + j) =
        g (N + d) - g N := by
      have h1 : ∑ j ∈ range (d + 1), g (N + j) =
          (∑ j ∈ range d, g (N + j)) + g (N + d) := sum_range_succ _ d
      have h2 : ∑ j ∈ range (d + 1), g (N + j) =
          g N + ∑ j ∈ range d, g (N + 1 + j) := by
        rw [sum_range_succ']
        simp only [Nat.add_zero]
        have hcongr : ∑ j ∈ range d, g (N + (j + 1)) = ∑ j ∈ range d, g (N + 1 + j) :=
          sum_congr rfl fun j _ => by congr 1; omega
        rw [hcongr]
        ring
      linarith
    linarith

private lemma tendsto_sum_shift_const (A : ℕ → ℝ) (L : ℝ) (hA : Tendsto A atTop (𝓝 L)) (d s : ℕ) :
    Tendsto (fun N => ∑ j ∈ range d, A (N + s + j)) atTop (𝓝 ((d : ℝ) * L)) := by
  have h : (d : ℝ) * L = ∑ _j ∈ range d, L := by simp
  rw [h]
  refine tendsto_finset_sum _ fun j _ => ?_
  have hcomp : Tendsto (fun N => A (N + s + j)) atTop (𝓝 L) := by
    simpa [Function.comp_def, Nat.add_assoc] using hA.comp (tendsto_add_atTop_nat (s + j))
  exact hcomp

private lemma sum_neg_one_pow_even (k N : ℕ) :
    ∑ j ∈ range (2 * k), (-1 : ℝ) ^ (N + j) = 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by omega, sum_range_succ, sum_range_succ, ih]
    rw [show N + (2 * k + 1) = (N + 2 * k) + 1 by omega, pow_succ]
    ring

private lemma tendsto_sum_shift_alt (A : ℕ → ℝ) (L : ℝ) (hA : Tendsto A atTop (𝓝 L))
    (k s : ℕ) :
    Tendsto (fun N => ∑ j ∈ range (2 * k), (-1 : ℝ) ^ (N + j) * A (N + s + j)) atTop (𝓝 0) := by
  have hzero : ∀ N : ℕ, ∑ j ∈ range (2 * k), (-1 : ℝ) ^ (N + j) * L = 0 := by
    intro N
    rw [← sum_mul, sum_neg_one_pow_even, zero_mul]
  have hrew : ∀ N : ℕ, ∑ j ∈ range (2 * k), (-1 : ℝ) ^ (N + j) * A (N + s + j) =
      ∑ j ∈ range (2 * k), (-1 : ℝ) ^ (N + j) * (A (N + s + j) - L) := by
    intro N
    have : ∑ j ∈ range (2 * k), (-1 : ℝ) ^ (N + j) * (A (N + s + j) - L) =
        (∑ j ∈ range (2 * k), (-1 : ℝ) ^ (N + j) * A (N + s + j)) -
        (∑ j ∈ range (2 * k), (-1 : ℝ) ^ (N + j) * L) := by
      rw [← sum_sub_distrib]
      refine sum_congr rfl fun j _ => by ring
    rw [this, hzero N, sub_zero]
  simp_rw [hrew]
  rw [show (0 : ℝ) = ∑ _j ∈ range (2 * k), (0 : ℝ) by simp]
  refine tendsto_finset_sum _ fun j _ => ?_
  have hcomp : Tendsto (fun N => A (N + s + j)) atTop (𝓝 L) := by
    simpa [Function.comp_def, Nat.add_assoc] using hA.comp (tendsto_add_atTop_nat (s + j))
  have hsub : Tendsto (fun N => A (N + s + j) - L) atTop (𝓝 0) := by
    simpa [sub_self] using hcomp.sub (tendsto_const_nhds (x := L))
  rw [Metric.tendsto_atTop] at hsub ⊢
  intro ε hε
  obtain ⟨N₀, hN₀⟩ := hsub ε hε
  refine ⟨N₀, fun N hN => ?_⟩
  have h1 := hN₀ N hN
  rw [Real.dist_eq, sub_zero] at h1 ⊢
  rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  exact h1

private lemma summable_inv_fib_mul (s d : ℕ) (hs : 1 ≤ s) :
    Summable (fun i : ℕ => 1 / ((Nat.fib (i + s) : ℝ) * (Nat.fib (i + s + d) : ℝ))) := by
  have hdom : Summable (fun i : ℕ => (1 : ℝ) / ((i + 1 : ℕ) : ℝ) ^ 2) := by
    have h2 : Summable (fun n : ℕ => ((n : ℝ) ^ 2)⁻¹) :=
      Real.summable_nat_pow_inv.mpr (by norm_num)
    simpa [Function.comp_def, one_div] using h2.comp_injective Nat.succ_injective
  refine Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_) (hdom.mul_left 4)
  have hfib_le : i + 1 ≤ 2 * Nat.fib (i + s) := by
    cases i with
    | zero =>
      simp only [zero_add]
      have : 1 ≤ Nat.fib s := Nat.fib_pos.mpr (by omega)
      omega
    | succ i =>
      have h1 : i + 1 ≤ Nat.fib (i + 2) := fib_ge_succ i
      have h2 : Nat.fib (i + 2) ≤ Nat.fib (i + 1 + s) := Nat.fib_mono (by omega)
      omega
  have hfib_le_r : ((i + 1 : ℕ) : ℝ) ≤ 2 * (Nat.fib (i + s) : ℝ) := by exact_mod_cast hfib_le
  have hmono : (Nat.fib (i + s) : ℝ) ≤ (Nat.fib (i + s + d) : ℝ) := by
    exact_mod_cast Nat.fib_mono (by omega : i + s ≤ i + s + d)
  have hp1 : (0 : ℝ) < (Nat.fib (i + s) : ℝ) := fib_pos_real (by omega)
  have hp2 : (0 : ℝ) < (Nat.fib (i + s + d) : ℝ) := fib_pos_real (by omega)
  have hsq : ((i + 1 : ℕ) : ℝ) ^ 2 ≤ 4 * ((Nat.fib (i + s) : ℝ) * (Nat.fib (i + s + d) : ℝ)) := by
    nlinarith
  rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
  linarith

private lemma term_eq_ratio_diff (s d i : ℕ) (hs : 1 ≤ s) (hd : 1 ≤ d) :
    1 / ((Nat.fib (i + s) : ℝ) * (Nat.fib (i + s + d) : ℝ)) =
      (-1 : ℝ) ^ (i + s + 1) / (Nat.fib d : ℝ) * (ratio (i + s + d) - ratio (i + s)) := by
  have hdoc := docagne d (i + s)
  have h1 : (Nat.fib (i + s) : ℝ) ≠ 0 := fib_ne_zero_real (by omega)
  have h2 : (Nat.fib (i + s + d) : ℝ) ≠ 0 := fib_ne_zero_real (by omega)
  have h3 : (Nat.fib d : ℝ) ≠ 0 := fib_ne_zero_real (by omega)
  have hsign : (-1 : ℝ) ^ (i + s + 1) * (-1 : ℝ) ^ (i + s + 1) = 1 := by
    rw [← pow_add, show (i + s + 1) + (i + s + 1) = 2 * (i + s + 1) by omega]
    simp [pow_mul]
  unfold ratio
  field_simp
  linear_combination -(Nat.fib d : ℝ) * hsign - (-1 : ℝ) ^ (i + s + 1) * hdoc

private lemma hasSum_inv_fib_mul (s k : ℕ) (hs : 1 ≤ s) (hk : 1 ≤ k) :
    HasSum (fun i : ℕ => 1 / ((Nat.fib (i + s) : ℝ) * (Nat.fib (i + s + 2 * k) : ℝ)))
      ((1 / (Nat.fib (2 * k) : ℝ)) *
        ∑ j ∈ range (2 * k), (-1 : ℝ) ^ (j + s) * ratio (j + s)) := by
  rw [(summable_inv_fib_mul s (2 * k) hs).hasSum_iff_tendsto_nat]
  let g : ℕ → ℝ := fun n => (-1 : ℝ) ^ (n + s + 1) * ratio (n + s)
  have hterm : ∀ i : ℕ, 1 / ((Nat.fib (i + s) : ℝ) * (Nat.fib (i + s + 2 * k) : ℝ)) =
      (1 / (Nat.fib (2 * k) : ℝ)) * (g (i + 2 * k) - g i) := by
    intro i
    rw [term_eq_ratio_diff s (2 * k) i hs (by omega)]
    dsimp only [g]
    have hpar : (-1 : ℝ) ^ (i + 2 * k + s + 1) = (-1 : ℝ) ^ (i + s + 1) := by
      rw [show i + 2 * k + s + 1 = (i + s + 1) + 2 * k by omega, pow_add]
      simp [pow_mul]
    rw [hpar, show i + 2 * k + s = i + s + 2 * k by omega]
    ring
  simp_rw [hterm, ← mul_sum, sum_telescope_shift g (2 * k)]
  have htail : Tendsto (fun N => ∑ j ∈ range (2 * k), g (N + j)) atTop (𝓝 0) := by
    have hrew : ∀ N, ∑ j ∈ range (2 * k), g (N + j) =
        (-1 : ℝ) ^ (s + 1) * ∑ j ∈ range (2 * k), (-1 : ℝ) ^ (N + j) * ratio (N + s + j) := by
      intro N
      rw [mul_sum]
      refine sum_congr rfl fun j _ => ?_
      dsimp only [g]
      rw [show N + j + s + 1 = (s + 1) + (N + j) by omega, pow_add,
        show N + j + s = N + s + j by omega]
      ring
    simp_rw [hrew]
    simpa using (tendsto_sum_shift_alt ratio goldenRatio tendsto_ratio k s).const_mul ((-1 : ℝ) ^ (s + 1))
  have hhead : -∑ j ∈ range (2 * k), g j = ∑ j ∈ range (2 * k), (-1 : ℝ) ^ (j + s) * ratio (j + s) := by
    rw [← sum_neg_distrib]
    refine sum_congr rfl fun j _ => ?_
    dsimp only [g]
    rw [pow_succ]
    ring
  have ht := (htail.sub_const (∑ j ∈ range (2 * k), g j)).const_mul (1 / (Nat.fib (2 * k) : ℝ))
  simpa [zero_sub, hhead] using ht

private lemma hasSum_alt_inv_fib_mul (s k : ℕ) (hs : 1 ≤ s) (hk : 1 ≤ k) :
    HasSum (fun i : ℕ => (-1 : ℝ) ^ (i + s + 1) / ((Nat.fib (i + s) : ℝ) * (Nat.fib (i + s + 2 * k) : ℝ)))
      ((1 / (Nat.fib (2 * k) : ℝ)) *
        ((2 * k : ℝ) * goldenRatio - ∑ j ∈ range (2 * k), ratio (j + s))) := by
  have hsumm : Summable (fun i : ℕ =>
      (-1 : ℝ) ^ (i + s + 1) / ((Nat.fib (i + s) : ℝ) * (Nat.fib (i + s + 2 * k) : ℝ))) := by
    refine Summable.of_norm ?_
    have heq : (fun i : ℕ => ‖(-1 : ℝ) ^ (i + s + 1) /
        ((Nat.fib (i + s) : ℝ) * (Nat.fib (i + s + 2 * k) : ℝ))‖) =
        fun i : ℕ => 1 / ((Nat.fib (i + s) : ℝ) * (Nat.fib (i + s + 2 * k) : ℝ)) := by
      ext i
      rw [norm_div, norm_pow, Real.norm_eq_abs, abs_neg, abs_one, one_pow,
        Real.norm_of_nonneg (by positivity)]
    rw [heq]
    exact summable_inv_fib_mul s (2 * k) hs
  rw [hsumm.hasSum_iff_tendsto_nat]
  let g : ℕ → ℝ := fun n => ratio (n + s)
  have hterm : ∀ i : ℕ, (-1 : ℝ) ^ (i + s + 1) /
      ((Nat.fib (i + s) : ℝ) * (Nat.fib (i + s + 2 * k) : ℝ)) =
      (1 / (Nat.fib (2 * k) : ℝ)) * (g (i + 2 * k) - g i) := by
    intro i
    rw [show (-1 : ℝ) ^ (i + s + 1) / ((Nat.fib (i + s) : ℝ) * (Nat.fib (i + s + 2 * k) : ℝ)) =
        (-1 : ℝ) ^ (i + s + 1) * (1 / ((Nat.fib (i + s) : ℝ) * (Nat.fib (i + s + 2 * k) : ℝ))) by ring]
    rw [term_eq_ratio_diff s (2 * k) i hs (by omega)]
    have hsign : (-1 : ℝ) ^ (i + s + 1) * (-1 : ℝ) ^ (i + s + 1) = 1 := by
      rw [← pow_add, show (i + s + 1) + (i + s + 1) = 2 * (i + s + 1) by omega]
      simp [pow_mul]
    dsimp only [g]
    rw [show i + 2 * k + s = i + s + 2 * k by omega]
    linear_combination (ratio (i + s + 2 * k) - ratio (i + s)) / (Nat.fib (2 * k) : ℝ) * hsign
  simp_rw [hterm, ← mul_sum, sum_telescope_shift g (2 * k)]
  have htail : Tendsto (fun N => ∑ j ∈ range (2 * k), g (N + j)) atTop (𝓝 ((2 * k : ℝ) * goldenRatio)) := by
    have hrew : ∀ N, ∑ j ∈ range (2 * k), g (N + j) = ∑ j ∈ range (2 * k), ratio (N + s + j) := by
      intro N
      refine sum_congr rfl fun j _ => by dsimp only [g]; rw [show N + j + s = N + s + j by omega]
    simp_rw [hrew]
    simpa [Nat.cast_mul, Nat.cast_ofNat] using tendsto_sum_shift_const ratio goldenRatio tendsto_ratio (2 * k) s
  exact (htail.sub_const (∑ j ∈ range (2 * k), g j)).const_mul (1 / (Nat.fib (2 * k) : ℝ))

private lemma split_recip_quartic (i : ℕ) :
    1 / (OMA.S_oeis_a007598.a (i + 3) - 1 / OMA.S_oeis_a007598.a (i + 3)) =
      (1 / 2 : ℝ) * (1 / ((Nat.fib (i + 2) : ℝ) * (Nat.fib (i + 4) : ℝ)) +
        1 / ((Nat.fib (i + 1) : ℝ) * (Nat.fib (i + 5) : ℝ))) := by
  unfold OMA.S_oeis_a007598.a
  have hc1 := catalan 1 (i + 2)
  have hc2 := catalan 2 (i + 1)
  simp only [Nat.fib_one, Nat.fib_two, Nat.cast_one, one_pow, mul_one] at hc1 hc2
  have h1 : (Nat.fib (i + 2) : ℝ) * (Nat.fib (i + 4) : ℝ) = (Nat.fib (i + 3) : ℝ) ^ 2 - (-1 : ℝ) ^ (i + 2) := by
    have : i + 2 + 1 = i + 3 := by omega
    have : i + 2 + 2 * 1 = i + 4 := by omega
    linarith [hc1]
  have h2 : (Nat.fib (i + 1) : ℝ) * (Nat.fib (i + 5) : ℝ) = (Nat.fib (i + 3) : ℝ) ^ 2 + (-1 : ℝ) ^ (i + 2) := by
    have ha : i + 1 + 2 = i + 3 := by omega
    have hb : i + 1 + 2 * 2 = i + 5 := by omega
    rw [ha, hb] at hc2
    have hs : (-1 : ℝ) ^ (i + 2) = -(-1 : ℝ) ^ (i + 1) := by rw [pow_succ]; ring
    linarith
  have hfn : (Nat.fib (i + 3) : ℝ) ≠ 0 := fib_ne_zero_real (by omega)
  have hf1 : (Nat.fib (i + 2) : ℝ) ≠ 0 := fib_ne_zero_real (by omega)
  have hf2 : (Nat.fib (i + 4) : ℝ) ≠ 0 := fib_ne_zero_real (by omega)
  have hf3 : (Nat.fib (i + 1) : ℝ) ≠ 0 := fib_ne_zero_real (by omega)
  have hf4 : (Nat.fib (i + 5) : ℝ) ≠ 0 := fib_ne_zero_real (by omega)
  have hfn_gt : (2 : ℝ) ≤ (Nat.fib (i + 3) : ℝ) := by
    have : 2 ≤ Nat.fib (i + 3) :=
      (by decide : 2 ≤ Nat.fib 3).trans (Nat.fib_mono (show 3 ≤ i + 3 by omega))
    exact_mod_cast this
  have hden : (Nat.fib (i + 3) : ℝ) ^ 2 - 1 / (Nat.fib (i + 3) : ℝ) ^ 2 ≠ 0 := by
    have hsq : (4 : ℝ) ≤ (Nat.fib (i + 3) : ℝ) ^ 2 := by nlinarith
    have hinv : 1 / (Nat.fib (i + 3) : ℝ) ^ 2 ≤ 1 := div_le_one_of_le₀ (by linarith) (by positivity)
    linarith
  have hsq1 : ((-1 : ℝ) ^ (i + 2)) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [h1, h2]
  have hp1 : (Nat.fib (i + 3) : ℝ) ^ 2 - (-1 : ℝ) ^ (i + 2) ≠ 0 := by rw [← h1]; exact mul_ne_zero hf1 hf2
  have hp2 : (Nat.fib (i + 3) : ℝ) ^ 2 + (-1 : ℝ) ^ (i + 2) ≠ 0 := by rw [← h2]; exact mul_ne_zero hf3 hf4
  have hnest : 1 / ((Nat.fib (i + 3) : ℝ) ^ 2 - 1 / (Nat.fib (i + 3) : ℝ) ^ 2) =
      (Nat.fib (i + 3) : ℝ) ^ 2 / ((Nat.fib (i + 3) : ℝ) ^ 4 - 1) := by
    have h4 : (Nat.fib (i + 3) : ℝ) ^ 4 - 1 ≠ 0 := by
      have hsq : (4 : ℝ) ≤ (Nat.fib (i + 3) : ℝ) ^ 2 := by nlinarith
      nlinarith
    field_simp
  rw [hnest]
  have h4 : (Nat.fib (i + 3) : ℝ) ^ 4 - 1 ≠ 0 := by
    have hsq : (4 : ℝ) ≤ (Nat.fib (i + 3) : ℝ) ^ 2 := by nlinarith
    nlinarith
  field_simp
  linear_combination -2 * (Nat.fib (i + 3) : ℝ) ^ 2 * hsq1

private lemma part1 :
    HasSum (fun i : ℕ => 1 / (OMA.S_oeis_a007598.a (i + 3) - 1 / OMA.S_oeis_a007598.a (i + 3))) (4 / 9 : ℝ) := by
  have hs1 := hasSum_inv_fib_mul 2 1 (by omega) (by omega)
  have hs2 := hasSum_inv_fib_mul 1 2 (by omega) (by omega)
  have hsum := (hs1.add hs2).mul_left (1 / 2 : ℝ)
  have hfun : (fun i : ℕ => 1 / (OMA.S_oeis_a007598.a (i + 3) - 1 / OMA.S_oeis_a007598.a (i + 3))) =
      fun i : ℕ => (1 / 2 : ℝ) * (1 / ((Nat.fib (i + 2) : ℝ) * (Nat.fib (i + 2 + 2 * 1) : ℝ)) +
        1 / ((Nat.fib (i + 1) : ℝ) * (Nat.fib (i + 1 + 2 * 2) : ℝ))) := by
    ext i
    exact split_recip_quartic i
  rw [hfun]
  have hval : (4 / 9 : ℝ) = (1 / 2 : ℝ) *
      (1 / (Nat.fib (2 * 1) : ℝ) * ∑ j ∈ range (2 * 1), (-1 : ℝ) ^ (j + 2) * ratio (j + 2) +
       1 / (Nat.fib (2 * 2) : ℝ) * ∑ j ∈ range (2 * 2), (-1 : ℝ) ^ (j + 1) * ratio (j + 1)) := by
    rw [show (2 * 1 : ℕ) = 2 by rfl, show (2 * 2 : ℕ) = 4 by rfl]
    simp only [sum_range_succ, range_zero, sum_empty, zero_add, ratio]
    norm_num [Nat.fib, Nat.fib_add_two]
  rw [hval]
  exact hsum

private lemma part2 :
    HasSum (fun i : ℕ => (-1 : ℝ) ^ (i + 3) / (OMA.S_oeis_a007598.a (i + 3) - 1 / OMA.S_oeis_a007598.a (i + 3)))
      (-(10 - 3 * Real.sqrt 5) / 18) := by
  have hs1 := hasSum_alt_inv_fib_mul 2 1 (by omega) (by omega)
  have hs2 := hasSum_alt_inv_fib_mul 1 2 (by omega) (by omega)
  have hsum := (hs1.sub hs2).mul_left (1 / 2 : ℝ)
  have hfun : (fun i : ℕ => (-1 : ℝ) ^ (i + 3) / (OMA.S_oeis_a007598.a (i + 3) - 1 / OMA.S_oeis_a007598.a (i + 3))) =
      fun i : ℕ => (1 / 2 : ℝ) *
        ((-1 : ℝ) ^ (i + 2 + 1) / ((Nat.fib (i + 2) : ℝ) * (Nat.fib (i + 2 + 2 * 1) : ℝ)) -
         (-1 : ℝ) ^ (i + 1 + 1) / ((Nat.fib (i + 1) : ℝ) * (Nat.fib (i + 1 + 2 * 2) : ℝ))) := by
    ext i
    rw [show (-1 : ℝ) ^ (i + 3) / (OMA.S_oeis_a007598.a (i + 3) - 1 / OMA.S_oeis_a007598.a (i + 3)) =
        (-1 : ℝ) ^ (i + 3) * (1 / (OMA.S_oeis_a007598.a (i + 3) - 1 / OMA.S_oeis_a007598.a (i + 3))) by ring]
    rw [split_recip_quartic]
    have h1 : i + 2 + 1 = i + 3 := by omega
    have h2 : (-1 : ℝ) ^ (i + 1 + 1) = -(-1 : ℝ) ^ (i + 3) := by
      rw [show i + 3 = (i + 1 + 1) + 1 by omega, pow_succ]; ring
    rw [h1, h2]
    ring_nf
  rw [hfun]
  have hval : -(10 - 3 * Real.sqrt 5) / 18 = (1 / 2 : ℝ) *
      (1 / (Nat.fib (2 * 1) : ℝ) * ((2 * (1 : ℕ) : ℝ) * goldenRatio - ∑ j ∈ range (2 * 1), ratio (j + 2)) -
       1 / (Nat.fib (2 * 2) : ℝ) * ((2 * (2 : ℕ) : ℝ) * goldenRatio - ∑ j ∈ range (2 * 2), ratio (j + 1))) := by
    rw [show (2 * 1 : ℕ) = 2 by rfl, show (2 * 2 : ℕ) = 4 by rfl]
    simp only [sum_range_succ, range_zero, sum_empty, zero_add, ratio, goldenRatio]
    norm_num [Nat.fib, Nat.fib_add_two]
    ring
  rw [hval]
  exact hsum

private lemma pair_ratio_identity {m j : ℕ} (hj1 : 1 ≤ j) (hjm : j < 2 * m) :
    (1 / (Nat.fib (2 * m) : ℝ)) * (ratio j + ratio (2 * m - j)) =
      1 / ((Nat.fib j : ℝ) * (Nat.fib (2 * m - j) : ℝ)) + 1 / (Nat.fib (2 * m) : ℝ) := by
  have hfib_add : (Nat.fib (2 * m) : ℝ) =
      (Nat.fib j : ℝ) * (Nat.fib (2 * m - j - 1) : ℝ) +
      (Nat.fib (j + 1) : ℝ) * (Nat.fib (2 * m - j) : ℝ) := by
    have h := fib_add_real j (2 * m - j - 1)
    have h1 : j + (2 * m - j - 1) + 1 = 2 * m := by omega
    have h2 : 2 * m - j - 1 + 1 = 2 * m - j := by omega
    rw [h1, h2] at h
    exact h
  have hfib_rec : (Nat.fib (2 * m - j + 1) : ℝ) =
      (Nat.fib (2 * m - j - 1) : ℝ) + (Nat.fib (2 * m - j) : ℝ) := by
    have := Nat.fib_add_two (n := 2 * m - j - 1)
    have h1 : 2 * m - j - 1 + 2 = 2 * m - j + 1 := by omega
    have h2 : 2 * m - j - 1 + 1 = 2 * m - j := by omega
    rw [h1, h2] at this
    exact_mod_cast this
  have h1 : (Nat.fib j : ℝ) ≠ 0 := fib_ne_zero_real (by omega)
  have h2 : (Nat.fib (2 * m - j) : ℝ) ≠ 0 := fib_ne_zero_real (by omega)
  have h3 : (Nat.fib (2 * m) : ℝ) ≠ 0 := fib_ne_zero_real (by omega)
  unfold ratio
  field_simp
  linear_combination (Nat.fib j : ℝ) * hfib_rec - hfib_add

private lemma part3 (k : ℕ) :
    HasSum (fun i : ℕ => if i + 1 = 2 * k + 1 then 0 else
      1 / (OMA.S_oeis_a007598.a (i + 1) + (-1 : ℝ) ^ (i + 1) * OMA.S_oeis_a007598.a (2 * k + 1)))
      (1 / OMA.S_oeis_a007598.a (4 * k + 2)) := by
  set m := 2 * k + 1 with hm_def
  have h2m : 2 * m = 4 * k + 2 := by omega
  rw [← h2m, ← hasSum_nat_add_iff' m]
  have htail_eq : (fun i : ℕ => if i + m + 1 = m then (0 : ℝ) else
      1 / (OMA.S_oeis_a007598.a (i + m + 1) + (-1 : ℝ) ^ (i + m + 1) * OMA.S_oeis_a007598.a m)) =
      fun i : ℕ => 1 / ((Nat.fib (i + 1) : ℝ) * (Nat.fib (i + 1 + 2 * m) : ℝ)) := by
    ext i
    rw [if_neg (by omega)]
    unfold OMA.S_oeis_a007598.a
    have hcat := catalan m (i + 1)
    have h1 : i + 1 + m = i + m + 1 := by omega
    rw [h1] at hcat
    have hsign : (-1 : ℝ) ^ (i + m + 1) = -(-1 : ℝ) ^ (i + 1) := by
      rw [show i + m + 1 = (i + 1) + (2 * k + 1) by omega, pow_add]
      have hodd : (-1 : ℝ) ^ (2 * k + 1) = -1 := by rw [pow_succ, pow_mul]; norm_num
      rw [hodd]
      ring
    rw [hsign]
    have heq : (Nat.fib (i + m + 1) : ℝ) ^ 2 + -(-1 : ℝ) ^ (i + 1) * (Nat.fib m : ℝ) ^ 2 =
        (Nat.fib (i + 1) : ℝ) * (Nat.fib (i + 1 + 2 * m) : ℝ) := by linarith
    rw [heq]
  rw [htail_eq]
  have hhs := hasSum_inv_fib_mul 1 m (by omega) (by omega)
  have hhead_split : ∑ i ∈ range m,
      (if i + 1 = m then (0 : ℝ) else
        1 / (OMA.S_oeis_a007598.a (i + 1) + (-1 : ℝ) ^ (i + 1) * OMA.S_oeis_a007598.a m)) =
      ∑ j ∈ range (2 * k), (-(-1 : ℝ) ^ (j + 1)) / ((Nat.fib (j + 1) : ℝ) * (Nat.fib (2 * m - (j + 1)) : ℝ)) := by
    rw [show m = 2 * k + 1 by omega, sum_range_succ, if_pos rfl, add_zero]
    have h0 : ∑ i ∈ range (2 * k),
        (if i + 1 = 2 * k + 1 then (0 : ℝ) else
          1 / (OMA.S_oeis_a007598.a (i + 1) + (-1 : ℝ) ^ (i + 1) * OMA.S_oeis_a007598.a m)) =
        ∑ i ∈ range (2 * k),
          1 / (OMA.S_oeis_a007598.a (i + 1) + (-1 : ℝ) ^ (i + 1) * OMA.S_oeis_a007598.a m) := by
      refine sum_congr rfl fun i hi => if_neg (by rw [mem_range] at hi; omega)
    rw [h0, ← sum_range_reflect]
    refine sum_congr rfl fun j hj => ?_
    rw [mem_range] at hj
    unfold OMA.S_oeis_a007598.a
    set n := 2 * k - 1 - j + 1 with hn_def
    have hnm : n + (j + 1) = m := by omega
    have hcat := catalan n (j + 1)
    rw [show j + 1 + n = m by omega, show j + 1 + 2 * n = 2 * m - (j + 1) by omega] at hcat
    have hsign : (-1 : ℝ) ^ n = -(-1 : ℝ) ^ (j + 1) := by
      have : n + (j + 1) = 2 * k + 1 := by omega
      have hmul : (-1 : ℝ) ^ n * (-1 : ℝ) ^ (j + 1) = -1 := by
        rw [← pow_add, this, pow_succ]; simp [pow_mul]
      have hsq : (-1 : ℝ) ^ (j + 1) * (-1 : ℝ) ^ (j + 1) = 1 := by
        rw [← pow_add, show (j + 1) + (j + 1) = 2 * (j + 1) by omega]; simp [pow_mul]
      linear_combination (-1 : ℝ) ^ (j + 1) * hmul - (-1 : ℝ) ^ n * hsq
    have hsq : (-1 : ℝ) ^ (j + 1) * (-1 : ℝ) ^ (j + 1) = 1 := by
      rw [← pow_add, show (j + 1) + (j + 1) = 2 * (j + 1) by omega]; simp [pow_mul]
    have hden : (Nat.fib n : ℝ) ^ 2 + (-1 : ℝ) ^ n * (Nat.fib m : ℝ) ^ 2 =
        (-(-1 : ℝ) ^ (j + 1)) * ((Nat.fib (j + 1) : ℝ) * (Nat.fib (2 * m - (j + 1)) : ℝ)) := by
      rw [hsign]
      linear_combination -(Nat.fib n : ℝ) ^ 2 * hsq - (-1 : ℝ) ^ (j + 1) * hcat
    rw [hden]
    have hne : (Nat.fib (j + 1) : ℝ) * (Nat.fib (2 * m - (j + 1)) : ℝ) ≠ 0 :=
      mul_ne_zero (fib_ne_zero_real (by omega)) (fib_ne_zero_real (by omega))
    have hne1 : -(-1 : ℝ) ^ (j + 1) ≠ 0 := neg_ne_zero.mpr (pow_ne_zero _ (by norm_num))
    rw [div_eq_div_iff (mul_ne_zero hne1 hne) hne]
    linear_combination -((Nat.fib (j + 1) : ℝ) * (Nat.fib (2 * m - (j + 1)) : ℝ)) * hsq
  have htail_split : ∑ j ∈ range (2 * m), (-1 : ℝ) ^ (j + 1) * ratio (j + 1) =
      (∑ j ∈ range (2 * k), (-1 : ℝ) ^ (j + 1) * (ratio (j + 1) + ratio (2 * m - (j + 1)))) +
      (ratio (2 * m) - ratio m) := by
    conv_lhs => rw [show 2 * m = (2 * k + 1) + (2 * k + 1) by omega]
    rw [sum_range_add, sum_range_succ, sum_range_succ]
    have hleft_m : (-1 : ℝ) ^ (2 * k + 1) * ratio (2 * k + 1) = -ratio m := by
      rw [← hm_def, show m = 2 * k + 1 by omega, pow_succ]; simp [pow_mul]
    have hright_2m : (-1 : ℝ) ^ (2 * k + 1 + 2 * k + 1) * ratio (2 * k + 1 + 2 * k + 1) = ratio (2 * m) := by
      rw [show 2 * k + 1 + 2 * k + 1 = 2 * m by omega]
      simp [pow_mul]
    have hmid : ∑ j ∈ range (2 * k), (-1 : ℝ) ^ (2 * k + 1 + j + 1) * ratio (2 * k + 1 + j + 1) =
        ∑ j ∈ range (2 * k), (-1 : ℝ) ^ (j + 1) * ratio (2 * m - (j + 1)) := by
      rw [← sum_range_reflect]
      refine sum_congr rfl fun j hj => ?_
      rw [mem_range] at hj
      have hidx : 2 * k + 1 + (2 * k - 1 - j) + 1 = 2 * m - (j + 1) := by omega
      have hpar : (-1 : ℝ) ^ (2 * m - (j + 1)) = (-1 : ℝ) ^ (j + 1) := by
        have h1 : (2 * m - (j + 1)) + (j + 1) = 2 * m := by omega
        have hmul : (-1 : ℝ) ^ (2 * m - (j + 1)) * (-1 : ℝ) ^ (j + 1) = 1 := by
          rw [← pow_add, h1]; simp [pow_mul]
        have hsq : (-1 : ℝ) ^ (j + 1) * (-1 : ℝ) ^ (j + 1) = 1 := by
          rw [← pow_add, show (j + 1) + (j + 1) = 2 * (j + 1) by omega]; simp [pow_mul]
        linear_combination (-1 : ℝ) ^ (j + 1) * hmul - (-1 : ℝ) ^ (2 * m - (j + 1)) * hsq
      rw [hidx, hpar]
    rw [hleft_m, hright_2m, hmid]
    have hcomb : (∑ j ∈ range (2 * k), (-1 : ℝ) ^ (j + 1) * ratio (j + 1)) +
        (∑ j ∈ range (2 * k), (-1 : ℝ) ^ (j + 1) * ratio (2 * m - (j + 1))) =
        ∑ j ∈ range (2 * k), (-1 : ℝ) ^ (j + 1) * (ratio (j + 1) + ratio (2 * m - (j + 1))) := by
      rw [← sum_add_distrib]
      refine sum_congr rfl fun j _ => by ring
    linarith
  have hlast : (1 / (Nat.fib (2 * m) : ℝ)) * (ratio (2 * m) - ratio m) =
      1 / (Nat.fib (2 * m) : ℝ) ^ 2 := by
    have hdoc := docagne m m
    have h1 : m + m = 2 * m := by omega
    rw [h1] at hdoc
    have hsign : (-1 : ℝ) ^ (m + 1) = 1 := by
      rw [show m + 1 = 2 * (k + 1) by omega]; simp [pow_mul]
    rw [hsign, one_mul] at hdoc
    have hfm : (Nat.fib m : ℝ) ≠ 0 := fib_ne_zero_real (by omega)
    have hf2m : (Nat.fib (2 * m) : ℝ) ≠ 0 := fib_ne_zero_real (by omega)
    unfold ratio
    field_simp
    linear_combination hdoc
  have hsum_zero : ∑ j ∈ range (2 * k), (-1 : ℝ) ^ (j + 1) * (1 / (Nat.fib (2 * m) : ℝ)) = 0 := by
    rw [← sum_mul]
    have := sum_neg_one_pow_even k 1
    have hrew : ∑ j ∈ range (2 * k), (-1 : ℝ) ^ (j + 1) = ∑ j ∈ range (2 * k), (-1 : ℝ) ^ (1 + j) :=
      sum_congr rfl fun j _ => by rw [Nat.add_comm]
    rw [hrew, this, zero_mul]
  have hval : 1 / OMA.S_oeis_a007598.a (2 * m) -
      ∑ i ∈ range m, (if i + 1 = m then (0 : ℝ) else
        1 / (OMA.S_oeis_a007598.a (i + 1) + (-1 : ℝ) ^ (i + 1) * OMA.S_oeis_a007598.a m)) =
      (1 / (Nat.fib (2 * m) : ℝ)) * ∑ j ∈ range (2 * m), (-1 : ℝ) ^ (j + 1) * ratio (j + 1) := by
    rw [hhead_split, htail_split, mul_add (1 / (Nat.fib (2 * m) : ℝ)), hlast, mul_sum]
    have hpair_sum : ∑ j ∈ range (2 * k), (1 / (Nat.fib (2 * m) : ℝ)) *
        ((-1 : ℝ) ^ (j + 1) * (ratio (j + 1) + ratio (2 * m - (j + 1)))) =
        ∑ j ∈ range (2 * k), (-1 : ℝ) ^ (j + 1) / ((Nat.fib (j + 1) : ℝ) * (Nat.fib (2 * m - (j + 1)) : ℝ)) := by
      have h1 : ∑ j ∈ range (2 * k), (1 / (Nat.fib (2 * m) : ℝ)) *
          ((-1 : ℝ) ^ (j + 1) * (ratio (j + 1) + ratio (2 * m - (j + 1)))) =
          ∑ j ∈ range (2 * k), ((-1 : ℝ) ^ (j + 1) / ((Nat.fib (j + 1) : ℝ) * (Nat.fib (2 * m - (j + 1)) : ℝ)) +
            (-1 : ℝ) ^ (j + 1) * (1 / (Nat.fib (2 * m) : ℝ))) := by
        refine sum_congr rfl fun j hj => ?_
        rw [mem_range] at hj
        have hp := pair_ratio_identity (m := m) (j := j + 1) (by omega) (by omega)
        linear_combination (-1 : ℝ) ^ (j + 1) * hp
      rw [h1, sum_add_distrib, hsum_zero, add_zero]
    rw [hpair_sum]
    have hcancel : ∑ j ∈ range (2 * k),
        (-(-1 : ℝ) ^ (j + 1)) / ((Nat.fib (j + 1) : ℝ) * (Nat.fib (2 * m - (j + 1)) : ℝ)) =
        -∑ j ∈ range (2 * k),
          (-1 : ℝ) ^ (j + 1) / ((Nat.fib (j + 1) : ℝ) * (Nat.fib (2 * m - (j + 1)) : ℝ)) := by
      rw [← sum_neg_distrib]
      refine sum_congr rfl fun j _ => by ring
    rw [hcancel]
    unfold OMA.S_oeis_a007598.a
    ring
  rw [hval]
  exact hhs

end OMA.OeisA007598Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a007598.main :=
  ⟨OMA.OeisA007598Proof.part1, OMA.OeisA007598Proof.part2, OMA.OeisA007598Proof.part3⟩
