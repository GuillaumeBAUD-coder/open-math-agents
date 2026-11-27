import OMAReductions.R_FlintCooksonHills_cookson_hills_series_converges_R1
import Mathlib

-- Step FlintCooksonHills.cookson_hills_series_converges.R1.H2: hypothesis H2 of reduction FlintCooksonHills.cookson_hills_series_converges.R1
-- Credit: @senamakel
-- H2 := ∀ α c ν : ℝ, 0 < c → 1 < ν → ν < 5 / 2 →     (∀ q : ℕ, 0 < q →       c * (q : ℝ) ^ (1 - ν) ≤ |(q : ℝ) * α - (round ((q : ℝ) * α) : ℝ)|) →     Summable (fun q : ℕ =>       1 / ((q : ℝ) ^ 3 * |(q : ℝ) * α - (round ((q : ℝ) * α) : ℝ)| ^ 2))

-- Dyadic spacing argument adapted from the Apache-2.0 Lean files of openai/math (PiExponent analysis).

namespace OMA_CooksonH2

open scoped BigOperators

noncomputable def integerDistance (x : ℝ) : ℝ := |x - (round x : ℝ)|

theorem integerDistance_nonneg (x : ℝ) : 0 ≤ integerDistance x := abs_nonneg _

theorem integerDistance_le (x : ℝ) (p : ℤ) : integerDistance x ≤ |x - p| :=
  round_le x p

theorem integerDistance_le_half (x : ℝ) : integerDistance x ≤ 1 / 2 :=
  abs_sub_round x

theorem integerDistance_mul_pos {α : ℝ} (hα : Irrational α) {q : ℕ}
    (hq : 0 < q) : 0 < integerDistance (q * α) := by
  exact abs_pos.mpr (sub_ne_zero.mpr ((hα.natCast_mul hq.ne').ne_int _))

theorem finite_relative_lower_bound (f g : ℕ → ℝ)
    (hf : ∀ n, 0 < f n) (hg : ∀ n, 0 < g n) (N : ℕ) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ n < N, c * g n ≤ f n := by
  induction N with
  | zero => exact ⟨1, zero_lt_one, le_rfl, by simp⟩
  | succ N ih =>
    rcases ih with ⟨c, hc, hc1, hbound⟩
    refine ⟨min c (f N / g N), lt_min hc (div_pos (hf N) (hg N)),
      (min_le_left _ _).trans hc1, ?_⟩
    intro n hn
    rcases Nat.lt_succ_iff_lt_or_eq.mp hn with hn | rfl
    · exact (mul_le_mul_of_nonneg_right (min_le_left _ _) (hg n).le).trans (hbound n hn)
    · exact (le_div_iff₀ (hg n)).mp (min_le_right _ _)

theorem uniform_relative_lower_bound (f g : ℕ → ℝ)
    (hf : ∀ n, 0 < f n) (hg : ∀ n, 0 < g n)
    (htail : ∃ N : ℕ, ∀ n, N ≤ n → g n ≤ f n) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ n, c * g n ≤ f n := by
  rcases htail with ⟨N, hN⟩
  rcases finite_relative_lower_bound f g hf hg N with ⟨c, hc, hc1, hbound⟩
  refine ⟨c, hc, hc1, fun n => ?_⟩
  by_cases hn : n < N
  · exact hbound n hn
  · exact (mul_le_of_le_one_left (hg n).le hc1).trans (hN n (Nat.le_of_not_gt hn))

theorem integerDistance_lower_bound {α ν : ℝ} {q : ℕ} (hq : 0 < q)
    (h : ∀ p : ℤ, (q : ℝ) ^ (-ν) ≤ |α - p / (q : ℝ)|) :
    (q : ℝ) ^ (1 - ν) ≤ integerDistance (q * α) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hh := mul_le_mul_of_nonneg_left (h (round ((q : ℝ) * α))) hqR.le
  have heq : (q : ℝ) * |α - (round ((q : ℝ) * α) : ℝ) / q| =
      integerDistance (q * α) := by
    calc
      _ = |(q : ℝ) * (α - (round ((q : ℝ) * α) : ℝ) / q)| := by
        rw [abs_mul, abs_of_pos hqR]
      _ = integerDistance (q * α) := by
        unfold integerDistance
        congr 1
        field_simp
  rw [heq] at hh
  simpa only [sub_eq_add_neg, Real.rpow_add hqR, Real.rpow_one] using hh

theorem uniform_integerDistance_lower_bound {α ν : ℝ} (hα : Irrational α)
    (h : ∃ Q : ℕ, ∀ q : ℕ, Q ≤ q → 0 < q →
      ∀ p : ℤ, (q : ℝ) ^ (-ν) ≤ |α - p / (q : ℝ)|) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ q : ℕ, 0 < q →
      c * (q : ℝ) ^ (1 - ν) ≤ integerDistance (q * α) := by
  let f : ℕ → ℝ := fun n => integerDistance ((n + 1 : ℕ) * α)
  let g : ℕ → ℝ := fun n => ((n + 1 : ℕ) : ℝ) ^ (1 - ν)
  have hf : ∀ n, 0 < f n := fun n => integerDistance_mul_pos hα (Nat.succ_pos n)
  have hg : ∀ n, 0 < g n := fun n => Real.rpow_pos_of_pos (by positivity) _
  have htail : ∃ N : ℕ, ∀ n, N ≤ n → g n ≤ f n := by
    rcases h with ⟨Q, hQ⟩
    exact ⟨Q, fun n hn => integerDistance_lower_bound (Nat.succ_pos n)
      (hQ (n + 1) (Nat.le_trans hn (Nat.le_succ n)) (Nat.succ_pos n))⟩
  rcases uniform_relative_lower_bound f g hf hg htail with ⟨c, hc, hc1, hbound⟩
  refine ⟨c, hc, hc1, ?_⟩
  rintro (_ | q) hq
  · exact False.elim (Nat.not_lt_zero _ hq)
  · exact hbound q

 theorem dyadic_block_bound_algebra {c K nu : ℝ} (hc : 0 < c) (hK : 0 < K) :
    4 / (K ^ 3 * (c * (2 * K) ^ (1 - nu)) ^ 2) =
      (4 / (c ^ 2 * (2 : ℝ) ^ (2 * (1 - nu)))) * K ^ (2 * nu - 5) := by
  have hsq (x : ℝ) (hx : 0 ≤ x) :
      (x ^ (1 - nu)) ^ (2 : ℕ) = x ^ (2 * (1 - nu)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
    congr 1
    ring
  have hprod : K ^ (3 : ℕ) * K ^ (2 * (1 - nu)) = K ^ (5 - 2 * nu) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hK]
    congr 1
    ring
  have hden : K ^ 3 * (c * (2 * K) ^ (1 - nu)) ^ 2 =
      (c ^ 2 * (2 : ℝ) ^ (2 * (1 - nu))) * K ^ (5 - 2 * nu) := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hK.le, mul_pow, mul_pow,
      hsq 2 (by norm_num), hsq K hK.le]
    calc
      _ = (c ^ 2 * (2 : ℝ) ^ (2 * (1 - nu))) *
          (K ^ 3 * K ^ (2 * (1 - nu))) := by ring
      _ = _ := by rw [hprod]
  have hcoeff : c ^ 2 * (2 : ℝ) ^ (2 * (1 - nu)) ≠ 0 :=
    (mul_pos (pow_pos hc 2) (Real.rpow_pos_of_pos (by norm_num) _)).ne'
  have hKpow : K ^ (5 - 2 * nu) ≠ 0 := (Real.rpow_pos_of_pos hK _).ne'
  rw [hden]
  apply (div_eq_iff (mul_ne_zero hcoeff hKpow)).2
  rw [mul_mul_mul_comm, div_mul_cancel₀ _ hcoeff, ← Real.rpow_add hK]
  have hexponent : 2 * nu - 5 + (5 - 2 * nu) = 0 := by ring
  rw [hexponent, Real.rpow_zero, mul_one]

 theorem dyadic_rpow_eq_geometric (nu : ℝ) (k : ℕ) :
    ((2 : ℝ) ^ k) ^ (2 * nu - 5) = ((2 : ℝ) ^ (2 * nu - 5)) ^ k := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
    mul_comm, Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]

 theorem dyadic_geometric_ratio_pos (nu : ℝ) :
    0 < (2 : ℝ) ^ (2 * nu - 5) := Real.rpow_pos_of_pos (by norm_num) _

 theorem dyadic_geometric_ratio_lt_one {nu : ℝ} (hnu : nu < 5 / 2) :
    (2 : ℝ) ^ (2 * nu - 5) < 1 := by
  apply Real.rpow_lt_one_of_one_lt_of_neg
  · norm_num
  · linarith

 theorem summable_dyadic_block_bound {c nu : ℝ} (hc : 0 < c) (hnu : nu < 5 / 2) :
    Summable (fun k : ℕ =>
      4 / (((2 : ℝ) ^ k) ^ (3 : ℕ) *
        (c * (2 * (2 : ℝ) ^ k) ^ (1 - nu)) ^ (2 : ℕ))) := by
  have hg := summable_geometric_of_lt_one (dyadic_geometric_ratio_pos nu).le
    (dyadic_geometric_ratio_lt_one hnu)
  have hm := hg.mul_left (4 / (c ^ 2 * (2 : ℝ) ^ (2 * (1 - nu))))
  apply hm.congr
  intro k
  rw [dyadic_block_bound_algebra hc (pow_pos (by norm_num) k),
    dyadic_rpow_eq_geometric]

section
open Finset

theorem sum_range_two_pow_eq_dyadic (f : ℕ → ℝ) (k : ℕ) :
    ∑ q ∈ range (2 ^ k), f q =
      f 0 + ∑ j ∈ range k, ∑ q ∈ Ico (2 ^ j) (2 ^ (j + 1)), f q := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk : 2 ^ k ≤ 2 ^ (k + 1) :=
      Nat.pow_le_pow_right (by norm_num) (Nat.le_succ k)
    rw [← sum_range_add_sum_Ico f hk, ih, sum_range_succ]
    rw [add_assoc]

theorem summable_of_dyadic_norm_blocks {f g : ℕ → ℝ}
    (hg : Summable g)
    (hblock : ∀ k, ∑ q ∈ Ico (2 ^ k) (2 ^ (k + 1)), ‖f q‖ ≤ g k) :
    Summable f := by
  have hg0 : ∀ k, 0 ≤ g k := fun k =>
    (sum_nonneg fun _ _ => norm_nonneg _).trans (hblock k)
  apply Summable.of_norm
  apply summable_of_sum_range_le (fun _ => norm_nonneg _) (c := ‖f 0‖ + ∑' k, g k)
  intro n
  calc
    ∑ q ∈ range n, ‖f q‖ ≤ ∑ q ∈ range (2 ^ n), ‖f q‖ :=
      sum_le_sum_of_subset_of_nonneg (range_mono (Nat.le_of_lt n.lt_two_pow_self))
        (fun _ _ _ => norm_nonneg _)
    _ = ‖f 0‖ + ∑ k ∈ range n, ∑ q ∈ Ico (2 ^ k) (2 ^ (k + 1)), ‖f q‖ :=
      sum_range_two_pow_eq_dyadic _ _
    _ ≤ ‖f 0‖ + ∑ k ∈ range n, g k :=
      add_le_add le_rfl (sum_le_sum fun k _ => hblock k)
    _ ≤ ‖f 0‖ + ∑' k, g k :=
      add_le_add le_rfl (hg.sum_le_tsum (range n) (fun k _ => hg0 k))

theorem summable_of_dyadic_blocks {f g : ℕ → ℝ}
    (hf : ∀ q, 0 < q → 0 ≤ f q) (hg : Summable g)
    (hblock : ∀ k, ∑ q ∈ Ico (2 ^ k) (2 ^ (k + 1)), f q ≤ g k) :
    Summable f := by
  apply summable_of_dyadic_norm_blocks hg
  intro k
  calc
    ∑ q ∈ Ico (2 ^ k) (2 ^ (k + 1)), ‖f q‖ =
        ∑ q ∈ Ico (2 ^ k) (2 ^ (k + 1)), f q := by
      apply sum_congr rfl
      intro q hq
      exact Real.norm_of_nonneg (hf q ((pow_pos (by norm_num) k).trans_le (mem_Ico.mp hq).1))
    _ ≤ g k := hblock k

theorem summable_of_dyadic_geometric {f : ℕ → ℝ} {M r : ℝ}
    (hf : ∀ q, 0 < q → 0 ≤ f q) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hblock : ∀ k, ∑ q ∈ Ico (2 ^ k) (2 ^ (k + 1)), f q ≤ M * r ^ k) :
    Summable f :=
  summable_of_dyadic_blocks hf ((summable_geometric_of_lt_one hr0 hr1).mul_left M) hblock

end

open scoped BigOperators

theorem lower_bound_of_spacing {N : ℕ} (x : Fin N → ℝ) {d : ℝ}
    (hmin : ∀ i, d ≤ x i)
    (hsep : ∀ i j, i < j → d ≤ x j - x i) :
    ∀ i, ((i.val : ℝ) + 1) * d ≤ x i := by
  have aux : ∀ k (hk : k < N), ((k : ℝ) + 1) * d ≤ x ⟨k, hk⟩ := by
    intro k
    induction k with
    | zero =>
      intro hk
      simpa using hmin ⟨0, hk⟩
    | succ k ih =>
      intro hk
      have hk' : k < N := Nat.lt_trans (Nat.lt_succ_self k) hk
      have hp := ih hk'
      have hs := hsep ⟨k, hk'⟩ ⟨k + 1, hk⟩ (by simp)
      push_cast
      linarith
  intro i
  exact aux i.val i.isLt

theorem sum_inv_succ_sq_le_two_sub (N : ℕ) :
    (∑ k ∈ Finset.range N, 1 / ((k : ℝ) + 1) ^ 2) ≤
      2 - 2 / ((N : ℝ) + 1) := by
  induction N with
  | zero => norm_num
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
    have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    have hN2 : (0 : ℝ) < (N : ℝ) + 2 := by positivity
    have hterm : 1 / ((N : ℝ) + 1) ^ 2 ≤
        2 / ((N : ℝ) + 1) - 2 / ((N : ℝ) + 2) := by
      field_simp
      nlinarith
    push_cast
    have e : (N : ℝ) + 1 + 1 = (N : ℝ) + 2 := by ring
    rw [e]
    linarith [add_le_add ih hterm]

theorem sum_inv_succ_sq_le_two (N : ℕ) :
    (∑ k ∈ Finset.range N, 1 / ((k : ℝ) + 1) ^ 2) ≤ 2 := by
  have h := sum_inv_succ_sq_le_two_sub N
  have hnonneg : 0 ≤ 2 / ((N : ℝ) + 1) := by positivity
  linarith

theorem sum_inv_sq_le_two_div_sq_of_spacing {N : ℕ}
    (x : Fin N → ℝ) {d : ℝ} (hd : 0 < d)
    (hmin : ∀ i, d ≤ x i)
    (hsep : ∀ i j, i < j → d ≤ x j - x i) :
    (∑ i, 1 / (x i) ^ 2) ≤ 2 / d ^ 2 := by
  have hlower := lower_bound_of_spacing x hmin hsep
  calc
    (∑ i, 1 / (x i) ^ 2) ≤
        ∑ i : Fin N, 1 / ((((i.val : ℝ) + 1) * d) ^ 2) := by
      apply Finset.sum_le_sum
      intro i _
      have hpos : 0 < ((i.val : ℝ) + 1) * d := by positivity
      exact one_div_le_one_div_of_le (sq_pos_of_pos hpos)
        (pow_le_pow_left₀ hpos.le (hlower i) 2)
    _ = (1 / d ^ 2) * ∑ i : Fin N, 1 / ((i.val : ℝ) + 1) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [mul_pow, one_div_mul_one_div]
      ring
    _ ≤ (1 / d ^ 2) * 2 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2)]
      exact sum_inv_succ_sq_le_two N
    _ = 2 / d ^ 2 := by ring

theorem sum_inv_sq_le_two_div_sq (s : Finset ℝ) {d : ℝ} (hd : 0 < d)
    (hmin : ∀ x ∈ s, d ≤ x)
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → d ≤ |x - y|) :
    (∑ x ∈ s, 1 / x ^ 2) ≤ 2 / d ^ 2 := by
  classical
  let e := s.orderEmbOfFin rfl
  have hmem : ∀ i, e i ∈ s := fun i => s.orderEmbOfFin_mem rfl i
  have hstep : ∀ i j, i < j → d ≤ e j - e i := by
    intro i j hij
    have hij' : e i < e j := e.strictMono hij
    have h := hsep (e j) (hmem j) (e i) (hmem i) (ne_of_gt hij')
    rwa [abs_of_pos (sub_pos.mpr hij')] at h
  have hbound := sum_inv_sq_le_two_div_sq_of_spacing e hd
    (fun i => hmin (e i) (hmem i)) hstep
  have hsum : (∑ i : Fin s.card, 1 / (e i) ^ 2) = ∑ x ∈ s, 1 / x ^ 2 := by
    have himage : Finset.univ.image e = s := s.image_orderEmbOfFin_univ rfl
    calc
      _ = ∑ y ∈ Finset.univ.image e, 1 / y ^ 2 :=
        (Finset.sum_image e.injective.injOn).symm
      _ = _ := congrArg (fun t : Finset ℝ => ∑ y ∈ t, 1 / y ^ 2) himage
  rwa [hsum] at hbound

theorem sum_inv_sq_le_two_div_sq_indexed {ι : Type*}
    (rows : Finset ι) (x : ι → ℝ) {d : ℝ} (hd : 0 < d)
    (hmin : ∀ i ∈ rows, d ≤ x i)
    (hsep : ∀ i ∈ rows, ∀ j ∈ rows, i ≠ j → d ≤ |x i - x j|) :
    (∑ i ∈ rows, 1 / (x i) ^ 2) ≤ 2 / d ^ 2 := by
  classical
  have hinj : Set.InjOn x (rows : Set ι) := by
    intro i hi j hj h
    by_contra hij
    have hs := hsep i hi j hj hij
    rw [h, sub_self, abs_zero] at hs
    exact (not_le_of_gt hd) hs
  have h := sum_inv_sq_le_two_div_sq (rows.image x) hd
    (by intro a ha; obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha; exact hmin i hi)
    (by
      intro a ha b hb hab
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hb
      exact hsep i hi j hj (fun hij => hab (congrArg x hij)))
  rwa [Finset.sum_image hinj] at h

open scoped BigOperators

noncomputable def centeredResidue (alpha : ℝ) (q : ℕ) : ℝ :=
  (q : ℝ) * alpha - (round ((q : ℝ) * alpha) : ℝ)

theorem abs_centeredResidue (alpha : ℝ) (q : ℕ) :
    |centeredResidue alpha q| = integerDistance ((q : ℝ) * alpha) := rfl

theorem integerDistance_sub_le (x y : ℝ) :
    integerDistance (x - y) ≤ |(x - (round x : ℝ)) - (y - (round y : ℝ))| := by
  have h := integerDistance_le (x - y) (round x - round y)
  push_cast at h
  convert h using 1
  congr 1
  ring

theorem centeredResidue_separation {alpha c nu : ℝ} (hc : 0 < c) (hnu : 1 < nu)
    (hlower : ∀ q : ℕ, 0 < q →
      c * (q : ℝ) ^ (1 - nu) ≤ integerDistance ((q : ℝ) * alpha))
    {K q r : ℕ} (hq : q ∈ Finset.Ico K (2 * K))
    (hr : r ∈ Finset.Ico K (2 * K)) (hqr : q < r) :
    c * (2 * (K : ℝ)) ^ (1 - nu) ≤
      |centeredResidue alpha r - centeredResidue alpha q| := by
  have hdiff : 0 < r - q := Nat.sub_pos_of_lt hqr
  have hdiffR : (0 : ℝ) < (r - q : ℕ) := by exact_mod_cast hdiff
  have hdiffle : ((r - q : ℕ) : ℝ) ≤ 2 * (K : ℝ) := by
    have hqK := (Finset.mem_Ico.mp hq).1
    have hrK := (Finset.mem_Ico.mp hr).2
    have hlt : r - q < K := by omega
    exact_mod_cast hlt.le.trans (by omega : K ≤ 2 * K)
  have hpower := Real.rpow_le_rpow_of_nonpos hdiffR hdiffle (by linarith : 1 - nu ≤ 0)
  have hsep := integerDistance_sub_le ((r : ℝ) * alpha) ((q : ℝ) * alpha)
  have hcast : ((r - q : ℕ) : ℝ) * alpha = (r : ℝ) * alpha - (q : ℝ) * alpha := by
    rw [Nat.cast_sub hqr.le]
    ring
  calc
    c * (2 * (K : ℝ)) ^ (1 - nu) ≤ c * ((r - q : ℕ) : ℝ) ^ (1 - nu) :=
      mul_le_mul_of_nonneg_left hpower hc.le
    _ ≤ integerDistance (((r - q : ℕ) : ℝ) * alpha) := hlower (r - q) hdiff
    _ ≤ |centeredResidue alpha r - centeredResidue alpha q| := by
      rw [hcast]
      exact hsep

theorem integerDistance_block_lower {alpha c nu : ℝ} (hc : 0 < c) (hnu : 1 < nu)
    (hlower : ∀ q : ℕ, 0 < q →
      c * (q : ℝ) ^ (1 - nu) ≤ integerDistance ((q : ℝ) * alpha))
    {K q : ℕ} (hK : 0 < K) (hq : q ∈ Finset.Ico K (2 * K)) :
    c * (2 * (K : ℝ)) ^ (1 - nu) ≤ integerDistance ((q : ℝ) * alpha) := by
  have hqpos : 0 < q := hK.trans_le (Finset.mem_Ico.mp hq).1
  have hqR : (0 : ℝ) < q := by exact_mod_cast hqpos
  have hqle : (q : ℝ) ≤ 2 * (K : ℝ) := by exact_mod_cast (Finset.mem_Ico.mp hq).2.le
  exact (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_nonpos hqR hqle (by linarith : 1 - nu ≤ 0)) hc.le).trans
    (hlower q hqpos)

theorem integerDistance_block_sum {alpha c nu : ℝ} (hc : 0 < c) (hnu : 1 < nu)
    (hlower : ∀ q : ℕ, 0 < q →
      c * (q : ℝ) ^ (1 - nu) ≤ integerDistance ((q : ℝ) * alpha))
    {K : ℕ} (hK : 0 < K) :
    (∑ q ∈ Finset.Ico K (2 * K), 1 / (integerDistance ((q : ℝ) * alpha)) ^ 2) ≤
      4 / (c * (2 * (K : ℝ)) ^ (1 - nu)) ^ 2 := by
  classical
  let rows := Finset.Ico K (2 * K)
  let d : ℝ := c * (2 * (K : ℝ)) ^ (1 - nu)
  have hd : 0 < d := by dsimp [d]; positivity
  have hmin : ∀ q ∈ rows, d ≤ integerDistance ((q : ℝ) * alpha) :=
    fun q hq => integerDistance_block_lower hc hnu hlower hK hq
  have hsep : ∀ q ∈ rows, ∀ r ∈ rows, q ≠ r →
      d ≤ |centeredResidue alpha q - centeredResidue alpha r| := by
    intro q hq r hr hqr
    rcases lt_or_gt_of_ne hqr with hqr | hrq
    · simpa only [abs_sub_comm] using centeredResidue_separation hc hnu hlower hq hr hqr
    · exact centeredResidue_separation hc hnu hlower hr hq hrq
  have hpos := sum_inv_sq_le_two_div_sq_indexed
    (rows.filter fun q => 0 ≤ centeredResidue alpha q)
    (fun q => integerDistance ((q : ℝ) * alpha)) hd
    (fun q hq => hmin q (Finset.mem_filter.mp hq).1)
    (by
      intro q hq r hr hqr
      change d ≤ abs (abs (centeredResidue alpha q) - abs (centeredResidue alpha r))
      rw [abs_of_nonneg (Finset.mem_filter.mp hq).2,
        abs_of_nonneg (Finset.mem_filter.mp hr).2]
      exact hsep q (Finset.mem_filter.mp hq).1 r (Finset.mem_filter.mp hr).1 hqr)
  have hneg := sum_inv_sq_le_two_div_sq_indexed
    (rows.filter fun q => ¬ 0 ≤ centeredResidue alpha q)
    (fun q => integerDistance ((q : ℝ) * alpha)) hd
    (fun q hq => hmin q (Finset.mem_filter.mp hq).1)
    (by
      intro q hq r hr hqr
      change d ≤ abs (abs (centeredResidue alpha q) - abs (centeredResidue alpha r))
      rw [abs_of_neg (lt_of_not_ge (Finset.mem_filter.mp hq).2),
        abs_of_neg (lt_of_not_ge (Finset.mem_filter.mp hr).2), neg_sub_neg, abs_sub_comm]
      exact hsep q (Finset.mem_filter.mp hq).1 r (Finset.mem_filter.mp hr).1 hqr)
  change (∑ q ∈ rows, 1 / (integerDistance ((q : ℝ) * alpha)) ^ 2) ≤ 4 / d ^ 2
  rw [← Finset.sum_filter_add_sum_filter_not rows (fun q => 0 ≤ centeredResidue alpha q)]
  calc
    _ ≤ 2 / d ^ 2 + 2 / d ^ 2 := add_le_add hpos hneg
    _ = _ := by ring

theorem inverse_cube_integerDistance_block_sum {alpha c nu : ℝ}
    (hc : 0 < c) (hnu : 1 < nu)
    (hlower : ∀ q : ℕ, 0 < q →
      c * (q : ℝ) ^ (1 - nu) ≤ integerDistance ((q : ℝ) * alpha))
    {K : ℕ} (hK : 0 < K) :
    (∑ q ∈ Finset.Ico K (2 * K),
      1 / ((q : ℝ) ^ 3 * (integerDistance ((q : ℝ) * alpha)) ^ 2)) ≤
      4 / ((K : ℝ) ^ 3 * (c * (2 * (K : ℝ)) ^ (1 - nu)) ^ 2) := by
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  calc
    _ ≤ ∑ q ∈ Finset.Ico K (2 * K),
        (1 / (K : ℝ) ^ 3) * (1 / (integerDistance ((q : ℝ) * alpha)) ^ 2) := by
      apply Finset.sum_le_sum
      intro q hq
      have hKq : (K : ℝ) ≤ q := by exact_mod_cast (Finset.mem_Ico.mp hq).1
      have hdist : 0 < integerDistance ((q : ℝ) * alpha) :=
        (mul_pos hc (Real.rpow_pos_of_pos (by positivity) _)).trans_le
          (integerDistance_block_lower hc hnu hlower hK hq)
      rw [one_div_mul_one_div]
      exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
        (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hKR.le hKq 3) (sq_nonneg _))
    _ = (1 / (K : ℝ) ^ 3) *
        ∑ q ∈ Finset.Ico K (2 * K), 1 / (integerDistance ((q : ℝ) * alpha)) ^ 2 := by
      rw [Finset.mul_sum]
    _ ≤ (1 / (K : ℝ) ^ 3) * (4 / (c * (2 * (K : ℝ)) ^ (1 - nu)) ^ 2) :=
      mul_le_mul_of_nonneg_left (integerDistance_block_sum hc hnu hlower hK) (by positivity)
    _ = _ := by ring

theorem summable_inverse_cube_integerDistance {alpha c nu : ℝ}
    (hc : 0 < c) (hnu1 : 1 < nu) (hnu2 : nu < 5 / 2)
    (hlower : ∀ q : ℕ, 0 < q →
      c * (q : ℝ) ^ (1 - nu) ≤ integerDistance ((q : ℝ) * alpha)) :
    Summable (fun q : ℕ =>
      1 / ((q : ℝ) ^ 3 * (integerDistance ((q : ℝ) * alpha)) ^ 2)) := by
  apply summable_of_dyadic_blocks (fun q hq => by positivity)
    (summable_dyadic_block_bound hc hnu2)
  intro k
  have hblock := inverse_cube_integerDistance_block_sum hc hnu1 hlower
    (pow_pos (by norm_num : (0 : ℕ) < 2) k)
  have hend : 2 * 2 ^ k = 2 ^ (k + 1) := by rw [pow_succ, Nat.mul_comm]
  rw [hend] at hblock
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using hblock

end OMA_CooksonH2

theorem OMA.solution : OMA.R_FlintCooksonHills_cookson_hills_series_converges_R1.H2 := by
  intro _ _ _ hc h1 h2 hl
  exact OMA_CooksonH2.summable_inverse_cube_integerDistance hc h1 h2 hl
