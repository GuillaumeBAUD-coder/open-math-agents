import OMAStatements.S_oeis_a010786

namespace OMA.S_oeis_a010786

open Real Filter Topology
open scoped BigOperators

private noncomputable def logWeight (j : ℕ) : ℝ :=
  (log ((j : ℝ) + 2) - log ((j : ℝ) + 1)) / ((j : ℝ) + 2)

private noncomputable def unitWeight (j : ℕ) : ℝ :=
  1 / ((j : ℝ) + 1) - 1 / ((j : ℝ) + 2)

private theorem unit_hasSum : HasSum unitWeight 1 := by
  have hpos (j : ℕ) : 0 ≤ unitWeight j := by
    unfold unitWeight
    exact sub_nonneg.mpr (one_div_le_one_div_of_le (by positivity) (by linarith))
  have hsum (n : ℕ) : ∑ j ∈ Finset.range n, unitWeight j = 1 - 1 / ((n : ℝ) + 1) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [unitWeight, Nat.cast_succ]
      ring
  apply (hasSum_iff_tendsto_nat_of_nonneg hpos 1).mpr
  simp_rw [hsum]
  simpa only [sub_zero] using
    (tendsto_const_nhds (x := (1 : ℝ))).sub tendsto_one_div_add_atTop_nhds_zero_nat

private theorem logWeight_pos (j : ℕ) : 0 < logWeight j := by
  unfold logWeight
  exact div_pos (sub_pos.mpr (Real.log_lt_log (by positivity) (by linarith))) (by positivity)

private theorem logWeight_lt_unit (j : ℕ) : logWeight j < unitWeight j := by
  let a : ℝ := j + 1
  let b : ℝ := j + 2
  have ha : 0 < a := by positivity
  have hb : 0 < b := by positivity
  have hba : b = a + 1 := by dsimp [a, b]; ring
  have hne : b / a ≠ 1 := by
    intro h
    have he := (div_eq_iff ha.ne').mp h
    linarith
  have h := Real.log_lt_sub_one_of_pos (div_pos hb ha) hne
  have h' := div_lt_div_of_pos_right h hb
  rw [Real.log_div hb.ne' ha.ne'] at h'
  change (log b - log a) / b < 1 / a - 1 / b
  have he : (b / a - 1) / b = 1 / a - 1 / b := by
    field_simp [ha.ne', hb.ne']
  rwa [he] at h'

private theorem logWeight_summable : Summable logWeight :=
  .of_nonneg_of_le (fun j => (logWeight_pos j).le) (fun j => (logWeight_lt_unit j).le)
    unit_hasSum.summable

private noncomputable def seriesTerm (j n : ℕ) : ℝ :=
  (1 / ((j : ℝ) + 2))^(n+2) / ((n : ℝ) + 1)

private theorem seriesTerm_nonnegative (j n : ℕ) : 0 ≤ seriesTerm j n := by
  unfold seriesTerm
  positivity

private theorem seriesTerm_hasSum_row (j : ℕ) :
    HasSum (seriesTerm j) (logWeight j) := by
  let a : ℝ := j + 1
  let b : ℝ := j + 2
  have ha : 0 < a := by positivity
  have hb : 0 < b := by positivity
  have hba : b = a + 1 := by dsimp [a, b]; ring
  have hsmall : |(1 : ℝ) / b| < 1 := by
    rw [abs_of_nonneg (by positivity), div_lt_iff₀ hb]
    dsimp [b]
    linarith [Nat.cast_nonneg (α := ℝ) j]
  have h := (Real.hasSum_pow_div_log_of_abs_lt_one hsmall).mul_right (1 / b)
  have he : 1 - 1 / b = a / b := by
    field_simp [hb.ne']
    linarith
  have hl : (-log (1 - 1 / b)) * (1 / b) = logWeight j := by
    rw [he, Real.log_div ha.ne' hb.ne']
    change -(log a - log b) * (1 / b) = (log b - log a) / b
    ring
  rw [hl] at h
  refine h.congr_fun fun n => ?_
  change (1 / b)^(n+2) / ((n : ℝ)+1) =
    ((1 / b)^(n+1) / ((n : ℝ)+1)) * (1 / b)
  rw [show n+2 = (n+1)+1 by omega, pow_succ]
  ring

private theorem zeta_tail_hasSum (n : ℕ) :
    HasSum (fun j : ℕ => 1 / (((j : ℝ) + 2)^(n+2)))
      (riemannZeta ((n : ℂ) + 2) - 1).re := by
  let k : ℕ := n + 2
  have hk : 1 < k := by omega
  have hkre : (1 : ℝ) < (k : ℂ).re := by
    simp only [Complex.natCast_re]
    exact_mod_cast hk
  have hsum₀ : Summable (fun j : ℕ => 1 / (j : ℂ) ^ k) := by
    simpa only [Complex.cpow_natCast] using Complex.summable_one_div_nat_cpow.mpr hkre
  have hsum : HasSum (fun j : ℕ => 1 / (j : ℂ) ^ k) (riemannZeta (k : ℂ)) := by
    rw [zeta_nat_eq_tsum_of_gt_one hk]
    exact hsum₀.hasSum
  have hfirst : ∑ j ∈ Finset.range 2, 1 / (j : ℂ)^k = 1 := by
    norm_num [Finset.sum_range_succ, zero_pow (show k ≠ 0 by omega)]
  have htail : HasSum (fun j : ℕ => 1 / ((j + 2 : ℕ) : ℂ)^k) (riemannZeta (k : ℂ) - 1) := by
    apply (hasSum_nat_add_iff 2 (f := fun j : ℕ => 1 / (j : ℂ)^k)).mpr
    simpa only [hfirst, sub_add_cancel] using hsum
  have hr := Complex.hasSum_re htail
  have he (j : ℕ) : (1 / ((j + 2 : ℕ) : ℂ)^k).re = 1 / (((j : ℝ) + 2)^(n+2)) := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_pow, ← Complex.ofReal_one, ← Complex.ofReal_div,
      Complex.ofReal_re]
    simp [k]
  simp_rw [he] at hr
  simpa [k] using hr

private theorem seriesTerm_hasSum_column (n : ℕ) :
    HasSum (fun j => seriesTerm j n) ((riemannZeta ((n : ℂ) + 2) - 1).re / ((n : ℝ) + 1)) := by
  simpa [seriesTerm, one_div_pow] using (zeta_tail_hasSum n).div_const ((n : ℝ) + 1)

theorem constant_eq_log_sum :
    c = ∑' j : ℕ, (log ((j : ℝ) + 2) - log ((j : ℝ) + 1)) / ((j : ℝ) + 2) := by
  have hF : Summable (Function.uncurry seriesTerm) := by
    refine (summable_prod_of_nonneg (fun p => seriesTerm_nonnegative p.1 p.2)).mpr ⟨?_, ?_⟩
    · exact fun j => (seriesTerm_hasSum_row j).summable
    · simpa only [Function.uncurry, (seriesTerm_hasSum_row _).tsum_eq] using logWeight_summable
  calc
    c = ∑' n, ∑' j, seriesTerm j n := by
      unfold c
      simp_rw [(seriesTerm_hasSum_column _).tsum_eq]
    _ = ∑' j, ∑' n, seriesTerm j n :=
      hF.tsum_comm' (fun j => (seriesTerm_hasSum_row j).summable)
        (fun n => (seriesTerm_hasSum_column n).summable)
    _ = ∑' j, logWeight j := by simp_rw [(seriesTerm_hasSum_row _).tsum_eq]

theorem constant_pos_lt_one : 0 < c ∧ c < 1 := by
  rw [constant_eq_log_sum]
  change 0 < ∑' j, logWeight j ∧ (∑' j, logWeight j) < 1
  constructor
  · exact (logWeight_pos 0).trans_le (logWeight_summable.le_tsum 0 fun j _ => (logWeight_pos j).le)
  · rw [← unit_hasSum.tsum_eq]
    exact logWeight_summable.tsum_lt_tsum (fun j => (logWeight_lt_unit j).le)
      (logWeight_lt_unit 0) unit_hasSum.summable

theorem constant_log_sum_hasSum :
    HasSum (fun j : ℕ => (log ((j : ℝ) + 2) - log ((j : ℝ) + 1)) / ((j : ℝ) + 2)) c := by
  rw [constant_eq_log_sum]
  exact logWeight_summable.hasSum

end OMA.S_oeis_a010786

namespace A010786Dyadic

open Finset Filter Asymptotics
open scoped BigOperators Topology

noncomputable def weight (j : ℕ) : ℝ :=
  Real.log ((j : ℝ) + 2) - Real.log ((j : ℝ) + 1)

noncomputable def coeff (j : ℕ) : ℝ := weight j / ((j : ℝ) + 2)

private theorem weight_nonneg (j : ℕ) : 0 ≤ weight j := by
  unfold weight
  exact sub_nonneg.mpr (Real.log_le_log (by positivity) (by linarith))

private theorem weight_le (j : ℕ) : weight j ≤ 1 / ((j : ℝ) + 1) := by
  unfold weight
  rw [← Real.log_div (by positivity : (j : ℝ) + 2 ≠ 0)
    (by positivity : (j : ℝ) + 1 ≠ 0)]
  have h : 1 < ((j : ℝ) + 2) / ((j : ℝ) + 1) := by
    apply (lt_div_iff₀ (by positivity)).mpr
    ring_nf
    linarith
  have hlog := Real.log_lt_sub_one_of_pos (by positivity : 0 < ((j : ℝ) + 2) / ((j : ℝ) + 1))
    (ne_of_gt h)
  apply hlog.le.trans
  apply le_of_eq
  field_simp
  ring

private theorem weight_sum (n : ℕ) : ∑ j ∈ range n, weight j = Real.log ((n : ℝ) + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih]
    push_cast
    unfold weight
    rw [show (n : ℝ) + 1 + 1 = n + 2 by ring]
    ring

private theorem log_prod_nat_of_pos {α : Type*} (s : Finset α) (f : α → ℕ)
    (h : ∀ x ∈ s, 0 < f x) :
    Real.log ((∏ x ∈ s, f x : ℕ) : ℝ) = ∑ x ∈ s, Real.log (f x) := by
  classical
  push_cast
  apply Real.log_prod
  intro x hx
  exact_mod_cast (h x hx).ne'

private theorem log_floor_factorial (n : ℕ) :
    Real.log (OMA.S_oeis_a010786.a n) = ∑ j ∈ range n, weight j * ((n / (j + 2) : ℕ) : ℝ) := by
  classical
  unfold OMA.S_oeis_a010786.a
  rw [log_prod_nat_of_pos _ _ (fun k hk => Nat.div_pos (mem_Icc.mp hk).2 (mem_Icc.mp hk).1)]
  calc
    _ = ∑ k ∈ Icc 1 n, ∑ j ∈ range n, if j + 2 ≤ n / k then weight j else 0 := by
      apply sum_congr rfl
      intro k hk
      have hpos : 0 < n / k := Nat.div_pos (mem_Icc.mp hk).2 (mem_Icc.mp hk).1
      have hle : n / k ≤ n := Nat.div_le_self _ _
      rw [← sum_filter]
      have hf : (range n).filter (fun j => j + 2 ≤ n / k) = range (n / k - 1) := by
        ext j
        simp only [mem_filter, mem_range]
        omega
      rw [hf, weight_sum]
      congr 1
      exact_mod_cast (show n / k = n / k - 1 + 1 by omega)
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl
      intro j hj
      rw [← sum_filter]
      have hf : (Icc 1 n).filter (fun k => j + 2 ≤ n / k) = Icc 1 (n / (j + 2)) := by
        ext k
        simp only [mem_filter, mem_Icc]
        by_cases hk : 1 ≤ k
        · simp only [hk, true_and]
          rw [Nat.le_div_iff_mul_le (by omega : 0 < k),
            Nat.le_div_iff_mul_le (by omega : 0 < j + 2), Nat.mul_comm k]
          exact and_iff_right_of_imp (fun h =>
            ((Nat.le_div_iff_mul_le (by omega : 0 < j + 2)).mpr
              (by simpa [Nat.mul_comm] using h)).trans (Nat.div_le_self _ _))
        · simp [hk]
      rw [hf, sum_const, Nat.card_Icc]
      simp [mul_comm]

private theorem coeff_nonneg (j : ℕ) : 0 ≤ coeff j := by
  exact div_nonneg (weight_nonneg j) (by positivity)

private theorem coeff_le (j : ℕ) :
    coeff j ≤ 1 / ((j : ℝ) + 1) - 1 / ((j : ℝ) + 2) := by
  have h := div_le_div_of_nonneg_right (weight_le j) (by positivity : (0 : ℝ) ≤ j + 2)
  apply h.trans
  apply le_of_eq
  field_simp
  ring

private theorem partial_gap (C : ℝ) (hC : HasSum coeff C) (N : ℕ) :
    0 ≤ C - ∑ j ∈ range N, coeff j ∧
      C - ∑ j ∈ range N, coeff j ≤ 1 / ((N : ℝ) + 1) := by
  have hlim : Tendsto (fun n : ℕ => (∑ j ∈ range n, coeff j) - ∑ j ∈ range N, coeff j)
      atTop (nhds (C - ∑ j ∈ range N, coeff j)) :=
    hC.tendsto_sum_nat.sub tendsto_const_nhds
  have hbounds : ∀ᶠ n : ℕ in atTop,
      0 ≤ (∑ j ∈ range n, coeff j) - ∑ j ∈ range N, coeff j ∧
      (∑ j ∈ range n, coeff j) - ∑ j ∈ range N, coeff j ≤ 1 / ((N : ℝ) + 1) := by
    filter_upwards [eventually_ge_atTop N] with n hn
    rw [← sum_sdiff (range_mono hn), add_sub_cancel_right]
    refine ⟨sum_nonneg (fun j _ => coeff_nonneg j), ?_⟩
    have hmaj := sum_le_sum (s := range n \ range N) (fun j _ => coeff_le j)
    have htel : ∀ m : ℕ, ∑ j ∈ range m, (1 / ((j : ℝ) + 1) - 1 / ((j : ℝ) + 2)) =
        1 - 1 / ((m : ℝ) + 1) := by
      intro m
      induction m with
      | zero => norm_num
      | succ m ih =>
        rw [sum_range_succ, ih]
        push_cast
        rw [show (m : ℝ) + 1 + 1 = m + 2 by ring]
        ring
    have ht := sum_sdiff (f := fun j : ℕ =>
      1 / ((j : ℝ) + 1) - 1 / ((j : ℝ) + 2)) (range_mono hn)
    rw [htel, htel] at ht
    linarith [show (0 : ℝ) ≤ 1 / ((n : ℝ) + 1) by positivity]
  exact ⟨le_of_tendsto_of_tendsto tendsto_const_nhds hlim (hbounds.mono (fun _ h => h.1)),
    le_of_tendsto_of_tendsto hlim tendsto_const_nhds (hbounds.mono (fun _ h => h.2))⟩

private noncomputable def frac (d n : ℕ) : ℝ := ((n % d : ℕ) : ℝ) / (d : ℝ)

private noncomputable def mean (d : ℕ) : ℝ := ((d : ℝ) - 1) / (2 * (d : ℝ))

private noncomputable def centered (d n : ℕ) : ℝ := frac d n - mean d

private theorem centered_period (d n : ℕ) : centered d (n + d) = centered d n := by
  simp [centered, frac]

private theorem centered_small (d : ℕ) (hd : 0 < d) (n : ℕ) : |centered d n| ≤ 1 := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hfrac0 : 0 ≤ frac d n := by unfold frac; positivity
  have hfrac1 : frac d n ≤ 1 := by
    unfold frac
    apply (div_le_iff₀ hdR).mpr
    rw [one_mul]
    exact_mod_cast (Nat.mod_lt n hd).le
  have hm0 : 0 ≤ mean d := by
    unfold mean
    exact div_nonneg (sub_nonneg.mpr hd1) (by positivity)
  have hm1 : mean d ≤ 1 := by
    unfold mean
    apply (div_le_iff₀ (by positivity : 0 < 2 * (d : ℝ))).mpr
    linarith
  unfold centered
  rw [abs_le]
  constructor <;> linarith

private theorem centered_first_period (d : ℕ) (hd : 0 < d) :
    ∑ i ∈ range d, centered d i = 0 := by
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hsum : (∑ i ∈ range d, (i : ℝ)) * 2 = (d : ℝ) * ((d : ℝ) - 1) := by
    have h := congrArg (fun x : ℕ => (x : ℝ)) (sum_range_id_mul_two d)
    push_cast [Nat.cast_sub (show 1 ≤ d by omega)] at h
    exact h
  unfold centered
  rw [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul]
  have hf : ∑ i ∈ range d, frac d i = (∑ i ∈ range d, (i : ℝ)) / (d : ℝ) := by
    rw [sum_div]
    exact sum_congr rfl (fun i hi => by simp [frac, Nat.mod_eq_of_lt (mem_range.mp hi)])
  rw [hf]
  unfold mean
  field_simp
  nlinarith

private theorem centered_any_period (d : ℕ) (hd : 0 < d) (a : ℕ) :
    ∑ i ∈ range d, centered d (a + i) = 0 := by
  induction a with
  | zero => simpa using centered_first_period d hd
  | succ a ih =>
    have h₁ := sum_range_succ (fun i => centered d (a + i)) d
    have h₂ := sum_range_succ' (fun i => centered d (a + i)) d
    rw [ih, zero_add, centered_period] at h₁
    rw [h₁, Nat.add_zero] at h₂
    simp only [Nat.add_assoc, Nat.add_comm 1] at h₂ ⊢
    linarith

private theorem centered_full_periods (d : ℕ) (hd : 0 < d) (q a : ℕ) :
    ∑ i ∈ range (d * q), centered d (a + i) = 0 := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Nat.mul_succ, sum_range_add, ih, zero_add]
    simpa only [Nat.add_assoc] using centered_any_period d hd (a + d * q)

private theorem centered_block (d : ℕ) (hd : 0 < d) (N a : ℕ) :
    |∑ i ∈ range N, centered d (a + i)| ≤ (d : ℝ) := by
  have hsplit : N = d * (N / d) + N % d := by
    have h := Nat.mod_add_div N d
    omega
  nth_rw 1 [hsplit]
  rw [sum_range_add, centered_full_periods d hd, zero_add]
  calc
    _ ≤ ∑ i ∈ range (N % d), |centered d (a + (d * (N / d) + i))| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ range (N % d), (1 : ℝ) := sum_le_sum (fun i _ => centered_small d hd _)
    _ ≤ (d : ℝ) := by
      simp only [sum_const, card_range, nsmul_eq_mul, mul_one]
      exact_mod_cast (Nat.mod_lt N hd).le

private theorem floor_remainder (n : ℕ) :
    Real.log (OMA.S_oeis_a010786.a n) =
      (n : ℝ) * (∑ j ∈ range n, coeff j) - ∑ j ∈ range n, weight j * frac (j + 2) n := by
  rw [log_floor_factorial, mul_sum, ← sum_sub_distrib]
  apply sum_congr rfl
  intro j hj
  have h := congrArg (fun k : ℕ => (k : ℝ)) (Nat.mod_add_div n (j + 2))
  push_cast at h ⊢
  unfold frac coeff
  push_cast
  have hj0 : (j : ℝ) + 2 ≠ 0 := by positivity
  field_simp
  linear_combination weight j * h

private theorem frac_nonneg (d n : ℕ) : 0 ≤ frac d n := by
  unfold frac
  positivity

private theorem frac_le_one (d n : ℕ) (hd : 0 < d) : frac d n ≤ 1 := by
  unfold frac
  apply (div_le_iff₀ (by exact_mod_cast hd : (0 : ℝ) < d)).mpr
  rw [one_mul]
  exact_mod_cast (Nat.mod_lt n hd).le

private theorem remainder_le (C : ℝ) (hC : HasSum coeff C) {N n : ℕ} (hN : N ≤ n) :
    Real.log (OMA.S_oeis_a010786.a n) - C * n ≤ -∑ j ∈ range N, weight j * frac (j + 2) n := by
  have hC' : ∑ j ∈ range n, coeff j ≤ C := sub_nonneg.mp (partial_gap C hC n).1
  have hsum := sum_le_sum_of_subset_of_nonneg (range_mono hN)
    (f := fun j => weight j * frac (j + 2) n)
    (fun j _ _ => mul_nonneg (weight_nonneg j) (frac_nonneg _ _))
  rw [floor_remainder]
  linarith [mul_le_mul_of_nonneg_left hC' (Nat.cast_nonneg n)]

private theorem weight_mul_le_two (j : ℕ) : weight j * ((j : ℝ) + 2) ≤ 2 := by
  have h₁ := mul_le_mul_of_nonneg_right (weight_le j) (by positivity : 0 ≤ (j : ℝ) + 2)
  apply h₁.trans
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity : 0 < (j : ℝ) + 1)]
  linarith [Nat.cast_nonneg (α := ℝ) j]

private theorem weighted_frac_sum (N j : ℕ) :
    (N : ℝ) * (weight j - coeff j) / 2 - 2 ≤
      weight j * (∑ i ∈ range N, frac (j + 2) (N + i)) := by
  have h := neg_le_of_abs_le (centered_block (j + 2) (by omega) N N)
  unfold centered at h
  rw [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul] at h
  push_cast at h
  have hm :
      weight j * ((N : ℝ) * mean (j + 2)) = (N : ℝ) * (weight j - coeff j) / 2 := by
    unfold mean coeff
    push_cast
    field_simp
  have hmul := mul_le_mul_of_nonneg_left h (weight_nonneg j)
  rw [mul_sub, hm] at hmul
  linarith [weight_mul_le_two j]

private theorem dyadic_upper (C : ℝ) (hC : HasSum coeff C) (hc : C ≤ 1) (N : ℕ) :
    ∑ i ∈ range N, (Real.log (OMA.S_oeis_a010786.a (N + i)) - C * ((N + i : ℕ) : ℝ)) ≤
      -(N : ℝ) * Real.log ((N : ℝ) + 1) / 2 + 3 * N := by
  have hpoint := sum_le_sum (s := range N) (fun i _ =>
    remainder_le C hC (show N ≤ N + i by omega))
  rw [sum_neg_distrib, sum_comm] at hpoint
  simp_rw [← mul_sum] at hpoint
  have hweighted := sum_le_sum (s := range N) (fun j _ => weighted_frac_sum N j)
  simp only [sum_sub_distrib, ← sum_div, ← mul_sum, sum_const, card_range,
    nsmul_eq_mul, weight_sum] at hweighted
  have hpart : (∑ j ∈ range N, coeff j) ≤ 1 :=
    (sub_nonneg.mp (partial_gap C hC N).1).trans hc
  have hmul := mul_le_mul_of_nonneg_left hpart (Nat.cast_nonneg (α := ℝ) N)
  linarith

private theorem pointwise_remainder (C : ℝ) (hC : HasSum coeff C) (N : ℕ) :
    |Real.log (OMA.S_oeis_a010786.a N) - C * N| ≤ 1 + Real.log ((N : ℝ) + 1) := by
  have h₁ := partial_gap C hC N
  have hm0 := mul_nonneg (Nat.cast_nonneg (α := ℝ) N) h₁.1
  have hm1 := mul_le_mul_of_nonneg_left h₁.2 (Nat.cast_nonneg (α := ℝ) N)
  have hm2 : (N : ℝ) * (1 / ((N : ℝ) + 1)) ≤ 1 := by
    rw [← mul_div_assoc, mul_one, div_le_iff₀ (by positivity : 0 < (N : ℝ) + 1), one_mul]
    linarith
  have hsum0 : 0 ≤ ∑ j ∈ range N, weight j * frac (j + 2) N :=
    sum_nonneg fun j _ => mul_nonneg (weight_nonneg j) (frac_nonneg _ _)
  have hsum1 : ∑ j ∈ range N, weight j * frac (j + 2) N ≤ Real.log ((N : ℝ) + 1) := by
    rw [← weight_sum]
    apply sum_le_sum
    intro j hj
    exact mul_le_of_le_one_right (weight_nonneg j) (frac_le_one _ _ (by omega))
  rw [floor_remainder, abs_le]
  constructor <;> linarith

private theorem inv_nat_limit : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop

private theorem log_div_nat_limit :
    Tendsto (fun n : ℕ => Real.log (n : ℝ) / n) atTop (𝓝 0) := by
  simpa [Function.comp_def] using (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
    tendsto_natCast_atTop_atTop

theorem growth_limit (C : ℝ) (hC : HasSum coeff C) :
    Tendsto (fun n : ℕ => Real.log (OMA.S_oeis_a010786.a n) / n) atTop (𝓝 C) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  have hmajor : Tendsto (fun n : ℕ => (1 + Real.log 2 + Real.log (n : ℝ)) / n) atTop (𝓝 0) := by
    have hc : Tendsto (fun _ : ℕ => (1 : ℝ) + Real.log 2) atTop (𝓝 (1 + Real.log 2)) :=
      tendsto_const_nhds
    have h := (hc.mul inv_nat_limit).add log_div_nat_limit
    simp only [mul_zero, zero_add] at h
    refine h.congr' (Eventually.of_forall fun n => ?_)
    change (1 + Real.log 2) * (n : ℝ)⁻¹ + Real.log (n : ℝ) / n =
      (1 + Real.log 2 + Real.log (n : ℝ)) / n
    rw [add_div, div_eq_mul_inv (1 + Real.log 2)]
  refine squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) ?_ hmajor
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hlog : Real.log ((n : ℝ) + 1) ≤ Real.log (n : ℝ) + Real.log 2 := by
    rw [← Real.log_mul hnpos.ne' (by norm_num : (2 : ℝ) ≠ 0)]
    exact Real.log_le_log (by linarith) (by linarith)
  rw [Real.dist_eq, show Real.log (OMA.S_oeis_a010786.a n) / n - C =
    (Real.log (OMA.S_oeis_a010786.a n) - C * n) / n by field_simp,
    abs_div, abs_of_pos hnpos]
  exact div_le_div_of_nonneg_right ((pointwise_remainder C hC n).trans (by linarith)) hnpos.le

theorem literal_asymptotic (C : ℝ) (hC : HasSum coeff C) (hc : 0 < C) :
    (fun n : ℕ => Real.log (OMA.S_oeis_a010786.a n)) ~[atTop]
      fun n : ℕ => C * ((n : ℝ) - Real.log (2 * Real.pi * n) / 2) := by
  have hlog : Tendsto (fun n : ℕ => Real.log (2 * Real.pi * n) / ((n : ℝ) * 2)) atTop (𝓝 0) := by
    have hc' : Tendsto (fun _ : ℕ => Real.log (2 * Real.pi)) atTop (𝓝 (Real.log (2 * Real.pi))) :=
      tendsto_const_nhds
    have haux : Tendsto (fun n : ℕ =>
      (Real.log (2 * Real.pi) * (n : ℝ)⁻¹ + Real.log (n : ℝ) / n) / 2) atTop (𝓝 0) := by
      simpa only [mul_zero, zero_add, zero_div] using
        ((hc'.mul inv_nat_limit).add log_div_nat_limit).div_const 2
    refine haux.congr' ?_
    filter_upwards [eventually_ne_atTop (0 : ℕ)] with n hn
    rw [Real.log_mul (by positivity : 2 * Real.pi ≠ 0) (by exact_mod_cast hn : (n : ℝ) ≠ 0)]
    rw [← div_eq_mul_inv, ← add_div, div_div]
  have hnormal : Tendsto (fun n : ℕ => C * ((n : ℝ) - Real.log (2 * Real.pi * n) / 2) / n)
      atTop (𝓝 C) := by
    have haux : Tendsto (fun n : ℕ => C * (1 - Real.log (2 * Real.pi * n) / ((n : ℝ) * 2)))
        atTop (𝓝 C) := by
      simpa only [sub_zero, mul_one] using
        ((tendsto_const_nhds : Tendsto (fun _ : ℕ => C) atTop (𝓝 C)).mul
          ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub hlog))
    refine haux.congr' ?_
    filter_upwards [eventually_ne_atTop (0 : ℕ)] with n hn
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    field_simp
  apply isEquivalent_of_tendsto_one
  have haux : Tendsto (fun n : ℕ =>
      (Real.log (OMA.S_oeis_a010786.a n) / n) /
        (C * ((n : ℝ) - Real.log (2 * Real.pi * n) / 2) / n)) atTop (𝓝 1) := by
    have h := (growth_limit C hC).div hnormal hc.ne'
    rw [div_self hc.ne'] at h
    exact h.congr' (Eventually.of_forall (fun _ => rfl))
  refine haux.congr' ?_
  filter_upwards [eventually_ne_atTop (0 : ℕ)] with n hn
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  exact div_div_div_cancel_right₀ hnR _ _

theorem disproof (C : ℝ) (hC : HasSum coeff C) (hc0 : 0 ≤ C) (hc1 : C < 1) :
    ¬ ((fun n : ℕ => Real.log (OMA.S_oeis_a010786.a n) -
        C * (n - Real.log (2 * Real.pi * n) / 2)) =o[atTop]
      fun n : ℕ => Real.log (n : ℝ)) := by
  intro h
  let ε : ℝ := (1 - C) / 8
  have hε : 0 < ε := by dsimp [ε]; linarith
  obtain ⟨M, hM⟩ := eventually_atTop.mp (h.bound hε)
  let K := |Real.log (2 * Real.pi)| + Real.log 2
  have hK : 0 ≤ K := add_nonneg (abs_nonneg _) (Real.log_nonneg (by norm_num))
  have hlog : Tendsto (fun N : ℕ => Real.log ((N : ℝ) + 1)) atTop atTop := by
    have hshift : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using Real.tendsto_log_atTop.comp hshift
  obtain ⟨T, hT⟩ := eventually_atTop.mp (hlog.eventually_ge_atTop ((3 + K) / (2 * ε) + 1))
  let N := max T (max M 2)
  have hNT : T ≤ N := le_max_left _ _
  have hNM : M ≤ N := (le_max_left _ _).trans (le_max_right _ _)
  have hN2 : 2 ≤ N := (le_max_right _ _).trans (le_max_right _ _)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hLogN : 0 ≤ Real.log ((N : ℝ) + 1) := Real.log_nonneg (by linarith)
  have hpoint (i : ℕ) (hi : i ∈ range N) :
      -(2 * ε * Real.log ((N : ℝ) + 1)) -
          C * (Real.log ((N : ℝ) + 1) + K) / 2 ≤
        Real.log (OMA.S_oeis_a010786.a (N + i)) - C * ((N + i : ℕ) : ℝ) := by
    have hi' := mem_range.mp hi
    have hnpos : (0 : ℝ) < ((N + i : ℕ) : ℝ) := by exact_mod_cast (show 0 < N + i by omega)
    have hn1 : (1 : ℝ) ≤ ((N + i : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ N + i by omega)
    have hlog0 : 0 ≤ Real.log ((N + i : ℕ) : ℝ) := Real.log_nonneg hn1
    have hln₂' : Real.log 2 ≤ Real.log ((N : ℝ) + 1) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast (show 2 ≤ N + 1 by omega))
    have hlog_le : Real.log ((N + i : ℕ) : ℝ) ≤ Real.log ((N : ℝ) + 1) + Real.log 2 := by
      rw [← Real.log_mul (by positivity : (N : ℝ) + 1 ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
      apply Real.log_le_log hnpos
      exact_mod_cast (show N + i ≤ (N + 1) * 2 by omega)
    have hlog_le' : Real.log (2 * Real.pi * ((N + i : ℕ) : ℝ)) ≤
        Real.log ((N : ℝ) + 1) + K := by
      rw [Real.log_mul (by positivity) hnpos.ne']
      dsimp [K]
      linarith [le_abs_self (Real.log (2 * Real.pi))]
    have hb := hM (N + i) (hNM.trans (by omega))
    simp only [Real.norm_eq_abs, abs_of_nonneg hlog0] at hb
    have hb' := neg_le_of_abs_le hb
    linarith [mul_le_mul_of_nonneg_left hlog_le' hc0,
      mul_le_mul_of_nonneg_left
        (show Real.log ((N + i : ℕ) : ℝ) ≤ 2 * Real.log ((N : ℝ) + 1) by linarith) hε.le]
  have hsum := sum_le_sum (s := range N) hpoint
  simp only [sum_const, card_range, nsmul_eq_mul] at hsum
  have hup := dyadic_upper C hC hc1.le N
  have hmul :
      (N : ℝ) * (-(2 * ε * Real.log ((N : ℝ) + 1)) -
        C * (Real.log ((N : ℝ) + 1) + K) / 2) ≤
      (N : ℝ) * (-Real.log ((N : ℝ) + 1) / 2 + 3) := by
    have hbound := hsum.trans hup
    linear_combination hbound
  have hdivide := le_of_mul_le_mul_left hmul hNpos
  have hcK := mul_le_mul_of_nonneg_right hc1.le hK
  have hbound : 2 * ε * Real.log ((N : ℝ) + 1) ≤ 3 + K := by
    have hCε : C = 1 - 8 * ε := by dsimp [ε]; ring
    nlinarith
  have hh := hT N hNT
  have hε2 : 0 < 2 * ε := by positivity
  have hlarge := (div_le_iff₀ hε2).mp (show (3 + K) / (2 * ε) ≤
      Real.log ((N : ℝ) + 1) - 1 by linarith)
  nlinarith

end A010786Dyadic

namespace OMA.S_oeis_a010786

open Filter Asymptotics Real
open scoped Topology

private theorem constant_hasSum_dyadic_coeff : HasSum A010786Dyadic.coeff c :=
  constant_log_sum_hasSum.congr_fun fun _ => rfl

/-- The ratio asymptotic printed in the OEIS entry holds with the stated constant. -/
theorem source_ratio_asymptotic :
    (fun n : ℕ => log (a n)) ~[atTop]
      fun n : ℕ => c * ((n : ℝ) - log (2 * π * n) / 2) :=
  A010786Dyadic.literal_asymptotic c constant_hasSum_dyadic_coeff constant_pos_lt_one.1

end OMA.S_oeis_a010786

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a010786.main) :=
  A010786Dyadic.disproof OMA.S_oeis_a010786.c OMA.S_oeis_a010786.constant_hasSum_dyadic_coeff
    OMA.S_oeis_a010786.constant_pos_lt_one.1.le OMA.S_oeis_a010786.constant_pos_lt_one.2
