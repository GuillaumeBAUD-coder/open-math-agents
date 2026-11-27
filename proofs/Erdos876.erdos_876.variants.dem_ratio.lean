import FormalConjectures.ErdosProblems.«876»

/-! A sequence of integers close to exp(√n), with one residue class for each
dyadic block of indices. At the first block used in a sum, its modulus
records the number of participating terms in that block. -/

open Filter Finset Real
open scoped Topology BigOperators

namespace OMA.SumFreeRatio

private def stage (n : ℕ) := Nat.log 2 (n + 1)
private def unitAt (s : ℕ) : ℕ := 2 ^ (s*s)
private def radix (s : ℕ) : ℕ := 2 ^ (2*s+1)

private theorem unit_succ (s : ℕ) : unitAt (s+1) = radix s * unitAt s := by
  simp only [unitAt, radix, ← pow_add]
  congr 1
  ring

private theorem unit_pos (s : ℕ) : 0 < unitAt s := by
  unfold unitAt
  positivity

private theorem unit_dvd {s t : ℕ} (h : s ≤ t) : unitAt s ∣ unitAt t :=
  pow_dvd_pow 2 (Nat.mul_le_mul h h)

private theorem stage_mono : Monotone stage := by
  intro n m h
  exact Nat.log_monotone (Nat.succ_le_succ h)

private theorem block_small (s : ℕ) (T : Finset ℕ) (h : ∀ i ∈ T, stage i = s) :
    T.card < radix s := by
  have hsub : T ⊆ range (2^(s+1)-1) := by
    intro i hi
    have hx := Nat.lt_pow_succ_log_self (by decide : 1 < 2) (i+1)
    change i+1 < 2^(stage i+1) at hx
    rw [h i hi] at hx
    exact mem_range.mpr (by omega)
  have hcard := card_le_card hsub
  rw [card_range] at hcard
  have hp : 0 < 2^(s+1) := by positivity
  exact lt_of_lt_of_le (by omega : T.card < 2^(s+1))
    (Nat.pow_le_pow_right (by decide) (by omega : s+1 ≤ 2*s+1))

private noncomputable def base (n : ℕ) : ℝ := exp (√(n+1 : ℝ))
private noncomputable def nextValue (n lower : ℕ) : ℕ :=
  let d := unitAt (stage n + 1)
  (lower / d + 1) * d + unitAt (stage n)

private noncomputable def seq : ℕ → ℕ
  | 0 => nextValue 0 ⌈base 0⌉₊
  | n+1 => nextValue (n+1) (max (seq n) ⌈base (n+1)⌉₊)

private theorem next_bounds (n lower : ℕ) : lower < nextValue n lower ∧
    nextValue n lower ≤ lower + 2*unitAt (stage n+1) := by
  let d := unitAt (stage n+1)
  have hd : 0 < d := unit_pos _
  have hu : unitAt (stage n) ≤ d := Nat.le_of_dvd hd (unit_dvd (Nat.le_succ _))
  have hlo := Nat.div_add_mod lower d
  have hm := Nat.mod_lt lower hd
  change lower < (lower/d+1)*d + _ ∧ (lower/d+1)*d + _ ≤ lower + 2*d
  rw [Nat.add_mul, one_mul, Nat.mul_comm (lower / d) d]
  omega

private theorem seq_mono : StrictMono seq := by
  apply strictMono_nat_of_lt_succ
  intro n
  exact lt_of_le_of_lt (le_max_left _ _) (next_bounds _ _).1

private theorem seq_ge (n : ℕ) : base n ≤ (seq n : ℝ) := by
  refine (Nat.le_ceil _).trans ?_
  exact_mod_cast (show ⌈base n⌉₊ ≤ seq n by
    cases n with
    | zero => exact (next_bounds _ _).1.le
    | succ n => exact (le_max_right _ _).trans (next_bounds _ _).1.le)

private theorem seq_residue (n : ℕ) :
    seq n ≡ unitAt (stage n) [MOD unitAt (stage n+1)] := by
  have h (l : ℕ) : nextValue n l ≡ unitAt (stage n) [MOD unitAt (stage n+1)] := by
    simp [nextValue, Nat.ModEq, Nat.add_mod]
  cases n <;> exact h _

private theorem seq_dvd (n : ℕ) : unitAt (stage n) ∣ seq n := by
  have hh := (seq_residue n).of_dvd (unit_dvd (Nat.le_succ _))
  exact Nat.modEq_zero_iff_dvd.mp (hh.trans (Nat.modEq_zero_iff_dvd.mpr (dvd_refl _)))

private theorem no_sum (n : ℕ) (T : Finset ℕ) (ht : ∀ i ∈ T, i < n)
    (hne : T.Nonempty) : seq n ≠ ∑ i ∈ T, seq i := by
  classical
  intro heq
  let s := stage (T.min' hne)
  let U := T.filter (fun i => stage i = s)
  have hs (i) (hi : i ∈ T) : s ≤ stage i := stage_mono (T.min'_le i hi)
  have hU : U.Nonempty := ⟨T.min' hne, mem_filter.mpr ⟨T.min'_mem _, rfl⟩⟩
  have hcard := block_small s U (fun i hi => (mem_filter.mp hi).2)
  have hsum : (∑ i ∈ T, seq i) ≡ U.card * unitAt s [MOD unitAt (s+1)] := by
    calc
      _ ≡ ∑ i ∈ T, (if stage i = s then unitAt s else 0) [MOD unitAt (s+1)] := by
        apply Nat.ModEq.sum
        intro i hi
        split_ifs with hi'
        · simpa [hi'] using seq_residue i
        · exact Nat.modEq_zero_iff_dvd.mpr
            ((unit_dvd (by have := hs i hi; omega : s+1 ≤ stage i)).trans (seq_dvd i))
      _ = U.card * unitAt s := by simp [U, ← Finset.sum_filter]
  rw [← heq, unit_succ] at hsum
  have hsn := stage_mono (ht _ (T.min'_mem hne)).le
  change s ≤ stage n at hsn
  by_cases hn : stage n = s
  · have hfull : U = T := filter_true_of_mem fun i hi => le_antisymm
        (hn ▸ stage_mono (ht i hi).le) (hs i hi)
    have hcon := (seq_residue n).symm
    rw [hn, unit_succ] at hcon
    have hc : 1 * unitAt s ≡ U.card * unitAt s [MOD radix s * unitAt s] := by
      simpa using hcon.trans hsum
    have hc' := Nat.ModEq.mul_right_cancel' (unit_pos s).ne' hc
    have hr : 1 < radix s := by unfold radix; exact Nat.one_lt_pow (by omega) (by decide)
    change 1 % radix s = U.card % radix s at hc'
    rw [Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt hcard, hfull] at hc'
    obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hc'.symm
    have hjn : j < n := ht j (by simp [hj])
    simp [hj] at heq
    exact (seq_mono hjn).ne heq.symm
  · have hmod := Nat.modEq_zero_iff_dvd.mpr
      ((unit_dvd (by omega : s+1 ≤ stage n)).trans (seq_dvd n))
    rw [unit_succ] at hmod
    have hc : 0 * unitAt s ≡ U.card * unitAt s [MOD radix s * unitAt s] := by
      simpa using hmod.symm.trans hsum
    have hc' := Nat.ModEq.mul_right_cancel' (unit_pos s).ne' hc
    change 0 % radix s = U.card % radix s at hc'
    simp [Nat.mod_eq_of_lt hcard] at hc'
    exact (Finset.card_pos.mpr hU).ne hc'


private theorem seq_pos (n : ℕ) : 0 < seq n := by
  exact_mod_cast lt_of_lt_of_le (exp_pos _) (seq_ge n)

private theorem range_sum_free : Erdos876.IsSubsetSumFree (Set.range seq) := by
  classical
  rintro _ ⟨n, rfl⟩
  refine ⟨seq_pos n, ?_⟩
  rintro ⟨B, hB, heq⟩
  let T := (range n).filter fun i => seq i ∈ B
  have hT : ∀ i ∈ T, i < n := fun i hi => mem_range.mp (mem_filter.mp hi).1
  have him : T.image seq = B := by
    ext x
    constructor
    · rintro hx
      obtain ⟨i, hi, rfl⟩ := mem_image.mp hx
      exact (mem_filter.mp hi).2
    · intro hx
      obtain ⟨⟨i, rfl⟩, hlt⟩ := hB hx
      exact mem_image.mpr ⟨i, mem_filter.mpr ⟨mem_range.mpr (seq_mono.lt_iff_lt.mp hlt), hx⟩, rfl⟩
  rw [← him, Finset.sum_image (fun _ _ _ _ h => seq_mono.injective h)] at heq
  apply no_sum n T hT _ heq
  by_contra! hh
  rw [hh, sum_empty] at heq
  exact (seq_pos n).ne' heq

private theorem base_pos (n : ℕ) : 0 < base n := exp_pos _

private theorem base_ratio :
    Tendsto (fun n => base (n+1) / base n) atTop (𝓝 1) := by
  have ht : Tendsto (fun n : ℕ => (n : ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have ht' := tendsto_sqrt_atTop.comp ht
  have hd : Tendsto (fun n : ℕ => √((n:ℝ)+1+1) - √((n:ℝ)+1)) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => sub_nonneg.mpr (sqrt_le_sqrt (by linarith)))
      (fun n => ?_) (tendsto_inv_atTop_zero.comp ht')
    have hx : 0 < √((n:ℝ)+1) := sqrt_pos.2 (by positivity)
    change _ ≤ (√((n:ℝ)+1))⁻¹
    rw [← one_div]
    apply (le_div_iff₀ hx).mpr
    have hs₁ := Real.sq_sqrt (by positivity : 0 ≤ (n:ℝ)+1)
    have hs₂ := Real.sq_sqrt (by positivity : 0 ≤ (n:ℝ)+1+1)
    nlinarith [sq_nonneg (√((n:ℝ)+1+1) - √((n:ℝ)+1))]
  simpa [base, Nat.cast_add, ← Real.exp_sub, Function.comp_def] using (Real.continuous_exp.tendsto 0).comp hd

private theorem unit_small :
    Tendsto (fun n => (unitAt (stage n+1) : ℝ) / base n) atTop (𝓝 0) := by
  have ht : Tendsto (fun n : ℕ => (n : ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have ht' := tendsto_sqrt_atTop.comp ht
  have hlog : 0 < log 2 := log_pos (by norm_num)
  have hsmall := ht.eventually ((isLittleO_log_rpow_rpow_atTop (2 : ℝ) (s := 1/2) (by norm_num)).bound
    (show 0 < log 2 / 8 by positivity))
  have hlim : Tendsto (fun n : ℕ => exp (-(√((n:ℝ)+1) / 2))) atTop (𝓝 0) :=
    tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp (ht'.atTop_div_const (by norm_num : (0:ℝ) < 2)))
  apply squeeze_zero' (Eventually.of_forall (fun n => div_nonneg (Nat.cast_nonneg _) (base_pos n).le)) _ hlim
  filter_upwards [hsmall, eventually_ge_atTop (1 : ℕ)] with n hn h1
  let x : ℝ := n+1
  have hx : 2 ≤ x := by dsimp [x]; exact_mod_cast (by omega : 2 ≤ n+1)
  have hlx : log 2 ≤ log x := log_le_log (by norm_num) hx
  have hnn : 0 ≤ x := by linarith
  have h : log x ^ 2 ≤ log 2 / 8 * √x := by
    change ‖log x ^ (2:ℝ)‖ ≤ log 2 / 8 * ‖x^(1/2 : ℝ)‖ at hn
    rwa [rpow_two, ← sqrt_eq_rpow, Real.norm_of_nonneg (sq_nonneg _),
      Real.norm_of_nonneg (sqrt_nonneg _)] at hn
  have hs : ((stage n : ℕ) : ℝ) ≤ log x / log 2 := by
    simpa [stage, logb, x] using natLog_le_logb (n+1) 2
  have hs' : (stage n : ℝ)+1 ≤ 2 * (log x / log 2) := by
    have : 1 ≤ log x / log 2 := (one_le_div hlog).mpr hlx
    linarith
  have hsq : ((stage n : ℝ)+1)^2 * log 2 ≤ √x / 2 := calc
    _ ≤ (2*(log x / log 2))^2 * log 2 := by gcongr
    _ = (log x ^ 2) * (4 / log 2) := by field_simp; ring
    _ ≤ (log 2 / 8 * √x) * (4 / log 2) := by gcongr
    _ = √x / 2 := by field_simp; ring
  have hu : (unitAt (stage n+1) : ℝ) = exp (((stage n : ℝ)+1)^2 * log 2) := by
    rw [unitAt, Nat.cast_pow, Nat.cast_ofNat, ← Real.exp_log (by norm_num : (0:ℝ)<2),
      ← Real.exp_nat_mul, Real.log_exp]
    push_cast
    congr 1
    ring
  rw [hu]
  change exp _ / exp (√x) ≤ exp (-(√x/2))
  rw [← exp_sub, exp_le_exp]
  linarith

private theorem seq_ratio : Tendsto (fun n => (seq (n+1):ℝ) / seq n) atTop (𝓝 1) := by
  let r (n : ℕ) := base (n+1) / base n
  let u (n : ℕ) := (unitAt (stage (n+1)+1):ℝ) / base (n+1)
  have hr : Tendsto r atTop (𝓝 1) := base_ratio
  have hu : Tendsto u atTop (𝓝 0) := unit_small.comp (tendsto_add_atTop_nat 1)
  have hb : Tendsto (fun n => max 1 (r n) + 3 * u n * r n) atTop (𝓝 1) := by
    simpa using ((tendsto_const_nhds (x := (1:ℝ))).max hr).add (((tendsto_const_nhds (x := (3:ℝ))).mul hu).mul hr)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb
  · intro n
    change 1 ≤ (seq (n+1) : ℝ) / seq n
    exact (one_le_div (Nat.cast_pos.mpr (seq_pos n))).mpr
      (Nat.cast_le.mpr (seq_mono (Nat.lt_succ_self n)).le)
  · intro n
    let d : ℝ := unitAt (stage (n+1)+1)
    have hd : 1 ≤ d := by dsimp [d]; exact_mod_cast (show 1 ≤ unitAt (stage (n+1)+1) from unit_pos _)
    have hcur : (0:ℝ) < seq n := by exact_mod_cast seq_pos n
    have hb₀ := base_pos n
    have hb₁ := base_pos (n+1)
    have hceil := (Nat.ceil_lt_add_one hb₁.le).le
    have hstep : (seq (n+1):ℝ) ≤ max (seq n : ℝ) (⌈base (n+1)⌉₊ : ℕ) + 2*d := by
      dsimp [d]
      exact_mod_cast (next_bounds (n+1) (max (seq n) ⌈base (n+1)⌉₊)).2
    have hmax : max (seq n : ℝ) (⌈base (n+1)⌉₊ : ℕ) ≤ max (seq n : ℝ) (base (n+1)) + 1 := by
      apply max_le
      · linarith [le_max_left (seq n : ℝ) (base (n+1))]
      · linarith [le_max_right (seq n : ℝ) (base (n+1))]
    have hfrac : base (n+1) / (seq n : ℝ) ≤ r n :=
      div_le_div_of_nonneg_left hb₁.le hb₀ (seq_ge n)
    have hc : u n * r n = d / base n := by
      dsimp [u,r,d]
      field_simp
    change (seq (n+1):ℝ) / seq n ≤ max 1 (r n) + 3 * u n * r n
    rw [mul_assoc, hc]
    calc
      _ ≤ (max (seq n : ℝ) (base (n+1)) + 3*d) / seq n := by
        apply div_le_div_of_nonneg_right _ hcur.le
        linarith
      _ = max 1 (base (n+1) / seq n) + 3 * (d / seq n) := by
        rw [add_div, ← max_div_div_right hcur.le _ _, div_self hcur.ne', mul_div_assoc]
      _ ≤ _ := by
        gcongr
        exact seq_ge n

private theorem construction : type_of% @Erdos876.erdos_876.variants.dem_ratio := by
  have hi := Set.infinite_range_of_injective seq_mono.injective
  refine ⟨Set.range seq, hi, range_sum_free, ?_⟩
  have hh (n : ℕ) : Nat.nth (· ∈ Set.range seq) n = seq n := by
    have he := Nat.nth_comp_of_strictMono (p := (· ∈ Set.range seq)) (n := n) seq_mono
      (fun _ h => h) (fun hf => (hi hf).elim)
    simpa [Set.mem_range_self] using he.symm
  simpa only [hh] using seq_ratio

end OMA.SumFreeRatio

open OMA.SumFreeRatio in
theorem OMA.solution : type_of% @Erdos876.erdos_876.variants.dem_ratio := construction
