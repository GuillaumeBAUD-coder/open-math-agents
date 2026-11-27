import OMAReductions.R_Erdos950_erdos_950_variants_weaker_pi_implies_f_R1

-- Step Erdos950.erdos_950.variants.weaker_pi_implies_f.R1.H2: hypothesis H2 of reduction Erdos950.erdos_950.variants.weaker_pi_implies_f.R1
-- Credit: @ivillar
-- H2 := ∀ K K₀ C : ℝ, 0 < K → 0 < K₀ → 0 < C → ∃ M : ℝ, ∀ᶠ n : ℕ in atTop,     ∀ S : Finset ℕ, (∀ s ∈ S, 1 ≤ s ∧ s ≤ n) →     (∀ t : ℕ, 2 ≤ t → (t : ℝ) ≤ Real.log n ^ C →       ((S.filter (· ≤ t)).card : ℝ) ≤ K₀ * t / Real.log t) →     (∀ t : ℕ, Real.log n ^ C < t → t ≤ n →       ((S.filter (· ≤ t)).card : ℝ) ≤ K * t / Real.log n) →     ∑ s ∈ S, (1 : ℝ) / s ≤ M * Real.log (Real.log (Real.log n))
--
-- Proof: split S into dyadic blocks [2^j, 2^(j+1)); block j contributes at most
-- #{s in S : s <= min(2^(j+1), n)} / 2^j. If 2^(j+1) <= (log n)^C the first counting bound gives
-- 2*K0/((j+1)*log 2), and these j satisfy j+1 <= log((log n)^C)/log 2, so they sum to at most
-- (2*K0/log 2)*(1 + log C + log log log n - log log 2) by harmonic_le_one_add_log. The other
-- blocks contribute 2*K/log n each, and there are at most log n/log 2 + 1 of them.

namespace OMA.E950

open Finset

lemma dyadic_bound (S : Finset ℕ) (n : ℕ) (hS : ∀ s ∈ S, 1 ≤ s ∧ s ≤ n) :
    ∑ s ∈ S, (1 : ℝ) / s ≤ ∑ j ∈ range (Nat.log 2 n + 1),
      ((S.filter (· ≤ min (2 ^ (j + 1)) n)).card : ℝ) / 2 ^ j := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := Nat.log 2) (t := range (Nat.log 2 n + 1))
    (fun s hs => by
      rw [mem_range]
      exact Nat.lt_succ_of_le (Nat.log_mono_right (hS s hs).2))]
  apply Finset.sum_le_sum
  intro j _
  calc ∑ s ∈ S.filter (fun s => Nat.log 2 s = j), (1 : ℝ) / s
      ≤ ∑ s ∈ S.filter (fun s => Nat.log 2 s = j), (1 : ℝ) / 2 ^ j := by
        apply Finset.sum_le_sum
        intro s hs
        rw [mem_filter] at hs
        have h1 := (hS s hs.1).1
        have h2 : 2 ^ j ≤ s := hs.2 ▸ Nat.pow_log_le_self 2 (by omega)
        apply one_div_le_one_div_of_le (by positivity)
        exact_mod_cast h2
    _ = ((S.filter (fun s => Nat.log 2 s = j)).card : ℝ) / 2 ^ j := by
        rw [sum_const, nsmul_eq_mul]; ring
    _ ≤ ((S.filter (· ≤ min (2 ^ (j + 1)) n)).card : ℝ) / 2 ^ j := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        apply Nat.cast_le.mpr
        apply card_le_card
        intro s hs
        rw [mem_filter] at hs ⊢
        refine ⟨hs.1, le_min ?_ (hS s hs.1).2⟩
        have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) s
        rw [hs.2] at this
        omega

end OMA.E950

open OMA.E950 Filter Finset in
theorem OMA.solution : OMA.R_Erdos950_erdos_950_variants_weaker_pi_implies_f_R1.H2 := by
  intro K K₀ C hK hK₀ hC
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set B : ℝ := 2 * K₀ / Real.log 2 with hBdef
  set A : ℝ := 2 * K / Real.log 2 + 2 * K + B * (1 + Real.log C - Real.log (Real.log 2)) with hAdef
  have hB : 0 ≤ B := by positivity
  refine ⟨|A| + B, ?_⟩
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlog3 : Tendsto (fun n : ℕ => Real.log (Real.log (Real.log (n : ℝ)))) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp hlog)
  have hLn : ∀ᶠ n : ℕ in atTop, Real.log (n : ℝ) ^ C < (n : ℝ) := by
    have h := (isLittleO_log_rpow_rpow_atTop C (by norm_num : (0 : ℝ) < 1)).bound
      (by norm_num : (0 : ℝ) < 1 / 2)
    filter_upwards [tendsto_natCast_atTop_atTop.eventually h, eventually_ge_atTop 1] with n hn h1
    have hpos : (0 : ℝ) < n := by exact_mod_cast h1
    rw [Real.rpow_one, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hpos] at hn
    linarith [le_abs_self (Real.log (n : ℝ) ^ C)]
  have hL2 : ∀ᶠ n : ℕ in atTop, (2 : ℝ) ≤ Real.log (n : ℝ) ^ C := by
    filter_upwards [hlog.eventually_ge_atTop ((2 : ℝ) ^ (1 / C))] with n hn
    calc (2 : ℝ) = ((2 : ℝ) ^ (1 / C)) ^ C := by
          rw [← Real.rpow_mul (by norm_num), one_div_mul_cancel hC.ne', Real.rpow_one]
      _ ≤ Real.log n ^ C := Real.rpow_le_rpow (by positivity) hn hC.le
  filter_upwards [hlog3.eventually_ge_atTop 1, hlog.eventually_ge_atTop 1, hLn, hL2,
    eventually_ge_atTop 2] with n h3 h1 hLn hL2 hn2
  intro S hS hyp1 hyp2
  set L : ℝ := Real.log (n : ℝ) ^ C with hLdef
  set x : ℝ := Real.log (Real.log (Real.log (n : ℝ))) with hxdef
  have hlogn : 0 < Real.log (n : ℝ) := by linarith
  refine (dyadic_bound S n hS).trans ?_
  set m := Nat.log 2 n + 1 with hm
  set c : ℕ → ℝ := fun j => ((S.filter (· ≤ min (2 ^ (j + 1)) n)).card : ℝ) / 2 ^ j with hc
  change ∑ j ∈ range m, c j ≤ _
  rw [← Finset.sum_filter_add_sum_filter_not (range m) (fun j => (2 : ℝ) ^ (j + 1) ≤ L)]
  -- small scales: Brun–Titchmarsh-type counting
  have p1 : ∑ j ∈ (range m).filter (fun j => (2 : ℝ) ^ (j + 1) ≤ L), c j ≤
      B * (1 + Real.log C + x - Real.log (Real.log 2)) := by
    have hcj : ∀ j ∈ (range m).filter (fun j => (2 : ℝ) ^ (j + 1) ≤ L),
        c j ≤ B * (1 / ((j : ℝ) + 1)) := by
      intro j hj
      rw [mem_filter] at hj
      have hcard : ((S.filter (· ≤ min (2 ^ (j + 1)) n)).card : ℝ) ≤
          ((S.filter (· ≤ 2 ^ (j + 1))).card : ℝ) := by
        apply Nat.cast_le.mpr
        apply card_le_card
        intro s hs
        rw [mem_filter] at hs ⊢
        exact ⟨hs.1, hs.2.trans (min_le_left _ _)⟩
      have h2 : 2 ≤ 2 ^ (j + 1) := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (j + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hy := hyp1 (2 ^ (j + 1)) h2 (by push_cast; exact hj.2)
      have hlogt : Real.log (((2 ^ (j + 1) : ℕ) : ℝ)) = ((j : ℝ) + 1) * Real.log 2 := by
        push_cast; rw [Real.log_pow]; push_cast; ring
      rw [hlogt] at hy
      simp only [hc]
      calc ((S.filter (· ≤ min (2 ^ (j + 1)) n)).card : ℝ) / 2 ^ j
          ≤ (K₀ * ((2 ^ (j + 1) : ℕ) : ℝ) / (((j : ℝ) + 1) * Real.log 2)) / 2 ^ j :=
            div_le_div_of_nonneg_right (hcard.trans hy) (by positivity)
        _ = B * (1 / ((j : ℝ) + 1)) := by
            rw [hBdef]; push_cast; field_simp; ring
    set N : ℕ := ⌊Real.log L / Real.log 2⌋₊ with hN
    have hsub : (range m).filter (fun j => (2 : ℝ) ^ (j + 1) ≤ L) ⊆ range N := by
      intro j hj
      rw [mem_filter] at hj
      rw [mem_range]
      have hle : ((j : ℝ) + 1) * Real.log 2 ≤ Real.log L := by
        have := Real.log_le_log (by positivity) hj.2
        rwa [Real.log_pow, Nat.cast_add, Nat.cast_one] at this
      have : ((j + 1 : ℕ) : ℝ) ≤ Real.log L / Real.log 2 := by
        rw [le_div_iff₀ hl2]; push_cast; exact hle
      have := Nat.le_floor this
      omega
    have hharm : ∑ j ∈ range N, (1 : ℝ) / ((j : ℝ) + 1) = (harmonic N : ℝ) := by
      simp [harmonic, one_div]
    have hLpos : 0 < Real.log L := Real.log_pos (by linarith)
    have hratio : 1 ≤ Real.log L / Real.log 2 := by
      rw [le_div_iff₀ hl2, one_mul]
      exact Real.log_le_log (by norm_num) hL2
    have hlogN : Real.log (N : ℝ) ≤ Real.log (Real.log L / Real.log 2) := by
      rcases Nat.eq_zero_or_pos N with h0 | hpos
      · rw [h0, Nat.cast_zero, Real.log_zero]
        exact Real.log_nonneg hratio
      · exact Real.log_le_log (by exact_mod_cast hpos) (Nat.floor_le (by positivity))
    have hll : 0 < Real.log (Real.log (n : ℝ)) := by
      have h0 : 0 ≤ Real.log (Real.log (n : ℝ)) := Real.log_nonneg h1
      rcases eq_or_lt_of_le h0 with h | h
      · rw [hxdef, ← h, Real.log_zero] at h3
        linarith
      · exact h
    have hLexp : Real.log (Real.log L / Real.log 2) = Real.log C + x - Real.log (Real.log 2) := by
      rw [Real.log_div hLpos.ne' hl2.ne', hLdef, Real.log_rpow hlogn,
        Real.log_mul hC.ne' hll.ne']
    calc ∑ j ∈ (range m).filter (fun j => (2 : ℝ) ^ (j + 1) ≤ L), c j
        ≤ ∑ j ∈ (range m).filter (fun j => (2 : ℝ) ^ (j + 1) ≤ L), B * (1 / ((j : ℝ) + 1)) :=
          Finset.sum_le_sum hcj
      _ ≤ ∑ j ∈ range N, B * (1 / ((j : ℝ) + 1)) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => by positivity)
      _ = B * (harmonic N : ℝ) := by rw [← Finset.mul_sum, hharm]
      _ ≤ B * (1 + Real.log (N : ℝ)) := by
          apply mul_le_mul_of_nonneg_left _ hB
          exact_mod_cast harmonic_le_one_add_log N
      _ ≤ B * (1 + Real.log C + x - Real.log (Real.log 2)) := by
          apply mul_le_mul_of_nonneg_left _ hB
          linarith
  -- large scales
  have p2 : ∑ j ∈ (range m).filter (fun j => ¬ (2 : ℝ) ^ (j + 1) ≤ L), c j ≤
      2 * K / Real.log 2 + 2 * K := by
    have hcj : ∀ j ∈ (range m).filter (fun j => ¬ (2 : ℝ) ^ (j + 1) ≤ L),
        c j ≤ 2 * K / Real.log (n : ℝ) := by
      intro j hj
      rw [mem_filter] at hj
      have hgt : L < (2 : ℝ) ^ (j + 1) := lt_of_not_ge hj.2
      have hLt : L < ((min (2 ^ (j + 1)) n : ℕ) : ℝ) := by
        rcases le_total (2 ^ (j + 1)) n with h | h
        · rw [min_eq_left h]; push_cast; exact hgt
        · rw [min_eq_right h]; exact hLn
      have hy := hyp2 (min (2 ^ (j + 1)) n) hLt (min_le_right _ _)
      have htle : ((min (2 ^ (j + 1)) n : ℕ) : ℝ) ≤ (2 : ℝ) ^ (j + 1) := by
        have : min (2 ^ (j + 1)) n ≤ 2 ^ (j + 1) := min_le_left _ _
        exact_mod_cast this
      simp only [hc]
      calc ((S.filter (· ≤ min (2 ^ (j + 1)) n)).card : ℝ) / 2 ^ j
          ≤ (K * (2 : ℝ) ^ (j + 1) / Real.log n) / 2 ^ j := by
            apply div_le_div_of_nonneg_right _ (by positivity)
            refine hy.trans ?_
            apply div_le_div_of_nonneg_right _ hlogn.le
            exact mul_le_mul_of_nonneg_left htle hK.le
        _ = 2 * K / Real.log (n : ℝ) := by field_simp; ring
    have hmle : (m : ℝ) ≤ Real.log n / Real.log 2 + 1 := by
      have hk : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 (by omega)
      have : (Nat.log 2 n : ℝ) * Real.log 2 ≤ Real.log n := by
        have := Real.log_le_log (by positivity) (show ((2 ^ Nat.log 2 n : ℕ) : ℝ) ≤ n by exact_mod_cast hk)
        rwa [Nat.cast_pow, Real.log_pow, Nat.cast_ofNat] at this
      rw [hm]; push_cast
      have : (Nat.log 2 n : ℝ) ≤ Real.log n / Real.log 2 := by rw [le_div_iff₀ hl2]; exact this
      linarith
    calc ∑ j ∈ (range m).filter (fun j => ¬ (2 : ℝ) ^ (j + 1) ≤ L), c j
        ≤ ∑ j ∈ (range m).filter (fun j => ¬ (2 : ℝ) ^ (j + 1) ≤ L), 2 * K / Real.log (n : ℝ) :=
          Finset.sum_le_sum hcj
      _ = ((range m).filter (fun j => ¬ (2 : ℝ) ^ (j + 1) ≤ L)).card * (2 * K / Real.log (n : ℝ)) := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ (m : ℝ) * (2 * K / Real.log (n : ℝ)) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          have := card_filter_le (range m) (fun j => ¬ (2 : ℝ) ^ (j + 1) ≤ L)
          rw [card_range] at this
          exact_mod_cast this
      _ ≤ (Real.log n / Real.log 2 + 1) * (2 * K / Real.log (n : ℝ)) :=
          mul_le_mul_of_nonneg_right hmle (by positivity)
      _ = 2 * K / Real.log 2 + 2 * K / Real.log (n : ℝ) := by field_simp
      _ ≤ 2 * K / Real.log 2 + 2 * K := by
          have : 2 * K / Real.log (n : ℝ) ≤ 2 * K := by
            rw [div_le_iff₀ hlogn]; nlinarith
          linarith
  have hAx : A ≤ |A| * x := (le_abs_self A).trans (le_mul_of_one_le_right (abs_nonneg A) h3)
  have : A + B * x = 2 * K / Real.log 2 + 2 * K + B * (1 + Real.log C + x - Real.log (Real.log 2)) := by
    rw [hAdef]; ring
  nlinarith
