import OMAReductions.R_Erdos46_erdos_46_variants_infinitely_many_disjoint_R1

-- Step Erdos46.erdos_46.variants.infinitely_many_disjoint.R1.H1: hypothesis H1 of reduction Erdos46.erdos_46.variants.infinitely_many_disjoint.R1

/-!
Since `1 / n ≥ log (n + 1) - log n`, the sum over `(B, N]` is at least
`log (N + 1) - log (B + 1) ≥ log N - log (B + 1)`. On the other hand
`log (log (log N)) / log (log N) → 0`, so for large `N` the left side is at most `(1/2) log N`,
which is smaller once `log N > 2 log (B + 1)`.
-/

namespace OMA

theorem harm_ge (B : ℕ) : ∀ N : ℕ, B ≤ N →
    Real.log ((N : ℝ) + 1) - Real.log ((B : ℝ) + 1) ≤ ∑ n ∈ Finset.Ioc B N, (1 / (n : ℝ)) := by
  intro N hN
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ N hN ih =>
    rw [Finset.sum_Ioc_succ_top hN]
    have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    have hN2 : (0 : ℝ) < (N : ℝ) + 1 + 1 := by positivity
    have h := Real.log_le_sub_one_of_pos (div_pos hN2 hN1)
    rw [Real.log_div hN2.ne' hN1.ne'] at h
    have e : ((N : ℝ) + 1 + 1) / ((N : ℝ) + 1) - 1 = 1 / ((N : ℝ) + 1) := by
      field_simp
      ring
    rw [e] at h
    push_cast
    linarith

end OMA

theorem OMA.solution : OMA.R_Erdos46_erdos_46_variants_infinitely_many_disjoint_R1.H1 := by
  unfold OMA.R_Erdos46_erdos_46_variants_infinitely_many_disjoint_R1.H1
  intro B N₀ K
  have hg : Filter.Tendsto (fun N : ℕ => Real.log (Real.log (N : ℝ))) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ)))
  have hf : Filter.Tendsto (fun x : ℝ => Real.log x / x) Filter.atTop (nhds 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hε : Filter.Tendsto (fun N : ℕ => K * (Real.log (Real.log (Real.log (N : ℝ))) /
      Real.log (Real.log (N : ℝ)))) Filter.atTop (nhds 0) := by
    have h := (hf.comp hg).const_mul K
    simpa using h
  have h1 : ∀ᶠ N : ℕ in Filter.atTop, K * (Real.log (Real.log (Real.log (N : ℝ))) /
      Real.log (Real.log (N : ℝ))) < 1 / 2 :=
    hε.eventually (gt_mem_nhds (by norm_num))
  have h2 : ∀ᶠ N : ℕ in Filter.atTop, 2 * Real.log ((B : ℝ) + 1) < Real.log (N : ℝ) :=
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_gt_atTop _
  obtain ⟨N, hN1, hN2, hN3, hN4⟩ :=
    (h1.and (h2.and ((Filter.eventually_ge_atTop N₀).and (Filter.eventually_ge_atTop (B + 1))))).exists
  refine ⟨N, hN3, ?_⟩
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have : 0 < N := by omega
    exact_mod_cast this
  have hB0 : 0 ≤ Real.log ((B : ℝ) + 1) := Real.log_nonneg (by
    have : (0 : ℝ) ≤ (B : ℝ) := Nat.cast_nonneg B
    linarith)
  have hlogN : 0 < Real.log (N : ℝ) := by linarith
  have hsum := OMA.harm_ge B N (by omega)
  have hmono : Real.log (N : ℝ) ≤ Real.log ((N : ℝ) + 1) :=
    Real.log_le_log hNpos (by linarith)
  have hlhs : K * (Real.log (Real.log (Real.log (N : ℝ))) / Real.log (Real.log (N : ℝ)) *
      Real.log (N : ℝ)) ≤ 1 / 2 * Real.log (N : ℝ) := by
    have h := mul_le_mul_of_nonneg_right hN1.le hlogN.le
    calc K * (Real.log (Real.log (Real.log (N : ℝ))) / Real.log (Real.log (N : ℝ)) *
          Real.log (N : ℝ))
        = K * (Real.log (Real.log (Real.log (N : ℝ))) / Real.log (Real.log (N : ℝ))) *
          Real.log (N : ℝ) := by ring
      _ ≤ 1 / 2 * Real.log (N : ℝ) := h
  linarith
