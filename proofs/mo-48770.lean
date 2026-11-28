import OMAStatements.S_mo_48770

open Filter Topology Set Metric
open scoped ENNReal

namespace OMA_mo_48770_aux

private lemma ofReal_abs_le_lipschitzSupNorm {X : Type*} [MetricSpace X] {s : Set X}
    {g : X → ℝ} {z : X} (hz : z ∈ s) :
    ENNReal.ofReal |g z| ≤ OMA.S_mo_48770.lipschitzSupNorm s g :=
  le_trans (le_biSup (fun x ↦ ENNReal.ofReal |g x|) hz) le_sup_left

private lemma ofReal_div_le_lipschitzSupNorm {X : Type*} [MetricSpace X] {s : Set X}
    {g : X → ℝ} {x y : X} (hx : x ∈ s) (hy : y ∈ s) :
    ENNReal.ofReal (|g x - g y| / dist x y) ≤ OMA.S_mo_48770.lipschitzSupNorm s g :=
  le_trans (le_biSup (fun b ↦ ENNReal.ofReal (|g x - g b| / dist x b)) hy)
    (le_trans (le_biSup (fun a ↦ ⨆ b ∈ s, ENNReal.ofReal (|g a - g b| / dist a b)) hx)
      le_sup_right)

private lemma exists_approx_seq {d : ℕ}
    {D : Set (EuclideanSpace ℝ (Fin d))}
    {Dseq : ℕ → Set (EuclideanSpace ℝ (Fin d))}
    {F : ℕ → EuclideanSpace ℝ (Fin d) → ℝ} {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hf : Continuous f)
    (hHaus : Tendsto (fun n ↦ hausdorffEDist (Dseq n) D) atTop (𝓝 0))
    (hF : ∀ K : Set (EuclideanSpace ℝ (Fin d)), IsCompact K →
      Tendsto (fun n ↦ OMA.S_mo_48770.lipschitzSupNorm K (fun z ↦ F n z - f z)) atTop (𝓝 0))
    {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ D) :
    ∃ (N : ℕ) (xseq : ℕ → EuclideanSpace ℝ (Fin d)),
      (∀ n ≥ N, xseq n ∈ Dseq n) ∧
      Tendsto xseq atTop (𝓝 x) ∧
      Tendsto (fun n ↦ F n (xseq n)) atTop (𝓝 (f x)) := by
  have hlt : ∀ᶠ n in atTop, hausdorffEDist (Dseq n) D < ⊤ :=
    hHaus.eventually (Iio_mem_nhds (by simp))
  obtain ⟨N, hN⟩ := eventually_atTop.mp hlt
  let ε : ℕ → ℝ≥0∞ := fun n ↦ ENNReal.ofReal (1 / ((n : ℝ) + 1))
  have hε_pos : ∀ n, 0 < ε n := fun n ↦ ENNReal.ofReal_pos.mpr (by positivity)
  have hEx : ∀ n, ∃ y, N ≤ n → y ∈ Dseq n ∧ edist x y < hausdorffEDist (Dseq n) D + ε n := by
    intro n
    by_cases hn : N ≤ n
    · have hne : hausdorffEDist (Dseq n) D ≠ ⊤ := (hN n hn).ne
      have hinf_le : Metric.infEDist x (Dseq n) ≤ hausdorffEDist (Dseq n) D := by
        rw [hausdorffEDist_comm]
        exact infEDist_le_hausdorffEDist_of_mem hx
      have hinf_lt : Metric.infEDist x (Dseq n) < hausdorffEDist (Dseq n) D + ε n :=
        lt_of_le_of_lt hinf_le (ENNReal.lt_add_right hne (hε_pos n).ne')
      rw [infEDist_lt_iff] at hinf_lt
      obtain ⟨y, hy_mem, hy_dist⟩ := hinf_lt
      exact ⟨y, fun _ ↦ ⟨hy_mem, hy_dist⟩⟩
    · exact ⟨x, fun h ↦ absurd h hn⟩
  choose xseq hxseq using hEx
  have hε_tendsto : Tendsto ε atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ ↦ (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa [ε, Function.comp_def] using (ENNReal.continuous_ofReal.tendsto 0).comp h1
  have hsum_tendsto : Tendsto (fun n ↦ hausdorffEDist (Dseq n) D + ε n) atTop (𝓝 0) := by
    simpa using hHaus.add hε_tendsto
  have hed_tendsto : Tendsto (fun n ↦ edist (xseq n) x) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℝ≥0∞)) atTop (𝓝 0)) hsum_tendsto
      (Eventually.of_forall fun _ ↦ by simp) ?_
    filter_upwards [eventually_ge_atTop N] with n hn
    rw [edist_comm]
    exact (hxseq n hn).2.le
  have hx_tendsto : Tendsto xseq atTop (𝓝 x) :=
    EMetric.tendsto_nhds.mpr fun δ hδ ↦ hed_tendsto.eventually (Iio_mem_nhds hδ)
  let K : Set (EuclideanSpace ℝ (Fin d)) := insert x (range xseq)
  have hK_compact : IsCompact K := hx_tendsto.isCompact_insert_range
  have hK_tendsto := hF K hK_compact
  have hdiff_ofReal :
      Tendsto (fun n ↦ ENNReal.ofReal |F n (xseq n) - f (xseq n)|) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℝ≥0∞)) atTop (𝓝 0)) hK_tendsto
      (fun _ ↦ by simp)
      (fun n ↦ ofReal_abs_le_lipschitzSupNorm (mem_insert_of_mem x (mem_range_self n)))
  have hdiff_abs : Tendsto (fun n ↦ |F n (xseq n) - f (xseq n)|) atTop (𝓝 0) := by
    have htoReal := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hdiff_ofReal
    simpa [Function.comp_def, ENNReal.toReal_ofReal (abs_nonneg _)] using htoReal
  have hdiff : Tendsto (fun n ↦ F n (xseq n) - f (xseq n)) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr (by simpa [Real.norm_eq_abs] using hdiff_abs)
  have hfx : Tendsto (fun n ↦ f (xseq n)) atTop (𝓝 (f x)) :=
    (hf.tendsto x).comp hx_tendsto
  have hFx : Tendsto (fun n ↦ F n (xseq n)) atTop (𝓝 (f x)) := by
    simpa [sub_add_cancel] using hdiff.add hfx
  exact ⟨N, xseq, fun n hn ↦ (hxseq n hn).1, hx_tendsto, hFx⟩

end OMA_mo_48770_aux

theorem OMA.solution : type_of% @OMA.S_mo_48770.main := by
  intro d D Dseq F f h h0 _hD _hK _hFcont hf hHaus hF hBounds
  unfold OMA.S_mo_48770.lipschitzSupNorm
  refine sup_le ?_ ?_
  · refine iSup₂_le fun x hx ↦ ?_
    obtain ⟨N, xseq, hx_mem, _, hFx⟩ := OMA_mo_48770_aux.exists_approx_seq hf hHaus hF hx
    have hle : |f x| ≤ h := by
      refine le_of_tendsto hFx.abs ?_
      filter_upwards [eventually_ge_atTop N] with n hn
      have h1 : ENNReal.ofReal |F n (xseq n)| ≤ ENNReal.ofReal h :=
        le_trans (OMA_mo_48770_aux.ofReal_abs_le_lipschitzSupNorm (hx_mem n hn)) (hBounds n)
      exact (ENNReal.ofReal_le_ofReal_iff h0).mp h1
    exact ENNReal.ofReal_le_ofReal hle
  · refine iSup₂_le fun x hx ↦ iSup₂_le fun y hy ↦ ?_
    by_cases hxy : x = y
    · subst hxy
      simp
    · have hdist_ne : dist x y ≠ 0 := (dist_pos.mpr hxy).ne'
      obtain ⟨Nx, xseq, hx_mem, hx_tendsto, hFx⟩ :=
        OMA_mo_48770_aux.exists_approx_seq hf hHaus hF hx
      obtain ⟨Ny, yseq, hy_mem, hy_tendsto, hFy⟩ :=
        OMA_mo_48770_aux.exists_approx_seq hf hHaus hF hy
      have hquot :
          Tendsto (fun n ↦ |F n (xseq n) - F n (yseq n)| / dist (xseq n) (yseq n))
            atTop (𝓝 (|f x - f y| / dist x y)) :=
        ((hFx.sub hFy).abs).div (hx_tendsto.dist hy_tendsto) hdist_ne
      have hle : |f x - f y| / dist x y ≤ h := by
        refine le_of_tendsto hquot ?_
        filter_upwards [eventually_ge_atTop (max Nx Ny)] with n hn
        have hnx : Nx ≤ n := le_trans (le_max_left Nx Ny) hn
        have hny : Ny ≤ n := le_trans (le_max_right Nx Ny) hn
        have h1 :
            ENNReal.ofReal (|F n (xseq n) - F n (yseq n)| / dist (xseq n) (yseq n)) ≤
              ENNReal.ofReal h :=
          le_trans
            (OMA_mo_48770_aux.ofReal_div_le_lipschitzSupNorm (hx_mem n hnx) (hy_mem n hny))
            (hBounds n)
        exact (ENNReal.ofReal_le_ofReal_iff h0).mp h1
      exact ENNReal.ofReal_le_ofReal hle
