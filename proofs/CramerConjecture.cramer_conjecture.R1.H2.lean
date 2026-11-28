import OMAReductions.R_CramerConjecture_cramer_conjecture_R1

/-!
# Proof of `CramerConjecture.cramer_conjecture.R1.H2`

Shows that for every `C > 0`, the sum of the von Mangoldt function `Λ(d)` over non-prime integers
`d ∈ [x, x + 2 ⌈C (log x)^2⌉₊)` is `o((log x)^2)` as `x → ∞`.

For sufficiently large `x`, we have `2 h < √x`, so for each exponent `k ≥ 2` at most one
prime power `p^k` can lie in `[x, x + 2h)` (since `(p + 1)^k - p^k ≥ 2 p^{k-1} ≥ 2 √x`).
Each such prime power contributes `Λ(p^k) = log p ≤ log(2x) / k`, and splitting the exponents
`2 ≤ k ≤ ⌊log_2(2x)⌋` at `√(log(2x))` bounds the total sum by `O((log x)^{3/2}) = o((log x)^2)`.
-/

open Filter Real Asymptotics ArithmeticFunction Finset

namespace CramerH2Proof

private lemma log_two_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)

private lemma prime_pow_gap_ge_two_sqrt {p k x : ℕ} (hk : 2 ≤ k) (hx : x ≤ p ^ k) :
    2 * Real.sqrt (x : ℝ) ≤ ((p + 1) ^ k : ℝ) - (p ^ k : ℝ) := by
  have hp1 : p ^ k + 2 * p ^ (k - 1) ≤ (p + 1) ^ k := by
    have hpow : (p + 1) ^ k = (p + 1) ^ 2 * (p + 1) ^ (k - 2) := by
      rw [← pow_add, show 2 + (k - 2) = k by omega]
    have hge1 : p ^ (k - 2) ≤ (p + 1) ^ (k - 2) := Nat.pow_le_pow_left (Nat.le_succ p) _
    have hsq : p ^ 2 + 2 * p ≤ (p + 1) ^ 2 := by nlinarith
    have hmul : (p ^ 2 + 2 * p) * p ^ (k - 2) ≤ (p + 1) ^ 2 * (p + 1) ^ (k - 2) :=
      Nat.mul_le_mul hsq hge1
    rw [← hpow] at hmul
    have hlhs : (p ^ 2 + 2 * p) * p ^ (k - 2) = p ^ k + 2 * p ^ (k - 1) := by
      rw [add_mul, ← pow_add, show 2 + (k - 2) = k by omega, mul_assoc]
      have : p * p ^ (k - 2) = p ^ (k - 1) := by
        rw [← pow_succ', show k - 2 + 1 = k - 1 by omega]
      rw [this]
    omega
  have hsq_ge : x ≤ (p ^ (k - 1)) ^ 2 := by
    rcases Nat.eq_zero_or_pos p with rfl | hp
    · simp [show k ≠ 0 by omega] at hx
      subst hx
      exact Nat.zero_le _
    · calc x ≤ p ^ k := hx
        _ ≤ p ^ (2 * (k - 1)) := Nat.pow_le_pow_right hp (by omega)
        _ = (p ^ (k - 1)) ^ 2 := by rw [mul_comm, pow_mul]
  have hsqrt : Real.sqrt (x : ℝ) ≤ (p ^ (k - 1) : ℝ) := by
    rw [Real.sqrt_le_left (by positivity)]
    exact_mod_cast hsq_ge
  have hp1_r : (p ^ k : ℝ) + 2 * (p ^ (k - 1) : ℝ) ≤ ((p + 1) ^ k : ℝ) := by
    exact_mod_cast hp1
  linarith

private lemma at_most_one_pow_in_interval {x L k : ℕ} (hk : 2 ≤ k)
    (hL : (L : ℝ) < 2 * Real.sqrt (x : ℝ))
    {p₁ p₂ : ℕ} (h1 : p₁ ^ k ∈ Ico x (x + L)) (h2 : p₂ ^ k ∈ Ico x (x + L)) :
    p₁ = p₂ := by
  by_contra hne
  wlog hlt : p₁ < p₂ generalizing p₁ p₂
  · exact this h2 h1 (Ne.symm hne) (by omega)
  have h1' := mem_Ico.mp h1
  have h2' := mem_Ico.mp h2
  have hle : (p₁ + 1) ^ k ≤ p₂ ^ k := Nat.pow_le_pow_left (by omega) k
  have hgap := prime_pow_gap_ge_two_sqrt hk h1'.1
  have hdiff : ((p₁ + 1) ^ k : ℝ) - (p₁ ^ k : ℝ) < (L : ℝ) := by
    have hle_r : ((p₁ + 1) ^ k : ℝ) ≤ (p₂ ^ k : ℝ) := by exact_mod_cast hle
    have hlt_r : (p₂ ^ k : ℝ) < (x : ℝ) + (L : ℝ) := by exact_mod_cast h2'.2
    have hx_r : (x : ℝ) ≤ (p₁ ^ k : ℝ) := by exact_mod_cast h1'.1
    linarith
  linarith

private lemma vonMangoldt_nonprime_eq_zero_or_pow {d : ℕ} (hd : ¬ d.Prime) (hne : Λ d ≠ 0) :
    ∃ p k : ℕ, p.Prime ∧ 2 ≤ k ∧ d = p ^ k ∧ (Λ d : ℝ) = Real.log (p : ℝ) := by
  have hpp : IsPrimePow d := by
    by_contra h
    exact hne (vonMangoldt_eq_zero_iff.mpr h)
  rcases hpp with ⟨p, k, hp_prime, hk_pos, hpk⟩
  have hp : p.Prime := Nat.prime_iff.mpr hp_prime
  have hk2 : 2 ≤ k := by
    by_contra hklt
    have hk1 : k = 1 := by omega
    subst hk1
    rw [pow_one] at hpk
    exact hd (hpk ▸ hp)
  refine ⟨p, k, hp, hk2, hpk.symm, ?_⟩
  rw [← hpk, vonMangoldt_apply_pow hk_pos.ne', vonMangoldt_apply_prime hp]

private lemma sum_nonprime_vonMangoldt_le {x L : ℕ} (hx : 4 ≤ x) (hLx : L ≤ x)
    (hL : (L : ℝ) < 2 * Real.sqrt (x : ℝ)) :
    ∑ d ∈ (Ico x (x + L)).filter (fun d => ¬ d.Prime), (Λ d : ℝ) ≤
      (Real.sqrt (Real.log (2 * (x : ℝ))) + 1) * Real.log (2 * (x : ℝ)) +
        (Real.log (2 * (x : ℝ)) / Real.log 2) * Real.sqrt (Real.log (2 * (x : ℝ))) := by
  set S := (Ico x (x + L)).filter (fun d => ¬ d.Prime)
  set U : ℝ := Real.log (2 * (x : ℝ))
  have hx_pos : (0 : ℝ) < (x : ℝ) := by positivity
  have h2x_ge : (8 : ℝ) ≤ 2 * (x : ℝ) := by
    have : (4 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
    linarith
  have hU_ge1 : (1 : ℝ) ≤ U := by
    have h1 : Real.exp 1 ≤ 2 * (x : ℝ) := by linarith [Real.exp_one_lt_d9]
    exact (Real.le_log_iff_exp_le (by positivity)).mpr h1
  have hU_pos : 0 < U := by linarith
  have hsqrtU_pos : 0 < Real.sqrt U := Real.sqrt_pos.mpr hU_pos
  set M : ℕ := Nat.floor (U / Real.log 2)
  set K : ℕ := Nat.floor (Real.sqrt U)
  -- Only elements with Λ d ≠ 0 contribute
  set T := S.filter (fun d => Λ d ≠ 0)
  have hST : ∑ d ∈ S, (Λ d : ℝ) = ∑ d ∈ T, (Λ d : ℝ) :=
    (Finset.sum_filter_of_ne (s := S) (p := fun d => Λ d ≠ 0) fun _ _ h => h).symm
  rw [hST]
  -- Map each d ∈ T to its prime-power exponent k = d.factorization (d.minFac)
  let expOf (d : ℕ) : ℕ := d.factorization d.minFac
  have hexp_spec : ∀ d ∈ T,
      d.minFac.Prime ∧ 2 ≤ expOf d ∧ expOf d ≤ M ∧ d = d.minFac ^ (expOf d) ∧
        (Λ d : ℝ) ≤ U / (expOf d : ℝ) := by
    intro d hd
    have hdS := (mem_filter.mp hd).1
    have hd_ne := (mem_filter.mp hd).2
    have hd_ico := (mem_filter.mp hdS).1
    have hd_np := (mem_filter.mp hdS).2
    obtain ⟨p, k, hp, hk2, hdpk, hΛ⟩ := vonMangoldt_nonprime_eq_zero_or_pow hd_np hd_ne
    have hmin : d.minFac = p := by
      have hdvd : d.minFac ∣ p ^ k := hdpk ▸ Nat.minFac_dvd d
      have hmin_prime : d.minFac.Prime := Nat.minFac_prime (by
        have h1 : 2 ^ 2 ≤ p ^ k := le_trans (Nat.pow_le_pow_left hp.two_le 2)
          (Nat.pow_le_pow_right hp.pos hk2)
        omega)
      exact (Nat.prime_dvd_prime_iff_eq hmin_prime hp).mp (hmin_prime.dvd_of_dvd_pow hdvd)
    have hexp : expOf d = k := by
      dsimp [expOf]
      rw [hmin, hdpk, Nat.Prime.factorization_pow hp, Finsupp.single_eq_same]
    have hd_le_2x : (d : ℝ) ≤ 2 * (x : ℝ) := by
      have h1 : d < x + L := (mem_Ico.mp hd_ico).2
      have h2 : d ≤ 2 * x := by omega
      exact_mod_cast h2
    have h2k_le : (2 : ℝ) ^ k ≤ 2 * (x : ℝ) := by
      have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
      calc (2 : ℝ) ^ k ≤ (p : ℝ) ^ k := pow_le_pow_left₀ (by norm_num) hp2 k
        _ = (d : ℝ) := by exact_mod_cast hdpk.symm
        _ ≤ 2 * (x : ℝ) := hd_le_2x
    have hk_le_M : k ≤ M := by
      refine Nat.le_floor ?_
      rw [le_div_iff₀ log_two_pos]
      have hlog := Real.log_le_log (by positivity) h2k_le
      rw [Real.log_pow] at hlog
      exact hlog
    have hΛ_le : (Λ d : ℝ) ≤ U / (k : ℝ) := by
      rw [hΛ, le_div_iff₀ (Nat.cast_pos.mpr (by omega))]
      have hp_pos : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hp.pos
      have hpk_le : ((p : ℝ) ^ k) ≤ 2 * (x : ℝ) := by
        have h1 : p ^ k ≤ 2 * x := by
          rw [← hdpk]; have := (mem_Ico.mp hd_ico).2; omega
        exact_mod_cast h1
      have hlog := Real.log_le_log (pow_pos hp_pos k) hpk_le
      rw [Real.log_pow] at hlog
      linarith
    exact ⟨hmin ▸ hp, hexp ▸ hk2, hexp ▸ hk_le_M, by rw [hmin, hexp]; exact hdpk, hexp ▸ hΛ_le⟩
  -- `expOf` is injective on `T`
  have hinj : Set.InjOn expOf (T : Set ℕ) := by
    intro d₁ hd₁ d₂ hd₂ heq
    have hs1 := hexp_spec d₁ hd₁
    have hs2 := hexp_spec d₂ hd₂
    have h1_ico : d₁.minFac ^ expOf d₁ ∈ Ico x (x + L) := by
      rw [← hs1.2.2.2.1]; exact (mem_filter.mp (mem_filter.mp hd₁).1).1
    have h2_ico : d₂.minFac ^ expOf d₁ ∈ Ico x (x + L) := by
      rw [heq, ← hs2.2.2.2.1]; exact (mem_filter.mp (mem_filter.mp hd₂).1).1
    have hp_eq := at_most_one_pow_in_interval hs1.2.1 hL h1_ico h2_ico
    rw [hs1.2.2.2.1, hs2.2.2.2.1, hp_eq, heq]
  -- Bound ∑_{d ∈ T} Λ(d) ≤ ∑_{d ∈ T} U / expOf d ≤ ∑_{k ∈ Icc 2 M} U / k
  have hsum_le : ∑ d ∈ T, (Λ d : ℝ) ≤ ∑ k ∈ Icc 2 M, U / (k : ℝ) := by
    calc ∑ d ∈ T, (Λ d : ℝ)
        ≤ ∑ d ∈ T, U / (expOf d : ℝ) := Finset.sum_le_sum fun d hd => (hexp_spec d hd).2.2.2.2
      _ = ∑ k ∈ T.image expOf, U / (k : ℝ) := (Finset.sum_image (f := fun k : ℕ => U / (k : ℝ))
          (by intro a ha b hb hab; exact hinj ha hb hab)).symm
      _ ≤ ∑ k ∈ Icc 2 M, U / (k : ℝ) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun k _ _ => by positivity)
          intro k hk
          rcases mem_image.mp hk with ⟨d, hd, rfl⟩
          exact mem_Icc.mpr ⟨(hexp_spec d hd).2.1, (hexp_spec d hd).2.2.1⟩
  -- Split Icc 2 M into k ≤ K and k > K
  have hsplit : ∑ k ∈ Icc 2 M, U / (k : ℝ) ≤
      (Real.sqrt U + 1) * U + (U / Real.log 2) * Real.sqrt U := by
    have hpart : ∑ k ∈ Icc 2 M, U / (k : ℝ) =
        ∑ k ∈ (Icc 2 M).filter (fun k => k ≤ K), U / (k : ℝ) +
        ∑ k ∈ (Icc 2 M).filter (fun k => ¬ k ≤ K), U / (k : ℝ) :=
      (Finset.sum_filter_add_sum_filter_not (Icc 2 M) (fun k => k ≤ K) _).symm
    rw [hpart]
    have hsmall : ∑ k ∈ (Icc 2 M).filter (fun k => k ≤ K), U / (k : ℝ) ≤
        (Real.sqrt U + 1) * U := by
      have hterm : ∀ k ∈ (Icc 2 M).filter (fun k => k ≤ K), U / (k : ℝ) ≤ U := by
        intro k hk
        have hk1 : (1 : ℝ) ≤ (k : ℝ) := by
          have := (mem_Icc.mp (mem_filter.mp hk).1).1
          exact_mod_cast (show 1 ≤ k by omega)
        exact div_le_self hU_pos.le hk1
      have hcard : ((Icc 2 M).filter (fun k => k ≤ K)).card ≤ K := by
        have hsub : (Icc 2 M).filter (fun k => k ≤ K) ⊆ Icc 1 K := by
          intro k hk
          have h1 := mem_Icc.mp (mem_filter.mp hk).1
          have h2 := (mem_filter.mp hk).2
          exact mem_Icc.mpr ⟨by omega, h2⟩
        exact (Finset.card_le_card hsub).trans (by simp)
      calc ∑ k ∈ (Icc 2 M).filter (fun k => k ≤ K), U / (k : ℝ)
          ≤ ∑ _k ∈ (Icc 2 M).filter (fun k => k ≤ K), U := Finset.sum_le_sum hterm
        _ = (((Icc 2 M).filter (fun k => k ≤ K)).card : ℝ) * U := by simp
        _ ≤ (K : ℝ) * U := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hU_pos.le
        _ ≤ (Real.sqrt U + 1) * U := by
            have hK : (K : ℝ) ≤ Real.sqrt U := Nat.floor_le hsqrtU_pos.le
            nlinarith
    have hlarge : ∑ k ∈ (Icc 2 M).filter (fun k => ¬ k ≤ K), U / (k : ℝ) ≤
        (U / Real.log 2) * Real.sqrt U := by
      have hterm : ∀ k ∈ (Icc 2 M).filter (fun k => ¬ k ≤ K), U / (k : ℝ) ≤ Real.sqrt U := by
        intro k hk
        have hgt : K < k := Nat.lt_of_not_le (mem_filter.mp hk).2
        have hsqrt_lt : Real.sqrt U < (k : ℝ) := (Nat.lt_floor_add_one (Real.sqrt U)).trans_le (by
          exact_mod_cast (show K + 1 ≤ k by omega))
        rw [div_le_iff₀ (by linarith)]
        calc U = Real.sqrt U * Real.sqrt U := (Real.mul_self_sqrt hU_pos.le).symm
          _ ≤ Real.sqrt U * (k : ℝ) := mul_le_mul_of_nonneg_left hsqrt_lt.le hsqrtU_pos.le
      have hcard : ((Icc 2 M).filter (fun k => ¬ k ≤ K)).card ≤ M := by
        have hsub : (Icc 2 M).filter (fun k => ¬ k ≤ K) ⊆ Icc 1 M := by
          intro k hk
          have h1 := mem_Icc.mp (mem_filter.mp hk).1
          exact mem_Icc.mpr ⟨by omega, h1.2⟩
        exact (Finset.card_le_card hsub).trans (by simp)
      calc ∑ k ∈ (Icc 2 M).filter (fun k => ¬ k ≤ K), U / (k : ℝ)
          ≤ ∑ _k ∈ (Icc 2 M).filter (fun k => ¬ k ≤ K), Real.sqrt U := Finset.sum_le_sum hterm
        _ = (((Icc 2 M).filter (fun k => ¬ k ≤ K)).card : ℝ) * Real.sqrt U := by simp
        _ ≤ (M : ℝ) * Real.sqrt U := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hsqrtU_pos.le
        _ ≤ (U / Real.log 2) * Real.sqrt U := by
            have hM : (M : ℝ) ≤ U / Real.log 2 := Nat.floor_le (by positivity)
            exact mul_le_mul_of_nonneg_right hM hsqrtU_pos.le
    linarith
  exact hsum_le.trans hsplit

private lemma tendsto_log_sq_div_sqrt :
    Tendsto (fun x : ℕ => (Real.log (x : ℝ)) ^ 2 / Real.sqrt (x : ℝ)) atTop (nhds 0) := by
  have h1 : Tendsto (fun t : ℝ => Real.log t / t ^ (1 / 4 : ℝ)) atTop (nhds 0) :=
    isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4) |>.tendsto_div_nhds_zero
  have h2 : Tendsto (fun t : ℝ => (Real.log t / t ^ (1 / 4 : ℝ)) ^ 2) atTop (nhds (0 ^ 2)) :=
    h1.pow 2
  rw [zero_pow (by norm_num)] at h2
  have h3 := h2.comp tendsto_natCast_atTop_atTop
  refine h3.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with x hx
  have hxpos : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (show 0 < x by omega)
  simp only [Function.comp_apply, div_pow]
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul hxpos.le, Real.sqrt_eq_rpow]
  norm_num

end CramerH2Proof

theorem OMA.solution : OMA.R_CramerConjecture_cramer_conjecture_R1.H2 := by
  intro C hC
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  have h_log_top : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h_sqrt_div : Tendsto (fun x : ℕ => 1 / Real.sqrt (Real.log (x : ℝ))) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp h_log_top)
  have h_inv_log : Tendsto (fun x : ℕ => 1 / Real.log (x : ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop h_log_top
  have h_L_small : ∀ᶠ x : ℕ in atTop,
      ((2 * ⌈C * (Real.log (x : ℝ)) ^ 2⌉₊ : ℕ) : ℝ) < 2 * Real.sqrt (x : ℝ) ∧
        2 * ⌈C * (Real.log (x : ℝ)) ^ 2⌉₊ ≤ x := by
    have ht := CramerH2Proof.tendsto_log_sq_div_sqrt
    have hε : 0 < 1 / (2 * C) := by positivity
    have h1 := (tendsto_order.mp ht).2 (1 / (2 * C)) hε
    have h2 : ∀ᶠ x : ℕ in atTop, (4 : ℝ) < Real.sqrt (x : ℝ) :=
      (tendsto_atTop.mp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop) 5).mono
        fun _ hx => by dsimp only [Function.comp_apply] at hx; linarith
    filter_upwards [h1, h2, eventually_ge_atTop (16 : ℕ)] with x hratio hsq4 hx16
    have hx_pos : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (show 0 < x by omega)
    have hsq_pos : 0 < Real.sqrt (x : ℝ) := Real.sqrt_pos.mpr hx_pos
    have hClog : C * (Real.log (x : ℝ)) ^ 2 < Real.sqrt (x : ℝ) / 2 := by
      have hmul := (div_lt_iff₀ hsq_pos).mp hratio
      have h2C : (0 : ℝ) < 2 * C := by positivity
      have : (2 * C) * ((Real.log (x : ℝ)) ^ 2) < (2 * C) * (1 / (2 * C) * Real.sqrt (x : ℝ)) :=
        mul_lt_mul_of_pos_left hmul h2C
      have hsimp : (2 * C) * (1 / (2 * C) * Real.sqrt (x : ℝ)) = Real.sqrt (x : ℝ) := by
        field_simp [hC.ne']
      linarith
    have hceil : (⌈C * (Real.log (x : ℝ)) ^ 2⌉₊ : ℝ) < C * (Real.log (x : ℝ)) ^ 2 + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    have hlt1 : ((2 * ⌈C * (Real.log (x : ℝ)) ^ 2⌉₊ : ℕ) : ℝ) < 2 * Real.sqrt (x : ℝ) := by
      push_cast; linarith
    have hle_x : 2 * ⌈C * (Real.log (x : ℝ)) ^ 2⌉₊ ≤ x := by
      have hsq_le : 2 * Real.sqrt (x : ℝ) ≤ (x : ℝ) := by
        have h4 : (4 : ℝ) ≤ Real.sqrt (x : ℝ) := hsq4.le
        have hsq2 : Real.sqrt (x : ℝ) * Real.sqrt (x : ℝ) = (x : ℝ) := Real.mul_self_sqrt hx_pos.le
        nlinarith
      exact_mod_cast (hlt1.le.trans hsq_le)
    exact ⟨hlt1, hle_x⟩
  -- Compare bound with c * (log x)^2
  set A : ℝ := 6 + 4 / Real.log 2
  have hA_pos : 0 < A := by
    have := CramerH2Proof.log_two_pos
    dsimp [A]; positivity
  have h_small_ratio : ∀ᶠ x : ℕ in atTop, 1 / Real.sqrt (Real.log (x : ℝ)) ≤ c / A :=
    (tendsto_order.mp h_sqrt_div).2 (c / A) (by positivity) |>.mono fun _ hx => hx.le
  have h_log_ge4 : ∀ᶠ x : ℕ in atTop, (4 : ℝ) ≤ Real.log (x : ℝ) :=
    tendsto_atTop.mp h_log_top 4
  filter_upwards [h_L_small, h_small_ratio, h_log_ge4, eventually_ge_atTop (4 : ℕ)]
    with x ⟨hL_lt, hL_le⟩ hrat hlog4 hx4
  set L := 2 * ⌈C * (Real.log (x : ℝ)) ^ 2⌉₊
  have hsum_nn : 0 ≤ ∑ d ∈ (Ico x (x + L)).filter (fun d => ¬ d.Prime), (Λ d : ℝ) :=
    Finset.sum_nonneg fun _ _ => vonMangoldt_nonneg
  have hlog_pos : 0 < Real.log (x : ℝ) := by linarith
  have hsqrt_pos : 0 < Real.sqrt (Real.log (x : ℝ)) := Real.sqrt_pos.mpr hlog_pos
  have hU_le : Real.log (2 * (x : ℝ)) ≤ 2 * Real.log (x : ℝ) := by
    have hx_pos : (0 : ℝ) < (x : ℝ) := by positivity
    rw [Real.log_mul (by norm_num) hx_pos.ne']
    have hlog2 : Real.log 2 ≤ 1 := by
      have : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
      exact (Real.log_le_iff_le_exp (by norm_num)).mpr this
    linarith
  have hU_pos : 0 < Real.log (2 * (x : ℝ)) := by
    have : (1 : ℝ) < 2 * (x : ℝ) := by
      have : (4 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx4
      linarith
    exact Real.log_pos this
  have hsqrtU_le : Real.sqrt (Real.log (2 * (x : ℝ))) ≤ 2 * Real.sqrt (Real.log (x : ℝ)) := by
    calc Real.sqrt (Real.log (2 * (x : ℝ)))
        ≤ Real.sqrt (4 * Real.log (x : ℝ)) := Real.sqrt_le_sqrt (by linarith)
      _ = 2 * Real.sqrt (Real.log (x : ℝ)) := by
          rw [Real.sqrt_mul (by norm_num), show Real.sqrt 4 = 2 by
            rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  have h1_le_sqrt : (1 : ℝ) ≤ Real.sqrt (Real.log (x : ℝ)) := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by linarith)
  have hbound := CramerH2Proof.sum_nonprime_vonMangoldt_le hx4 hL_le hL_lt
  have hbound2 : ∑ d ∈ (Ico x (x + L)).filter (fun d => ¬ d.Prime), (Λ d : ℝ) ≤
      A * (Real.log (x : ℝ) * Real.sqrt (Real.log (x : ℝ))) := by
    have hlog2_pos := CramerH2Proof.log_two_pos
    have h1 : (Real.sqrt (Real.log (2 * (x : ℝ))) + 1) * Real.log (2 * (x : ℝ)) ≤
        6 * (Real.log (x : ℝ) * Real.sqrt (Real.log (x : ℝ))) := by
      have ha : Real.sqrt (Real.log (2 * (x : ℝ))) + 1 ≤ 3 * Real.sqrt (Real.log (x : ℝ)) := by
        linarith
      nlinarith
    have h2 : (Real.log (2 * (x : ℝ)) / Real.log 2) * Real.sqrt (Real.log (2 * (x : ℝ))) ≤
        (4 / Real.log 2) * (Real.log (x : ℝ) * Real.sqrt (Real.log (x : ℝ))) := by
      have hdiv : Real.log (2 * (x : ℝ)) / Real.log 2 ≤ 2 * Real.log (x : ℝ) / Real.log 2 :=
        div_le_div_of_nonneg_right hU_le hlog2_pos.le
      have hmul := mul_le_mul hdiv hsqrtU_le (Real.sqrt_nonneg _) (by positivity)
      calc (Real.log (2 * (x : ℝ)) / Real.log 2) * Real.sqrt (Real.log (2 * (x : ℝ)))
          ≤ (2 * Real.log (x : ℝ) / Real.log 2) * (2 * Real.sqrt (Real.log (x : ℝ))) := hmul
        _ = (4 / Real.log 2) * (Real.log (x : ℝ) * Real.sqrt (Real.log (x : ℝ))) := by ring
    have hA_eq : A = 6 + 4 / Real.log 2 := rfl
    nlinarith
  have hbound3 : A * (Real.log (x : ℝ) * Real.sqrt (Real.log (x : ℝ))) ≤
      c * (Real.log (x : ℝ)) ^ 2 := by
    have hmul : A * (1 / Real.sqrt (Real.log (x : ℝ))) ≤ c := by
      have := mul_le_mul_of_nonneg_left hrat hA_pos.le
      rwa [mul_div_cancel₀ _ hA_pos.ne'] at this
    have hstep := mul_le_mul_of_nonneg_right hmul (sq_nonneg (Real.log (x : ℝ)))
    have heq : A * (1 / Real.sqrt (Real.log (x : ℝ))) * (Real.log (x : ℝ)) ^ 2 =
        A * (Real.log (x : ℝ) * Real.sqrt (Real.log (x : ℝ))) := by
      have hsq : Real.sqrt (Real.log (x : ℝ)) * Real.sqrt (Real.log (x : ℝ)) = Real.log (x : ℝ) :=
        Real.mul_self_sqrt hlog_pos.le
      field_simp [hsqrt_pos.ne']
      nlinarith
    linarith
  rw [Real.norm_of_nonneg hsum_nn, Real.norm_of_nonneg (sq_nonneg _)]
  linarith
