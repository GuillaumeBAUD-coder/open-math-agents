import OMAStatements.S_oeis_a068598

-- Complete refutation of OEIS A068598: every admissible family is a collection of pairwise
-- disjoint nonempty subsets of Fin n, hence term(n) <= (n + 1)^n = exp(n log(n + 1)) = o(exp(b n^c))
-- for all b > 0 and c > 1.
-- Author: Paul Roulleau (@Solfanbtc) via Antigravity NEON-SWARM FACTORY v3

open OMA.S_oeis_a068598 Filter Topology

private noncomputable def encodeFamily {n : ℕ} (s : Family n) (i : Fin n) : Option (Fin n) := by
  classical
  exact if h : ∃ b ∈ s, i ∈ b then
    some (h.choose.min' ⟨i, h.choose_spec.2⟩)
  else none

private lemma mem_iff_encode_eq {n : ℕ} {s : Family n} (hs : admissible s)
    {b : Block n} (hb : b ∈ s) (hne : b.Nonempty) (i : Fin n) :
    i ∈ b ↔ encodeFamily s i = some (b.min' hne) := by
  classical
  unfold encodeFamily
  constructor
  · intro hi
    have hex : ∃ d ∈ s, i ∈ d := ⟨b, hb, hi⟩
    rw [dif_pos hex]
    congr 1
    have hdb : hex.choose = b := hs.2 hex.choose hex.choose_spec.1 b hb i hex.choose_spec.2 hi
    subst hdb
    rfl
  · intro heq
    by_cases hex : ∃ d ∈ s, i ∈ d
    · rw [dif_pos hex] at heq
      injection heq with hmin
      have hmb : b.min' hne ∈ b := Finset.min'_mem b hne
      have hmd : hex.choose.min' ⟨i, hex.choose_spec.2⟩ ∈ hex.choose :=
        Finset.min'_mem hex.choose ⟨i, hex.choose_spec.2⟩
      rw [hmin] at hmd
      have hdb : hex.choose = b := hs.2 hex.choose hex.choose_spec.1 b hb (b.min' hne) hmd hmb
      rw [← hdb]
      exact hex.choose_spec.2
    · rw [dif_neg hex] at heq
      cases heq

private lemma encodeFamily_injOn (n : ℕ) :
    Set.InjOn (encodeFamily (n := n)) {s : Family n | admissible s} := by
  classical
  intro s hs t ht heq
  have hsub : ∀ {u v : Family n}, admissible u → admissible v →
      encodeFamily u = encodeFamily v → u ⊆ v := by
    intro u v hu hv huv b hb
    have hne : b.Nonempty := (hu.1 b hb).1
    set m := b.min' hne
    have hm_in_b : m ∈ b := Finset.min'_mem b hne
    have hcode : encodeFamily v m = some m := by
      rw [← huv]
      exact (mem_iff_encode_eq hu hb hne m).mp hm_in_b
    unfold encodeFamily at hcode
    by_cases hex : ∃ d ∈ v, m ∈ d
    · rw [dif_pos hex] at hcode
      injection hcode with hmin
      set d := hex.choose
      have hd_mem : d ∈ v := hex.choose_spec.1
      have hd_ne : d.Nonempty := ⟨m, hex.choose_spec.2⟩
      have hdb : b = d := by
        ext i
        rw [mem_iff_encode_eq hu hb hne i, huv, mem_iff_encode_eq hv hd_mem hd_ne i, hmin]
      rw [hdb]
      exact hd_mem
    · rw [dif_neg hex] at hcode
      cases hcode
  exact Finset.Subset.antisymm (hsub hs ht heq) (hsub ht hs heq.symm)

private lemma term_le_pow (n : ℕ) (hn : 1 ≤ n) : term n ≤ (n + 1) ^ n := by
  classical
  have hne0 : n ≠ 0 := by omega
  unfold term
  rw [if_neg hne0]
  have h1 :
      (Finset.univ.filter (fun s : Family n =>
        admissible s ∧ ∀ t : Family n, s ⊆ t → admissible t → t = s)).card ≤
      (Finset.univ.filter (fun s : Family n => admissible s)).card := by
    apply Finset.card_le_card
    intro s hs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
    exact hs.1
  have h2 :
      (Finset.univ.filter (fun s : Family n => admissible s)).card ≤
      Fintype.card (Fin n → Option (Fin n)) := by
    calc
      (Finset.univ.filter (fun s : Family n => admissible s)).card
        = ((Finset.univ.filter (fun s : Family n => admissible s)).image encodeFamily).card := by
          symm
          apply Finset.card_image_of_injOn
          intro s hs t ht heq
          simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hs ht
          exact encodeFamily_injOn n hs ht heq
      _ ≤ (Finset.univ : Finset (Fin n → Option (Fin n))).card := Finset.card_le_univ _
      _ = Fintype.card (Fin n → Option (Fin n)) := rfl
  have h3 : Fintype.card (Fin n → Option (Fin n)) = (n + 1) ^ n := by
    simp [Fintype.card_fun, Fintype.card_option, Fintype.card_fin]
  omega

private lemma tendsto_term_div_zero {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 1 < c) :
    Tendsto (fun n : ℕ => (term n : ℝ) / (a * Real.exp (b * (n : ℝ) ^ c))) atTop (𝓝 0) := by
  set ε : ℝ := (c - 1) / 2
  have hε : 0 < ε := by simp [ε]; linarith
  have hc_eq : 1 + ε + ε = c := by simp [ε]; ring
  set K : ℝ := (2 : ℝ) ^ ε / ε + 1
  have h_rpow : Tendsto (fun n : ℕ => b * (n : ℝ) ^ ε) atTop atTop :=
    Filter.Tendsto.const_mul_atTop hb ((tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop)
  have hev_big : ∀ᶠ n : ℕ in atTop, K ≤ b * (n : ℝ) ^ ε :=
    h_rpow.eventually (Filter.eventually_ge_atTop K)
  have h_upper : Tendsto (fun n : ℕ => (1 / a) * Real.exp (-(n : ℝ))) atTop (𝓝 0) := by
    have hneg : Tendsto (fun n : ℕ => -(n : ℝ)) atTop atBot :=
      Filter.tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop
    have hexp : Tendsto (fun n : ℕ => Real.exp (-(n : ℝ))) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp hneg
    simpa using hexp.const_mul (1 / a)
  refine squeeze_zero' ?_ ?_ h_upper
  · exact Filter.Eventually.of_forall fun n => by positivity
  · filter_upwards [hev_big, Filter.eventually_ge_atTop 1] with n hK hn1
    have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
    have hterm : (term n : ℝ) ≤ ((n : ℝ) + 1) ^ n := by
      exact_mod_cast term_le_pow n hn1
    have hpow_exp : ((n : ℝ) + 1) ^ n = Real.exp ((n : ℝ) * Real.log ((n : ℝ) + 1)) := by
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by positivity)]
      ring_nf
    have hlog : Real.log ((n : ℝ) + 1) ≤ (2 : ℝ) ^ ε / ε * (n : ℝ) ^ ε := by
      have h1 : Real.log ((n : ℝ) + 1) ≤ ((n : ℝ) + 1) ^ ε / ε :=
        Real.log_le_rpow_div (by positivity) hε
      have h2 : (n : ℝ) + 1 ≤ 2 * (n : ℝ) := by
        have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
        linarith
      have h3 : ((n : ℝ) + 1) ^ ε ≤ (2 * (n : ℝ)) ^ ε :=
        Real.rpow_le_rpow (by positivity) h2 (le_of_lt hε)
      have h4 : (2 * (n : ℝ)) ^ ε = (2 : ℝ) ^ ε * (n : ℝ) ^ ε :=
        Real.mul_rpow (by norm_num) (le_of_lt hn_pos)
      calc
        Real.log ((n : ℝ) + 1) ≤ ((n : ℝ) + 1) ^ ε / ε := h1
        _ ≤ (2 * (n : ℝ)) ^ ε / ε := div_le_div_of_nonneg_right h3 (le_of_lt hε)
        _ = (2 : ℝ) ^ ε / ε * (n : ℝ) ^ ε := by rw [h4]; ring
    have hn1e : (n : ℝ) * (n : ℝ) ^ ε = (n : ℝ) ^ (1 + ε) := by
      rw [Real.rpow_add hn_pos, Real.rpow_one]
    have hnc : (n : ℝ) ^ c = (n : ℝ) ^ ε * (n : ℝ) ^ (1 + ε) := by
      rw [← hc_eq, Real.rpow_add hn_pos, mul_comm]
    have h1e_ge : (n : ℝ) ≤ (n : ℝ) ^ (1 + ε) := by
      have hge1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
      calc
        (n : ℝ) = (n : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ (n : ℝ) ^ (1 + ε) := Real.rpow_le_rpow_of_exponent_le hge1 (by linarith)
    have hexp_bound : (n : ℝ) * Real.log ((n : ℝ) + 1) - b * (n : ℝ) ^ c ≤ -(n : ℝ) := by
      have hm1 : (n : ℝ) * Real.log ((n : ℝ) + 1) ≤ (2 : ℝ) ^ ε / ε * (n : ℝ) ^ (1 + ε) := by
        calc
          (n : ℝ) * Real.log ((n : ℝ) + 1)
            ≤ (n : ℝ) * ((2 : ℝ) ^ ε / ε * (n : ℝ) ^ ε) :=
              mul_le_mul_of_nonneg_left hlog (le_of_lt hn_pos)
          _ = (2 : ℝ) ^ ε / ε * ((n : ℝ) * (n : ℝ) ^ ε) := by ring
          _ = (2 : ℝ) ^ ε / ε * (n : ℝ) ^ (1 + ε) := by rw [hn1e]
      have hm2 : K * (n : ℝ) ^ (1 + ε) ≤ b * (n : ℝ) ^ c := by
        rw [hnc, ← mul_assoc]
        exact mul_le_mul_of_nonneg_right hK (by positivity)
      have hK_def : K * (n : ℝ) ^ (1 + ε) = (2 : ℝ) ^ ε / ε * (n : ℝ) ^ (1 + ε) + (n : ℝ) ^ (1 + ε) := by
        simp [K]; ring
      linarith
    calc
      (term n : ℝ) / (a * Real.exp (b * (n : ℝ) ^ c))
        ≤ ((n : ℝ) + 1) ^ n / (a * Real.exp (b * (n : ℝ) ^ c)) :=
          div_le_div_of_nonneg_right hterm (by positivity)
      _ = (1 / a) * Real.exp ((n : ℝ) * Real.log ((n : ℝ) + 1) - b * (n : ℝ) ^ c) := by
          rw [hpow_exp, Real.exp_sub]
          field_simp [ne_of_gt ha, ne_of_gt (Real.exp_pos (b * (n : ℝ) ^ c))]
      _ ≤ (1 / a) * Real.exp (-(n : ℝ)) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp_bound) (by positivity)

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a068598.main) := by
  rintro ⟨a, b, c, ha, hb, hc, hlim⟩
  have h0 : (1 : ℝ) = 0 := tendsto_nhds_unique hlim (tendsto_term_div_zero ha hb hc)
  norm_num at h0
