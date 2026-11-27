import OMAReductions.R_Erdos423_erdos_423_variants_upper_bound_R1
import Mathlib

/-! Proof of `Erdos423.erdos_423.variants.upper_bound.R1.H2` (Tang's transfer lemma):
every consecutive block sum of `{a 1, ..., a m}` in a Hofstadter sequence `a` appears in the
sequence itself and is bounded by `m * a m`, yielding `a (|S_m|) <= m * a m`. Given
`|S_m| >= C⁻¹ * m^(c - η)` for all `η > 0`, strong induction establishes
`a n <= A * n^(1/(c - 1) + ε)` for all `n >= 1`. -/

namespace OMA.Erdos423Transfer

open Filter Finset Asymptotics Real

private lemma le_apply_of_le {a : ℕ → ℕ} (ha : Erdos423.IsHofstadterSeq a) {i j : ℕ}
    (hi : 1 ≤ i) (hij : i ≤ j) : a i ≤ a j := by
  rcases eq_or_lt_of_le hij with rfl | hlt
  · exact le_rfl
  · exact ((Erdos423.IsHofstadterSeq.lt_iff_lt ha hi (by omega)).2 hlt).le

private lemma mem_range_of_isConsecutiveBlockSum {a : ℕ → ℕ} (ha : Erdos423.IsHofstadterSeq a)
    {m s : ℕ} (hs : Erdos423.IsConsecutiveBlockSum a (m + 1) s) :
    ∃ k : ℕ, 1 ≤ k ∧ a k = s := by
  classical
  obtain ⟨i, j, hi, hij, hjm, rfl⟩ := hs
  have hai_pos : 1 ≤ a i := Erdos423.IsHofstadterSeq.le_apply ha i hi |>.trans' hi
  have haj_ge2 : 2 ≤ a j := Erdos423.IsHofstadterSeq.le_apply ha j (by omega) |>.trans' (by omega)
  have hsum_gt : a j < ∑ l ∈ Finset.Icc i j, a l := by
    have hsub : ({i, j} : Finset ℕ) ⊆ Finset.Icc i j := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> simp [Finset.mem_Icc] <;> omega
    have hle : ∑ l ∈ ({i, j} : Finset ℕ), a l ≤ ∑ l ∈ Finset.Icc i j, a l :=
      Finset.sum_le_sum_of_subset hsub
    rw [Finset.sum_pair (by omega : i ≠ j)] at hle
    omega
  set s := ∑ l ∈ Finset.Icc i j, a l
  have hex : ∃ k : ℕ, 1 ≤ k ∧ s ≤ a k := by
    refine ⟨max s 1, le_max_right _ _, ?_⟩
    exact le_trans (le_max_left _ _) (Erdos423.IsHofstadterSeq.le_apply ha _ (le_max_right _ _))
  set k := Nat.find hex
  have hk_spec : 1 ≤ k ∧ s ≤ a k := Nat.find_spec hex
  have hk_ge3 : 3 ≤ k := by
    by_contra hlt
    have hk12 : k = 1 ∨ k = 2 := by omega
    rcases hk12 with hk1 | hk2
    · rw [hk1, ha.1] at hk_spec
      omega
    · rw [hk2, ha.2.1] at hk_spec
      omega
  have hk_pred : a (k - 1) < s := by
    by_contra hge
    push Not at hge
    have hmin := Nat.find_min hex (show k - 1 < k by omega)
    exact hmin ⟨by omega, hge⟩
  have hjk : j + 1 ≤ k := by
    by_contra hge
    have hkj : k ≤ j := by omega
    have hak_le : a k ≤ a j := le_apply_of_le ha hk_spec.1 hkj
    omega
  have hcb : Erdos423.IsConsecutiveBlockSum a k s := ⟨i, j, hi, hij, hjk, rfl⟩
  rcases eq_or_lt_of_le hk_spec.2 with heq | hlt
  · exact ⟨k, hk_spec.1, heq.symm⟩
  · exact absurd hcb ((ha.2.2 k hk_ge3).2.2 s hk_pred hlt)

private lemma apply_ncard_le_mul {a : ℕ → ℕ} (ha : Erdos423.IsHofstadterSeq a) {m : ℕ}
    (hm : 1 ≤ m) :
    let S := {s : ℕ | Erdos423.IsConsecutiveBlockSum a (m + 1) s}
    S.Finite ∧ (1 ≤ S.ncard → a S.ncard ≤ m * a m) := by
  classical
  intro S
  have hbound : ∀ s ∈ S, s ≤ m * a m := by
    intro s ⟨i, j, hi, hij, hjm, hs_eq⟩
    rw [hs_eq]
    calc
      ∑ l ∈ Finset.Icc i j, a l ≤ ∑ l ∈ Finset.Icc 1 m, a l := by
        apply Finset.sum_le_sum_of_subset
        intro l hl
        simp only [Finset.mem_Icc] at hl ⊢
        omega
      _ ≤ ∑ _l ∈ Finset.Icc 1 m, a m := by
        apply Finset.sum_le_sum
        intro l hl
        simp only [Finset.mem_Icc] at hl
        exact le_apply_of_le ha hl.1 hl.2
      _ = m * a m := by
        simp [Nat.card_Icc]
  have hSfin : S.Finite :=
    (Set.finite_Icc 0 (m * a m)).subset fun s hs => ⟨Nat.zero_le _, hbound s hs⟩
  refine ⟨hSfin, fun hcard1 => ?_⟩
  by_contra hgt
  push Not at hgt
  have hsub : S ⊆ a '' (Finset.Icc 1 (S.ncard - 1) : Set ℕ) := by
    intro s hs
    obtain ⟨k, hk1, rfl⟩ := mem_range_of_isConsecutiveBlockSum ha hs
    have hak_lt : a k < a S.ncard := lt_of_le_of_lt (hbound (a k) hs) hgt
    have hk_lt : k < S.ncard := (Erdos423.IsHofstadterSeq.lt_iff_lt ha hk1 hcard1).1 hak_lt
    refine ⟨k, ?_, rfl⟩
    simp only [Finset.coe_Icc, Set.mem_Icc]
    omega
  have hle : S.ncard ≤ (a '' (Finset.Icc 1 (S.ncard - 1) : Set ℕ)).ncard :=
    Set.ncard_le_ncard hsub ((Finset.finite_toSet _).image a)
  have himg : (a '' (Finset.Icc 1 (S.ncard - 1) : Set ℕ)).ncard ≤
      (Finset.Icc 1 (S.ncard - 1) : Set ℕ).ncard :=
    Set.ncard_image_le (Finset.finite_toSet _)
  have hIcc : (Finset.Icc 1 (S.ncard - 1) : Set ℕ).ncard = S.ncard - 1 := by
    rw [Set.ncard_coe_finset, Nat.card_Icc]
    omega
  omega

private lemma solve_H2 :
    OMA.R_Erdos423_erdos_423_variants_upper_bound_R1.H2 := by
  classical
  intro a ha c hc hcount ε hε
  set α : ℝ := (1 : ℝ) / (c - 1) + ε
  have hc1 : 0 < c - 1 := by linarith
  have hα_pos : 0 < α := by positivity
  set η : ℝ := min ((c - 1) / 2) ((ε * (c - 1)) / (2 * α))
  have hη_pos : 0 < η := lt_min (by positivity) (by positivity)
  have hη_lt1 : η ≤ (c - 1) / 2 := min_le_left _ _
  have hη_lt2 : η ≤ (ε * (c - 1)) / (2 * α) := min_le_right _ _
  set β : ℝ := c - η
  have hβ_gt1 : 1 < β := by dsimp [β]; linarith
  have hβ_pos : 0 < β := by linarith
  have hαβ_gt : α + 1 < α * β := by
    have hεc : 0 < ε * (c - 1) := mul_pos hε hc1
    have h1 : α * (c - 1) = 1 + ε * (c - 1) := by
      dsimp [α]
      field_simp [hc1.ne']
    have h2 : α * η ≤ ε * (c - 1) / 2 := by
      have := mul_le_mul_of_nonneg_left hη_lt2 hα_pos.le
      have hsimp : α * (ε * (c - 1) / (2 * α)) = ε * (c - 1) / 2 := by
        field_simp [hα_pos.ne']
      linarith
    have h3 : α * β = α * (c - 1) + α - α * η := by dsimp [β]; ring
    linarith
  have hexp_lt : (α + 1) / β < α := (div_lt_iff₀ hβ_pos).2 hαβ_gt
  set δ : ℝ := α - (α + 1) / β
  have hδ_pos : 0 < δ := by dsimp [δ]; linarith
  obtain ⟨C, hC, hM_ev⟩ := hcount η hη_pos
  obtain ⟨M₀, hM₀⟩ := Filter.eventually_atTop.1 hM_ev
  set M₁ : ℕ := max M₀ 2
  set K : ℝ := (2 * C ^ ((1 : ℝ) / β)) ^ (α + 1)
  have hK_pos : 0 < K := by positivity
  have h_large1 : ∀ᶠ n : ℕ in atTop, (M₁ : ℝ) ≤ (C * (n : ℝ)) ^ ((1 : ℝ) / β) := by
    have ht : Tendsto (fun n : ℕ => (C * (n : ℝ)) ^ ((1 : ℝ) / β)) atTop atTop :=
      (tendsto_rpow_atTop (by positivity : (0 : ℝ) < 1 / β)).comp
        (Tendsto.const_mul_atTop hC tendsto_natCast_atTop_atTop)
    exact ht.eventually_ge_atTop (M₁ : ℝ)
  have h_large2 : ∀ᶠ n : ℕ in atTop, (C * (n : ℝ)) ^ ((1 : ℝ) / β) + 2 < (n : ℝ) := by
    have hpow_pos : (0 : ℝ) < 1 - 1 / β := by
      have : (1 : ℝ) / β < 1 := (div_lt_one hβ_pos).2 hβ_gt1
      linarith
    have ht := ((tendsto_rpow_atTop hpow_pos).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop
      (C ^ ((1 : ℝ) / β) + 3)
    filter_upwards [ht, eventually_ge_atTop 2] with n hn hn2
    have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.2 (by omega)
    have hn1 : (1 : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / β) :=
      Real.one_le_rpow (by exact_mod_cast (show 1 ≤ n by omega)) (by positivity)
    have hmul : (n : ℝ) ^ (1 - 1 / β) * (n : ℝ) ^ ((1 : ℝ) / β) = (n : ℝ) := by
      rw [← Real.rpow_add hn_pos]
      norm_num
    have hCn : (C * (n : ℝ)) ^ ((1 : ℝ) / β) = C ^ ((1 : ℝ) / β) * (n : ℝ) ^ ((1 : ℝ) / β) :=
      Real.mul_rpow hC.le hn_pos.le
    simp only [Function.comp_apply] at hn
    calc
      (C * (n : ℝ)) ^ ((1 : ℝ) / β) + 2
          = C ^ ((1 : ℝ) / β) * (n : ℝ) ^ ((1 : ℝ) / β) + 2 := by rw [hCn]
      _ < (n : ℝ) ^ (1 - 1 / β) * (n : ℝ) ^ ((1 : ℝ) / β) := by nlinarith
      _ = (n : ℝ) := hmul
  have h_large3 : ∀ᶠ n : ℕ in atTop, K ≤ (n : ℝ) ^ δ :=
    ((tendsto_rpow_atTop hδ_pos).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop K
  have h_all := h_large1.and (h_large2.and (h_large3.and (eventually_ge_atTop 2)))
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1 h_all
  set A : ℝ := max 1 ((Finset.range (N₀ + 1)).sup' ⟨0, by simp⟩ (fun k => (a k : ℝ)))
  have hA_ge1 : 1 ≤ A := le_max_left _ _
  have hA_ge : ∀ k ≤ N₀, (a k : ℝ) ≤ A := fun k hk =>
    le_trans (Finset.le_sup' (f := fun k => (a k : ℝ)) (Finset.mem_range.2 (by omega)))
      (le_max_right _ _)
  have hmain : ∀ n : ℕ, 1 ≤ n → (a n : ℝ) ≤ A * (n : ℝ) ^ α := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn1
      by_cases hle : n ≤ N₀
      · have h1 : (1 : ℝ) ≤ (n : ℝ) ^ α := Real.one_le_rpow (by exact_mod_cast hn1) hα_pos.le
        calc
          (a n : ℝ) ≤ A := hA_ge n hle
          _ = A * 1 := by ring
          _ ≤ A * (n : ℝ) ^ α := mul_le_mul_of_nonneg_left h1 (by linarith)
      · push Not at hle
        obtain ⟨h1, h2, h3, h4⟩ := hN₀ n (by omega)
        set r : ℝ := (C * (n : ℝ)) ^ ((1 : ℝ) / β)
        set m : ℕ := ⌈r⌉₊
        have hm_ge_r : r ≤ (m : ℝ) := Nat.le_ceil r
        have hm_ge_M1 : M₁ ≤ m := by
          have : (M₁ : ℝ) ≤ (m : ℝ) := le_trans h1 hm_ge_r
          exact_mod_cast this
        have hm_ge_M0 : M₀ ≤ m := le_trans (le_max_left _ _) hm_ge_M1
        have hm_ge2 : 2 ≤ m := le_trans (le_max_right _ _) hm_ge_M1
        have hm_lt_n : m < n := by
          have hr_nn : 0 ≤ r := Real.rpow_nonneg (by positivity) _
          have hm_lt : (m : ℝ) < r + 1 := Nat.ceil_lt_add_one hr_nn
          have : (m : ℝ) < (n : ℝ) := by linarith
          exact_mod_cast this
        have hm_le_2r : (m : ℝ) ≤ 2 * r := by
          have hr_ge2 : (2 : ℝ) ≤ r := le_trans (by exact_mod_cast le_max_right M₀ 2) h1
          have hm_lt : (m : ℝ) < r + 1 := Nat.ceil_lt_add_one (by linarith)
          linarith
        set S := {s : ℕ | Erdos423.IsConsecutiveBlockSum a (m + 1) s}
        have hScard_ge : n ≤ S.ncard := by
          have hCm := hM₀ m hm_ge_M0
          have hr_pow : r ^ β = C * (n : ℝ) := by
            dsimp [r]
            rw [← Real.rpow_mul (by positivity), one_div_mul_cancel hβ_pos.ne', Real.rpow_one]
          have hm_pow : C * (n : ℝ) ≤ (m : ℝ) ^ β := by
            rw [← hr_pow]
            exact Real.rpow_le_rpow (Real.rpow_nonneg (by positivity) _) hm_ge_r hβ_pos.le
          have hCn_le : C * (n : ℝ) ≤ C * (S.ncard : ℝ) := le_trans hm_pow hCm
          have hn_le_R : (n : ℝ) ≤ (S.ncard : ℝ) := le_of_mul_le_mul_left hCn_le hC
          exact_mod_cast hn_le_R
        have han_le : a n ≤ m * a m := by
          have h1' : a n ≤ a S.ncard := le_apply_of_le ha hn1 hScard_ge
          have h2' : a S.ncard ≤ m * a m :=
            (apply_ncard_le_mul ha (by omega : 1 ≤ m)).2 (le_trans hn1 hScard_ge)
          exact le_trans h1' h2'
        have ham_ih : (a m : ℝ) ≤ A * (m : ℝ) ^ α := ih m hm_lt_n (by omega)
        have han_R : (a n : ℝ) ≤ A * (m : ℝ) ^ (α + 1) := by
          have hcast : (a n : ℝ) ≤ (m : ℝ) * (a m : ℝ) := by exact_mod_cast han_le
          have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.2 (by omega)
          calc
            (a n : ℝ) ≤ (m : ℝ) * (A * (m : ℝ) ^ α) :=
              le_trans hcast (mul_le_mul_of_nonneg_left ham_ih hm_pos.le)
            _ = A * ((m : ℝ) ^ α * (m : ℝ) ^ (1 : ℝ)) := by rw [Real.rpow_one]; ring
            _ = A * (m : ℝ) ^ (α + 1) := by rw [← Real.rpow_add hm_pos]
        have hm_pow_le : (m : ℝ) ^ (α + 1) ≤ K * (n : ℝ) ^ ((α + 1) / β) := by
          have hr_eq : 2 * r = (2 * C ^ ((1 : ℝ) / β)) * (n : ℝ) ^ ((1 : ℝ) / β) := by
            dsimp [r]
            rw [Real.mul_rpow hC.le (Nat.cast_nonneg n)]
            ring
          calc
            (m : ℝ) ^ (α + 1) ≤ (2 * r) ^ (α + 1) :=
              Real.rpow_le_rpow (Nat.cast_nonneg m) hm_le_2r (by linarith)
            _ = ((2 * C ^ ((1 : ℝ) / β)) * (n : ℝ) ^ ((1 : ℝ) / β)) ^ (α + 1) := by rw [hr_eq]
            _ = K * ((n : ℝ) ^ ((1 : ℝ) / β)) ^ (α + 1) := by
              rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg (Nat.cast_nonneg n) _)]
            _ = K * (n : ℝ) ^ ((α + 1) / β) := by
              rw [← Real.rpow_mul (Nat.cast_nonneg n), one_div_mul_eq_div]
        have hK_le : K * (n : ℝ) ^ ((α + 1) / β) ≤ (n : ℝ) ^ α := by
          have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.2 (by omega)
          calc
            K * (n : ℝ) ^ ((α + 1) / β) ≤ (n : ℝ) ^ δ * (n : ℝ) ^ ((α + 1) / β) :=
              mul_le_mul_of_nonneg_right h3 (Real.rpow_nonneg hn_pos.le _)
            _ = (n : ℝ) ^ (δ + (α + 1) / β) := by rw [← Real.rpow_add hn_pos]
            _ = (n : ℝ) ^ α := by congr 1; dsimp [δ]; ring
        calc
          (a n : ℝ) ≤ A * (m : ℝ) ^ (α + 1) := han_R
          _ ≤ A * (K * (n : ℝ) ^ ((α + 1) / β)) := mul_le_mul_of_nonneg_left hm_pow_le (by linarith)
          _ ≤ A * (n : ℝ) ^ α := mul_le_mul_of_nonneg_left hK_le (by linarith)
  rw [Asymptotics.isBigO_iff]
  refine ⟨A, ?_⟩
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _),
      Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
  exact hmain n hn

end OMA.Erdos423Transfer

theorem OMA.solution : OMA.R_Erdos423_erdos_423_variants_upper_bound_R1.H2 :=
  OMA.Erdos423Transfer.solve_H2
