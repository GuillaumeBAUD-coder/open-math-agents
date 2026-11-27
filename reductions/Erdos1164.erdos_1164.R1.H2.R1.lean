import OMAReductions.R_Erdos1164_erdos_1164_R1

-- Reduction Erdos1164.erdos_1164.R1.H2.R1 of step Erdos1164.erdos_1164.R1.H2
-- Credit: @green-notes

/-!
Split the upper bound on the covering radius of the 2D simple random walk into two
independent components:
1. `H1`: discounted Green-function lower bound on the non-hitting probability `1 - E[s^τ_u]`
   for even axis points `u = (a, 0)` with `|a| ≥ d` and `s = 1 - 1/n`.
2. `H2`: discounted Matthews covering-time upper bound for any finite set `S` (`0 ∉ S`) whose
   pairwise discounted hitting probabilities are bounded away from `1` by `q`.
`main` combines them on the set `S = {(j * d, 0) | 1 ≤ j ≤ M}` inside `closedDisc r`.
-/

open MeasureTheory Filter
open scoped ProbabilityTheory Real ENNReal

namespace OMA.R_Erdos1164_erdos_1164_R1_H2_R1

open Erdos1165 Erdos1164 OMA.R_Erdos1164_erdos_1164_R1

def H1 : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      {X : ℕ → Ω → ℤ × ℤ}, IsSimpleRandomWalkSteps X →
      ∀ (n d : ℕ), 4 ≤ d → d ≤ n → ∀ a : ℤ, 2 ∣ a → (d : ℤ) ≤ |a| →
        c * Real.log d / Real.log n ≤
          1 - ∑' k : ℕ, (1 - (1 : ℝ) / n) ^ (k + 1) *
            (ℙ {ω | position X (k + 1) ω = (a, 0) ∧
              ∀ j < k + 1, position X j ω ≠ (a, 0)}).toReal

def H2 : Prop :=
  ∀ {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {X : ℕ → Ω → ℤ × ℤ}, IsSimpleRandomWalkSteps X →
    ∀ (n : ℕ), 2 ≤ n → ∀ (S : Finset (ℤ × ℤ)),
      S.Nonempty → (0 : ℤ × ℤ) ∉ S → ∀ (q : ℝ), 0 ≤ q → q ≤ 1 →
      (∀ z ∈ S, ∀ w ∈ insert (0 : ℤ × ℤ) S, w ≠ z →
        q ≤ 1 - ∑' k : ℕ, (1 - (1 : ℝ) / n) ^ (k + 1) *
          (ℙ {ω | position X (k + 1) ω = z - w ∧
            ∀ j < k + 1, position X j ω ≠ z - w}).toReal) →
      (ℙ {ω | ∀ x ∈ S, ∃ k ≤ n, position X k ω = x}).toReal ≤
        4 * Real.exp (-(q / 2) * Real.log S.card)

lemma closedDisc_mono {r₁ r₂ : ℕ} (h : r₁ ≤ r₂) : closedDisc r₁ ⊆ closedDisc r₂ := by
  intro x hx
  have h1 : (r₁ : ℤ) ^ 2 ≤ (r₂ : ℤ) ^ 2 := by
    have : (r₁ : ℤ) ≤ (r₂ : ℤ) := Int.ofNat_le.mpr h
    nlinarith [Int.natCast_nonneg r₁]
  exact le_trans hx h1

lemma coveringRadius_le_of_not_covers {Ω : Type*} (X : ℕ → Ω → ℤ × ℤ) (n : ℕ) (ω : Ω)
    {r : ℕ} (h : ¬ Covers X n ω (closedDisc r)) :
    coveringRadius X n ω ≤ r := by
  refine csSup_le ⟨0, covers_closedDisc_zero X n ω⟩ ?_
  intro r' hr'
  by_contra hlt
  have hle : r ≤ r' := by omega
  exact h fun x hx ↦ hr' x (closedDisc_mono hle hx)

lemma log_coveringRadius_le_of_le {Ω : Type*} (X : ℕ → Ω → ℤ × ℤ) (n : ℕ) (ω : Ω)
    {C : ℝ} (hC : 0 ≤ C) {r : ℕ} (hr : (r : ℝ) ≤ Real.exp (C * Real.sqrt (Real.log n)))
    (hcov : coveringRadius X n ω ≤ r) :
    Real.log (coveringRadius X n ω) ≤ C * Real.sqrt (Real.log n) := by
  rcases Nat.eq_zero_or_pos (coveringRadius X n ω) with h0 | hpos
  · rw [h0, Nat.cast_zero, Real.log_zero]
    exact mul_nonneg hC (Real.sqrt_nonneg _)
  · have hpos' : (0 : ℝ) < (coveringRadius X n ω : ℝ) := Nat.cast_pos.mpr hpos
    have hle : (coveringRadius X n ω : ℝ) ≤ (r : ℝ) := Nat.cast_le.mpr hcov
    calc Real.log (coveringRadius X n ω) ≤ Real.log (r : ℝ) := Real.log_le_log hpos' hle
      _ ≤ Real.log (Real.exp (C * Real.sqrt (Real.log n))) :=
          Real.log_le_log (lt_of_lt_of_le hpos' hle) hr
      _ = C * Real.sqrt (Real.log n) := Real.log_exp _

lemma large_n_params {C : ℝ} (hC : 0 < C) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      ∃ r d M : ℕ,
        4 ≤ d ∧ 2 ∣ d ∧ d ≤ n ∧ 1 ≤ M ∧ M * d ≤ r ∧
        (r : ℝ) ≤ Real.exp (C * Real.sqrt (Real.log n)) ∧
        0 < Real.log n ∧
        (1 / 4 : ℝ) * C * Real.sqrt (Real.log n) ≤ Real.log d ∧
        (1 / 4 : ℝ) * C * Real.sqrt (Real.log n) ≤ Real.log M := by
  let B : ℝ := max (max (Real.log 64 / C) (4 * Real.log 4 / C)) C
  refine ⟨⌈Real.exp (B ^ 2 + 1)⌉₊ + 4, fun n hn ↦ ?_⟩
  have hn4 : 4 ≤ n := by omega
  have hlogn_ge : B ^ 2 + 1 ≤ Real.log n := by
    have h1 : Real.exp (B ^ 2 + 1) ≤ (⌈Real.exp (B ^ 2 + 1)⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈Real.exp (B ^ 2 + 1)⌉₊ : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast (by omega : ⌈Real.exp (B ^ 2 + 1)⌉₊ ≤ n)
    have h3 : Real.exp (B ^ 2 + 1) ≤ (n : ℝ) := h1.trans h2
    have h4 := Real.log_le_log (Real.exp_pos _) h3
    rwa [Real.log_exp] at h4
  have hlogn_pos : 0 < Real.log n := by
    have : 0 ≤ B ^ 2 := sq_nonneg B
    linarith
  have hsqrt_ge_B : B ≤ Real.sqrt (Real.log n) :=
    Real.le_sqrt_of_sq_le (by linarith)
  have hC_sqrt_le : C * Real.sqrt (Real.log n) ≤ Real.log n := by
    have h1 : C ≤ Real.sqrt (Real.log n) := (le_max_right _ _).trans hsqrt_ge_B
    calc C * Real.sqrt (Real.log n) ≤ Real.sqrt (Real.log n) * Real.sqrt (Real.log n) :=
          mul_le_mul_of_nonneg_right h1 (Real.sqrt_nonneg _)
      _ = Real.log n := Real.mul_self_sqrt hlogn_pos.le
  have hlog64_le : Real.log 64 ≤ C * Real.sqrt (Real.log n) := by
    have h1 : Real.log 64 / C ≤ Real.sqrt (Real.log n) :=
      ((le_max_left _ _).trans (le_max_left _ _)).trans hsqrt_ge_B
    exact ((div_le_iff₀ hC).mp h1).trans_eq (mul_comm _ _)
  have hlog4_le : 4 * Real.log 4 ≤ C * Real.sqrt (Real.log n) := by
    have h1 : 4 * Real.log 4 / C ≤ Real.sqrt (Real.log n) :=
      ((le_max_right _ _).trans (le_max_left _ _)).trans hsqrt_ge_B
    exact ((div_le_iff₀ hC).mp h1).trans_eq (mul_comm _ _)
  let r : ℕ := ⌊Real.exp (C * Real.sqrt (Real.log n))⌋₊
  have hr_le_exp : (r : ℝ) ≤ Real.exp (C * Real.sqrt (Real.log n)) :=
    Nat.floor_le (Real.exp_pos _).le
  have hr_le_n : r ≤ n := by
    have h1 : (r : ℝ) ≤ (n : ℝ) := by
      calc (r : ℝ) ≤ Real.exp (C * Real.sqrt (Real.log n)) := hr_le_exp
        _ ≤ Real.exp (Real.log n) := Real.exp_le_exp.mpr hC_sqrt_le
        _ = (n : ℝ) := Real.exp_log (by exact_mod_cast (by omega : 0 < n))
    exact Nat.cast_le.mp h1
  have hexp64 : (64 : ℝ) ≤ Real.exp (C * Real.sqrt (Real.log n)) := by
    calc (64 : ℝ) = Real.exp (Real.log 64) := (Real.exp_log (by norm_num)).symm
      _ ≤ Real.exp (C * Real.sqrt (Real.log n)) := Real.exp_le_exp.mpr hlog64_le
  have hr_ge_64 : 64 ≤ r := Nat.le_floor hexp64
  have hr_half_exp : Real.exp (C * Real.sqrt (Real.log n)) / 2 ≤ (r : ℝ) := by
    have h1 : Real.exp (C * Real.sqrt (Real.log n)) < (r : ℝ) + 1 := Nat.lt_floor_add_one _
    linarith
  let sr : ℕ := Nat.sqrt r
  have hsr_ge_8 : 8 ≤ sr := Nat.le_sqrt.mpr (by omega)
  have hsr_sq : sr * sr ≤ r := Nat.sqrt_le r
  have hr_lt_sq : r < (sr + 1) * (sr + 1) := Nat.lt_succ_sqrt r
  let d : ℕ := 2 * (sr / 2)
  have hd_even : 2 ∣ d := ⟨sr / 2, rfl⟩
  have hd_le_sr : d ≤ sr := by omega
  have hd_ge_4 : 4 ≤ d := by omega
  have hd_le_r : d ≤ r := by
    have : sr ≤ r := by nlinarith
    omega
  have hd_le_n : d ≤ n := hd_le_r.trans hr_le_n
  have hd_ge_half : (sr + 1 : ℝ) / 2 ≤ (d : ℝ) := by
    have : sr + 1 ≤ 2 * d := by omega
    have : (sr + 1 : ℝ) ≤ 2 * (d : ℝ) := by exact_mod_cast this
    linarith
  let M : ℕ := r / d
  have hM_ge_sr : sr ≤ M := (Nat.le_div_iff_mul_le (by omega)).mpr (by nlinarith)
  have hM_ge_half : (sr + 1 : ℝ) / 2 ≤ (M : ℝ) := by
    have : (sr : ℝ) ≤ (M : ℝ) := Nat.cast_le.mpr hM_ge_sr
    have : sr + 1 ≤ 2 * sr := by omega
    have : (sr + 1 : ℝ) ≤ 2 * (sr : ℝ) := by exact_mod_cast this
    linarith
  have hM_pos : 1 ≤ M := by omega
  have hMd_le_r : M * d ≤ r := Nat.div_mul_le_self r d
  have hsqrt_r_lt : Real.sqrt (r : ℝ) < (sr : ℝ) + 1 := by
    refine (Real.sqrt_lt' (by positivity)).mpr ?_
    have h1 : r < (sr + 1) ^ 2 := by rw [sq]; exact hr_lt_sq
    have h2 : (r : ℝ) < ((sr + 1 : ℕ) : ℝ) ^ 2 := by exact_mod_cast h1
    push_cast at h2
    exact h2
  have hE_half : Real.exp ((1 / 2 : ℝ) * (C * Real.sqrt (Real.log n))) / 4 ≤ (sr + 1 : ℝ) / 2 := by
    have h1 : Real.exp (C * Real.sqrt (Real.log n)) / 4 ≤ (r : ℝ) / 2 := by linarith
    have h2 : Real.exp ((1 / 2 : ℝ) * (C * Real.sqrt (Real.log n))) / 2 ≤ Real.sqrt (r : ℝ) := by
      refine Real.le_sqrt_of_sq_le ?_
      have hsq : (Real.exp ((1 / 2 : ℝ) * (C * Real.sqrt (Real.log n)))) ^ 2 =
          Real.exp (C * Real.sqrt (Real.log n)) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
      calc (Real.exp ((1 / 2 : ℝ) * (C * Real.sqrt (Real.log n))) / 2) ^ 2
          = Real.exp (C * Real.sqrt (Real.log n)) / 4 := by rw [div_pow, hsq]; norm_num
        _ ≤ (r : ℝ) / 2 := h1
        _ ≤ (r : ℝ) := by linarith [show (0 : ℝ) ≤ (r : ℝ) by positivity]
    linarith
  have hexp_pos : 0 < Real.exp ((1 / 2 : ℝ) * (C * Real.sqrt (Real.log n))) / 4 := by positivity
  have hlow : (1 / 4 : ℝ) * C * Real.sqrt (Real.log n) ≤
      Real.log (Real.exp ((1 / 2 : ℝ) * (C * Real.sqrt (Real.log n))) / 4) := by
    rw [Real.log_div (Real.exp_pos _).ne' (by norm_num), Real.log_exp]
    linarith
  exact ⟨r, d, M, hd_ge_4, hd_even, hd_le_n, hM_pos, hMd_le_r, hr_le_exp, hlogn_pos,
    hlow.trans (Real.log_le_log hexp_pos (hE_half.trans hd_ge_half)),
    hlow.trans (Real.log_le_log hexp_pos (hE_half.trans hM_ge_half))⟩

theorem main : H1 → H2 → OMA.R_Erdos1164_erdos_1164_R1.H2 := by
  intro h1 h2 Ω _ _ X hX ε hε
  obtain ⟨c₀, hc₀, hc₀_bound⟩ := h1
  let c : ℝ := min c₀ 1
  have hc_pos : 0 < c := lt_min hc₀ zero_lt_one
  have hc_le1 : c ≤ 1 := min_le_right _ _
  have hc_le0 : c ≤ c₀ := min_le_left _ _
  let C : ℝ := Real.sqrt (32 * (4 / ε) / c) + 1
  have hC_pos : 0 < C := by positivity
  have hC_sq : 4 / ε ≤ (c / 32) * C ^ 2 := by
    have h1' : 32 * (4 / ε) / c ≤ C ^ 2 := by
      have hnon : 0 ≤ 32 * (4 / ε) / c := by positivity
      have hsq : Real.sqrt (32 * (4 / ε) / c) ≤ C := by dsimp [C]; linarith
      calc 32 * (4 / ε) / c = (Real.sqrt (32 * (4 / ε) / c)) ^ 2 := (Real.sq_sqrt hnon).symm
        _ ≤ C ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hsq 2
    have h2' : (c / 32) * (32 * (4 / ε) / c) ≤ (c / 32) * C ^ 2 :=
      mul_le_mul_of_nonneg_left h1' (by positivity)
    have h3' : (c / 32) * (32 * (4 / ε) / c) = 4 / ε := by field_simp
    linarith
  have hC_exp : 4 * Real.exp (-((c / 32) * C ^ 2)) ≤ ε := by
    have h1' : 4 / ε ≤ Real.exp ((c / 32) * C ^ 2) := by
      have := Real.add_one_le_exp ((c / 32) * C ^ 2)
      linarith
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
    have := (div_le_iff₀ hε).mp h1'
    linarith
  obtain ⟨N₀, hN₀⟩ := large_n_params hC_pos
  refine ⟨C, eventually_atTop.mpr ⟨N₀ + 4, fun n hn ↦ ?_⟩⟩
  have hn2 : 2 ≤ n := by omega
  obtain ⟨r, d, M, hd_ge_4, hd_even, hd_le_n, hM_pos, hMd_le_r, hr_le_exp, hlogn_pos,
    hlogd_low, hlogM_low⟩ := hN₀ n (by omega)
  let S : Finset (ℤ × ℤ) := (Finset.Icc 1 M).image (fun j ↦ (((j * d : ℕ) : ℤ), (0 : ℤ)))
  have hS_ne : S.Nonempty :=
    ⟨(((1 * d : ℕ) : ℤ), (0 : ℤ)),
      Finset.mem_image.mpr ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hM_pos⟩, rfl⟩⟩
  have hS_zero : (0 : ℤ × ℤ) ∉ S := by
    intro h0
    obtain ⟨j, hj, hj0⟩ := Finset.mem_image.mp h0
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    have hjd : (j * d : ℕ) = 0 := by
      have := congrArg Prod.fst hj0
      simpa using this
    nlinarith
  have hS_card : S.card = M := by
    rw [Finset.card_image_of_injective]
    · simp
    · intro a b hab
      have h1' : (a * d : ℕ) = b * d := by
        have := congrArg Prod.fst hab
        simpa using this
      exact Nat.eq_of_mul_eq_mul_right (by omega) h1'
  have hS_sub : (S : Set (ℤ × ℤ)) ⊆ closedDisc r := by
    intro x hx
    rw [Finset.mem_coe] at hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
    have hjM : j ≤ M := (Finset.mem_Icc.mp hj).2
    have hjd : j * d ≤ r := (Nat.mul_le_mul_right d hjM).trans hMd_le_r
    show ((j * d : ℕ) : ℤ) ^ 2 + (0 : ℤ) ^ 2 ≤ (r : ℤ) ^ 2
    have hjd' : ((j * d : ℕ) : ℤ) ≤ (r : ℤ) := Int.ofNat_le.mpr hjd
    nlinarith [Int.natCast_nonneg (j * d)]
  let q : ℝ := c * Real.log d / Real.log n
  have hlogd_pos : 0 < Real.log d := Real.log_pos (by exact_mod_cast (by omega : 1 < d))
  have hlogd_le : Real.log d ≤ Real.log n := Real.log_le_log (by positivity) (by exact_mod_cast hd_le_n)
  have hq_nonneg : 0 ≤ q := by positivity
  have hq_le1 : q ≤ 1 := by
    dsimp [q]
    rw [div_le_one hlogn_pos]
    calc c * Real.log d ≤ 1 * Real.log d := mul_le_mul_of_nonneg_right hc_le1 hlogd_pos.le
      _ = Real.log d := one_mul _
      _ ≤ Real.log n := hlogd_le
  have hq_pair : ∀ z ∈ S, ∀ w ∈ insert (0 : ℤ × ℤ) S, w ≠ z →
      q ≤ 1 - ∑' k : ℕ, (1 - (1 : ℝ) / n) ^ (k + 1) *
        (ℙ {ω | position X (k + 1) ω = z - w ∧
          ∀ j < k + 1, position X j ω ≠ z - w}).toReal := by
    intro z hz w hw hwz
    obtain ⟨jz, hjz, rfl⟩ := Finset.mem_image.mp hz
    have hw_ex : ∃ iw : ℕ, iw ≤ M ∧ w = (((iw * d : ℕ) : ℤ), (0 : ℤ)) := by
      rcases Finset.mem_insert.mp hw with rfl | hwS
      · refine ⟨0, by omega, ?_⟩
        ext <;> simp
      · obtain ⟨iw, hiw, rfl⟩ := Finset.mem_image.mp hwS
        exact ⟨iw, (Finset.mem_Icc.mp hiw).2, rfl⟩
    obtain ⟨iw, -, rfl⟩ := hw_ex
    have hne : iw ≠ jz := by
      intro heq
      subst heq
      exact hwz rfl
    have hzw_eq : (((jz * d : ℕ) : ℤ), (0 : ℤ)) - (((iw * d : ℕ) : ℤ), (0 : ℤ)) =
        (((jz : ℤ) - iw) * (d : ℤ), (0 : ℤ)) := by
      ext <;> simp <;> ring
    rw [hzw_eq]
    have hdiv : (2 : ℤ) ∣ (((jz : ℤ) - iw) * (d : ℤ)) :=
      dvd_mul_of_dvd_right (Int.natCast_dvd_natCast.mpr hd_even) _
    have habs : (d : ℤ) ≤ |((jz : ℤ) - iw) * (d : ℤ)| := by
      rw [abs_mul, abs_of_nonneg (Int.natCast_nonneg d)]
      have h1' : (1 : ℤ) ≤ |(jz : ℤ) - iw| := by
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · rw [abs_of_pos (by omega)]; omega
        · rw [abs_of_neg (by omega)]; omega
      calc (d : ℤ) = 1 * (d : ℤ) := (one_mul _).symm
        _ ≤ |(jz : ℤ) - iw| * (d : ℤ) := mul_le_mul_of_nonneg_right h1' (Int.natCast_nonneg d)
    have hbound := hc₀_bound hX n d hd_ge_4 hd_le_n (((jz : ℤ) - iw) * (d : ℤ)) hdiv habs
    have hc_mul : q ≤ c₀ * Real.log d / Real.log n := by
      dsimp [q]
      gcongr
    exact hc_mul.trans hbound
  have hprob_cov : (ℙ {ω | ∀ x ∈ S, ∃ k ≤ n, position X k ω = x}).toReal ≤
      4 * Real.exp (-(q / 2) * Real.log S.card) :=
    h2 hX n hn2 S hS_ne hS_zero q hq_nonneg hq_le1 hq_pair
  have hexp_bound : (c / 32) * C ^ 2 ≤ (q / 2) * Real.log S.card := by
    rw [hS_card]
    dsimp [q]
    have h0 : 0 ≤ (1 / 4 : ℝ) * C * Real.sqrt (Real.log n) := by positivity
    have hmul : ((1 / 4 : ℝ) * C * Real.sqrt (Real.log n)) ^ 2 ≤ Real.log d * Real.log M := by
      calc ((1 / 4 : ℝ) * C * Real.sqrt (Real.log n)) ^ 2
          = ((1 / 4 : ℝ) * C * Real.sqrt (Real.log n)) * ((1 / 4 : ℝ) * C * Real.sqrt (Real.log n)) := sq _
        _ ≤ Real.log d * Real.log M := mul_le_mul hlogd_low hlogM_low h0 hlogd_pos.le
    have hsq : ((1 / 4 : ℝ) * C * Real.sqrt (Real.log n)) ^ 2 = (1 / 16 : ℝ) * C ^ 2 * Real.log n := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hlogn_pos.le]
      ring
    rw [hsq] at hmul
    have hln_ne : Real.log n ≠ 0 := hlogn_pos.ne'
    have hc2_nonneg : (0 : ℝ) ≤ c / 2 := by positivity
    calc (c / 32) * C ^ 2 = (c / 2) * ((1 / 16 : ℝ) * C ^ 2 * Real.log n) / Real.log n := by
          field_simp [hln_ne]; norm_num
      _ ≤ (c / 2) * (Real.log d * Real.log M) / Real.log n := by gcongr
      _ = (c * Real.log d / Real.log n / 2) * Real.log M := by ring
  have hprob_small : (ℙ {ω | ∀ x ∈ S, ∃ k ≤ n, position X k ω = x}).toReal ≤ ε := by
    refine hprob_cov.trans ?_
    refine (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by norm_num)).trans hC_exp
  let E_good : Set Ω := {ω | Real.log (coveringRadius X n ω) ≤ C * Real.sqrt (Real.log n)}
  have hmeas_good : MeasurableSet E_good :=
    meas_event hX.measurable n (fun k ↦ Real.log (k : ℝ) ≤ C * Real.sqrt (Real.log n))
  have hcompl_sub : E_goodᶜ ⊆ {ω | ∀ x ∈ S, ∃ k ≤ n, position X k ω = x} := by
    intro ω hω
    simp only [E_good, Set.mem_compl_iff, Set.mem_ofPred_eq, not_le] at hω
    have hcov_r : Covers X n ω (closedDisc r) := by
      by_contra hncov
      have hle := coveringRadius_le_of_not_covers X n ω hncov
      have hlog := log_coveringRadius_le_of_le X n ω hC_pos.le hr_le_exp hle
      linarith
    intro x hx
    exact hcov_r x (hS_sub hx)
  have hcompl_le : (ℙ E_goodᶜ).toReal ≤ ε := by
    calc (ℙ E_goodᶜ).toReal ≤ (ℙ {ω | ∀ x ∈ S, ∃ k ≤ n, position X k ω = x}).toReal :=
          ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hcompl_sub)
      _ ≤ ε := hprob_small
  rw [prob_compl_eq_one_sub hmeas_good, ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top,
    ENNReal.toReal_one] at hcompl_le
  linarith

end OMA.R_Erdos1164_erdos_1164_R1_H2_R1
