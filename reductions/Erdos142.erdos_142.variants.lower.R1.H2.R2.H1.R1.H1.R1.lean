import OMAReductions.R_Erdos142_erdos_142_variants_lower_R1_H2_R2_H1_R1
import Mathlib

/-!
# Iterative density increment and qualitative Szemeredi reduction for the k = 4 color bound

Reduces the 4-term extremal bound `r 4 N < N / (⌈log N⌉₊ + 1) ^ 4` to two genuine inputs:
- `H1`: sparse 4-AP-free sets inside the subquadratic log-log budget admit an affine
  subprogression density increment (`p' + 1 ≤ p`) preserving `C * p ^ β + R ≤ log log N`.
- `H2`: qualitative 4-term Szemeredi theorem at each fixed positive density (`p ≤ T`).

In `main`, strong induction on `⌊p⌋₊` rules out any 4-AP-free set inside the budget,
inverting `C * p ^ β + R > log log N` yields `r 4 N ≤ 2 * N * exp (-((log log N - R) / C)^(1/β))`,
and `1 / β > 1` dominates `4 * log (log N)` asymptotically.
-/

namespace OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R2_H1_R1_H1_R1

open Erdos142 Filter Real

/-- Sparse 4-AP-free sets admit an affine density increment preserving a sublinear log-log budget. -/
def H1 : Prop :=
  ∃ (β C T R₀ : ℝ), 0 < β ∧ β < 1 ∧ 0 < C ∧
    ∀ R : ℝ, R₀ ≤ R → ∀ (N : ℕ) (S : Finset ℕ),
      2 ≤ N → S ⊆ Finset.Icc 1 N → 0 < S.card →
        (¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < 4, a + i * d ∈ S) →
      let p := max 2 (Real.log (2 * (N : ℝ) / (S.card : ℝ)))
      T < p → C * p ^ β + R ≤ Real.log (Real.log (N : ℝ)) →
        ∃ (a q M : ℕ), 0 < q ∧ 2 ≤ M ∧
          (∀ i ∈ Finset.Icc 1 M, a + (i - 1) * q ∈ Finset.Icc 1 N) ∧
          let U := (Finset.Icc 1 M).filter (fun i ↦ a + (i - 1) * q ∈ S)
          let p' := max 2 (Real.log (2 * (M : ℝ) / (U.card : ℝ)))
          0 < U.card ∧ p' + 1 ≤ p ∧ C * p' ^ β + R ≤ Real.log (Real.log (M : ℝ))

/-- Qualitative 4-term Szemeredi theorem at each fixed logarithmic density threshold. -/
def H2 : Prop :=
  ∀ T : ℝ, ∃ Q : ℝ, ∀ (N : ℕ) (S : Finset ℕ),
    2 ≤ N → S ⊆ Finset.Icc 1 N → 0 < S.card →
    (¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < 4, a + i * d ∈ S) →
    max 2 (Real.log (2 * (N : ℝ) / (S.card : ℝ))) ≤ T →
      Real.log (Real.log (N : ℝ)) < Q

lemma apFree_iff {A : Set ℕ} {k : ℕ} (hk : 1 < k) :
    A.IsAPOfLengthFree k ↔ ¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ A := by
  have hk' : (1 : ℕ∞) < (k : ℕ∞) := by exact_mod_cast hk
  constructor
  · rintro hA ⟨a, d, hd, hterms⟩
    let f (i : ℕ) := a + i * d
    let T := (Finset.range k).image f
    have hf : Function.Injective f := fun i j hij =>
      Nat.eq_of_mul_eq_mul_right hd (Nat.add_left_cancel hij)
    have hT : ((T : Finset ℕ) : Set ℕ) = {a + n • d | (n : ℕ) (_ : n < (k : ℕ∞))} := by
      ext x; simp [T, f]
    have hcard : T.card = k := by simp [T, Finset.card_image_of_injective _ hf]
    have hsub : (T : Set ℕ) ⊆ A := by
      intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      exact hterms i (Finset.mem_range.mp hi)
    exact hk'.not_ge (hA _ hsub ⟨a, d, by simp [hcard], hT⟩)
  · intro hno T hsub hT
    obtain ⟨a, d, hcard, hterms⟩ := hT
    have hmem (i : ℕ) (hi : i < k) : a + i * d ∈ T := by
      rw [hterms]; exact ⟨i, by exact_mod_cast hi, by simp⟩
    have hd : 0 < d := by
      by_contra! h
      have he : d = 0 := Nat.eq_zero_of_le_zero h
      have hs : T = {a} := by
        apply Set.Subset.antisymm
        · rw [hterms, he]; rintro _ ⟨i, -, rfl⟩; simp
        · apply Set.singleton_subset_iff.mpr; simpa using hmem 0 (by omega)
      rw [hs] at hcard; exact hk'.ne (by simpa using hcard)
    exact (hno ⟨a, d, hd, fun i hi => hsub (hmem i hi)⟩).elim

lemma exists_maximizer {k : ℕ} (hk : 1 < k) (N : ℕ) :
    ∃ S : Finset ℕ, S ⊆ Finset.Icc 1 N ∧ (S : Set ℕ).IsAPOfLengthFree k ∧
      r k N = S.card := by
  let C : Set ℕ := {m | ∃ S : Finset ℕ, ∃ _ : S ⊆ Finset.Icc 1 N,
    ∃ _ : (S : Set ℕ).IsAPOfLengthFree k, S.card = m}
  have hz : 0 ∈ C := by
    refine ⟨∅, Finset.empty_subset _, (apFree_iff hk).mpr ?_, rfl⟩
    rintro ⟨a, d, -, h⟩; simpa using h 0 (by omega)
  have hb : BddAbove C := by
    refine ⟨N, ?_⟩; rintro _ ⟨S, hS, -, rfl⟩; simpa using Finset.card_le_card hS
  obtain ⟨S, hS, hf, he⟩ := Nat.sSup_mem ⟨0, hz⟩ hb
  exact ⟨S, hS, hf, he.symm⟩

lemma pullback_free {a q M : ℕ} {S : Finset ℕ} (hq : 0 < q)
    (hfree : ¬ ∃ b d : ℕ, 0 < d ∧ ∀ i < 4, b + i * d ∈ S) :
    ¬ ∃ b d : ℕ, 0 < d ∧ ∀ i < 4,
      b + i * d ∈ (Finset.Icc 1 M).filter (fun i ↦ a + (i - 1) * q ∈ S) := by
  rintro ⟨b, d, hd, hmem⟩
  have hb1 : 1 ≤ b := by
    have h0 := Finset.mem_Icc.mp (Finset.mem_filter.mp (hmem 0 (by decide))).1
    simpa using h0.1
  refine hfree ⟨a + (b - 1) * q, d * q, Nat.mul_pos hd hq, fun i hi ↦ ?_⟩
  have hbi := (Finset.mem_filter.mp (hmem i hi)).2
  have hEq : a + (b + i * d - 1) * q = a + (b - 1) * q + i * (d * q) := by
    have hsub : b + i * d - 1 = (b - 1) + i * d := by omega
    rw [hsub, add_mul, ← add_assoc, mul_assoc]
  rwa [hEq] at hbi

theorem main : H1 → H2 → OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R2_H1_R1.H1 := by
  intro h1 h2
  obtain ⟨β, C, T, R₀, hβ0, hβ1, hC, hstep⟩ := h1
  obtain ⟨Q, hQ⟩ := h2 T
  let R : ℝ := max R₀ Q
  have hR₀ : R₀ ≤ R := le_max_left _ _
  have hQR : Q ≤ R := le_max_right _ _
  have hNo : ∀ n : ℕ, ∀ (N : ℕ) (S : Finset ℕ),
      2 ≤ N → S ⊆ Finset.Icc 1 N → 0 < S.card →
      (¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < 4, a + i * d ∈ S) →
      let p := max 2 (Real.log (2 * (N : ℝ) / (S.card : ℝ)))
      ⌊p⌋₊ = n → ¬ (C * p ^ β + R ≤ Real.log (Real.log (N : ℝ))) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro N S hN2 hSsub hScard hSfree
      dsimp only
      set p := max 2 (Real.log (2 * (N : ℝ) / (S.card : ℝ)))
      intro hfl hbud
      by_cases hT : p ≤ T
      · have hlt := hQ N S hN2 hSsub hScard hSfree hT
        have hp0 : 0 ≤ C * p ^ β := mul_nonneg hC.le (Real.rpow_nonneg
          (le_trans (by norm_num : (0 : ℝ) ≤ 2) (le_max_left _ _)) β)
        linarith
      · push Not at hT
        obtain ⟨a, q, M, hq, hM2, -, hUcard, hpdrop, hMbud⟩ :=
          hstep R hR₀ N S hN2 hSsub hScard hSfree hT hbud
        let U := (Finset.Icc 1 M).filter (fun i ↦ a + (i - 1) * q ∈ S)
        set p' := max 2 (Real.log (2 * (M : ℝ) / (U.card : ℝ)))
        have hp'0 : 0 ≤ p' := le_trans (by norm_num : (0 : ℝ) ≤ 2) (le_max_left _ _)
        have hfl_lt : ⌊p'⌋₊ < n := by
          have hle := Nat.floor_mono hpdrop
          rw [Nat.floor_add_one hp'0, hfl] at hle
          omega
        exact ih ⌊p'⌋₊ hfl_lt M U hM2 (Finset.filter_subset _ _) hUcard
          (pullback_free hq hSfree) rfl hMbud
  have hα_gt1 : 1 < 1 / β := (one_lt_div hβ0).mpr hβ1
  have hll_top : Tendsto (fun N : ℕ => Real.log (Real.log (N : ℝ))) atTop atTop :=
    tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hdom : Tendsto (fun x : ℝ => (x / (2 * C)) ^ (1 / β) - (4 * x + Real.log 32 + 1)) atTop atTop := by
    have hpow : Tendsto (fun x : ℝ => x ^ (1 / β - 1)) atTop atTop :=
      tendsto_rpow_atTop (by linarith)
    have hratio : Tendsto (fun x : ℝ => ((2 * C) ^ (-(1 / β)) * x ^ (1 / β - 1) - 4) * x -
        (Real.log 32 + 1)) atTop atTop := by
      have h1 : Tendsto (fun x : ℝ => (2 * C) ^ (-(1 / β)) * x ^ (1 / β - 1) - 4) atTop atTop := by
        simpa only [sub_eq_add_neg] using
          (hpow.const_mul_atTop (Real.rpow_pos_of_pos (by positivity) _)).atTop_add
            (tendsto_const_nhds (x := (-4 : ℝ)))
      simpa only [sub_eq_add_neg, id_eq] using
        (h1.atTop_mul_atTop₀ tendsto_id).atTop_add (tendsto_const_nhds (x := -(Real.log 32 + 1)))
    refine hratio.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have h2C : 0 < 2 * C := by positivity
    have h1 : (x / (2 * C)) ^ (1 / β) = (2 * C) ^ (-(1 / β)) * x ^ (1 / β) := by
      rw [Real.div_rpow hx.le h2C.le, Real.rpow_neg h2C.le, div_eq_inv_mul]
    have h2 : x ^ (1 / β) = x ^ (1 / β - 1) * x := by
      calc
        x ^ (1 / β) = x ^ ((1 / β - 1) + 1) := by congr 1; ring
        _ = x ^ (1 / β - 1) * x ^ (1 : ℝ) := Real.rpow_add hx _ _
        _ = x ^ (1 / β - 1) * x := by rw [Real.rpow_one]
    rw [h1, h2]; ring
  have hlog_top : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop 3,
    hlog_top.eventually (eventually_gt_atTop (2 : ℝ)),
    hll_top.eventually (eventually_gt_atTop (max (max (2 * R) 1) (4 * C * 2 ^ β))),
    (hdom.comp hll_top).eventually (eventually_gt_atTop (0 : ℝ))] with N hN3 hlog2 hll hbig
  have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hceil4_pos : (0 : ℝ) < (((⌈Real.log (N : ℝ)⌉₊ + 1) ^ 4 : ℕ) : ℝ) := by positivity
  obtain ⟨S, hSsub, hSfree, hScard⟩ := exists_maximizer (by decide : 1 < 4) N
  rw [hScard]
  by_cases hS0 : S.card = 0
  · rw [hS0, Nat.cast_zero]
    exact div_pos hN_pos hceil4_pos
  have hScard_pos : 0 < S.card := Nat.pos_of_ne_zero hS0
  have hNotBud := hNo ⌊max 2 (Real.log (2 * (N : ℝ) / (S.card : ℝ)))⌋₊ N S
    (by omega) hSsub hScard_pos ((apFree_iff (by decide : 1 < 4)).mp hSfree) rfl
  set p := max 2 (Real.log (2 * (N : ℝ) / (S.card : ℝ)))
  have hll_gt : C * p ^ β + R > Real.log (Real.log (N : ℝ)) := lt_of_not_ge hNotBud
  have hll_2R : 2 * R < Real.log (Real.log (N : ℝ)) :=
    lt_of_le_of_lt ((le_max_left _ _).trans (le_max_left _ _)) hll
  have hll_1 : 1 < Real.log (Real.log (N : ℝ)) :=
    lt_of_le_of_lt ((le_max_right _ _).trans (le_max_left _ _)) hll
  have hll_2β : 4 * C * 2 ^ β < Real.log (Real.log (N : ℝ)) :=
    lt_of_le_of_lt (le_max_right _ _) hll
  have hCp : Real.log (Real.log (N : ℝ)) / 2 < C * p ^ β := by linarith
  have hp_pos : 0 < p := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hp_gt2 : 2 < p := by
    by_contra! hp2
    have hpow : p ^ β ≤ 2 ^ β := Real.rpow_le_rpow hp_pos.le hp2 hβ0.le
    have hmul : C * p ^ β ≤ C * 2 ^ β := mul_le_mul_of_nonneg_left hpow hC.le
    linarith
  have hp_eq : p = Real.log (2 * (N : ℝ) / (S.card : ℝ)) := by
    dsimp [p]
    apply max_eq_right
    by_contra! h
    have h2 : max 2 (Real.log (2 * (N : ℝ) / (S.card : ℝ))) = 2 := max_eq_left h.le
    linarith
  have hp_lb : (Real.log (Real.log (N : ℝ)) / (2 * C)) ^ (1 / β) < p := by
    have h1 : Real.log (Real.log (N : ℝ)) / (2 * C) < p ^ β := by
      rw [div_lt_iff₀ (by positivity)]
      linarith
    have h2 := Real.rpow_lt_rpow (by positivity) h1 (one_div_pos.mpr hβ0)
    rwa [← Real.rpow_mul hp_pos.le, mul_one_div_cancel hβ0.ne', Real.rpow_one] at h2
  have hlog_bd : 4 * Real.log (Real.log (N : ℝ)) + Real.log 32 <
      Real.log (2 * (N : ℝ) / (S.card : ℝ)) := by
    dsimp only [Function.comp_apply] at hbig
    linarith
  have hceil_le : ((⌈Real.log (N : ℝ)⌉₊ + 1 : ℕ) : ℝ) ≤ 2 * Real.log (N : ℝ) := by
    have hlt : (⌈Real.log (N : ℝ)⌉₊ : ℝ) < Real.log (N : ℝ) + 1 :=
      Nat.ceil_lt_add_one (by linarith)
    push_cast; linarith
  have hceil4_le : (((⌈Real.log (N : ℝ)⌉₊ + 1) ^ 4 : ℕ) : ℝ) ≤ 16 * Real.log (N : ℝ) ^ 4 := by
    have h1 : (((⌈Real.log (N : ℝ)⌉₊ + 1 : ℕ) : ℝ)) ^ 4 ≤ (2 * Real.log (N : ℝ)) ^ 4 :=
      pow_le_pow_left₀ (by positivity) hceil_le 4
    have h2 : (((⌈Real.log (N : ℝ)⌉₊ + 1) ^ 4 : ℕ) : ℝ) =
        (((⌈Real.log (N : ℝ)⌉₊ + 1 : ℕ) : ℝ)) ^ 4 := by push_cast; rfl
    rw [h2]
    linarith [show (2 * Real.log (N : ℝ)) ^ 4 = 16 * Real.log (N : ℝ) ^ 4 by ring]
  have hexp_lhs : Real.exp (4 * Real.log (Real.log (N : ℝ)) + Real.log 32) =
      32 * Real.log (N : ℝ) ^ 4 := by
    rw [Real.exp_add, Real.exp_log (by norm_num),
      show 4 * Real.log (Real.log (N : ℝ)) = ((4 : ℕ) : ℝ) * Real.log (Real.log (N : ℝ)) by norm_num,
      ← Real.log_pow, Real.exp_log (pow_pos (by linarith) 4)]
    ring
  have hS_pos_R : (0 : ℝ) < (S.card : ℝ) := by exact_mod_cast hScard_pos
  have hexp_lt : 32 * Real.log (N : ℝ) ^ 4 < 2 * (N : ℝ) / (S.card : ℝ) := by
    rw [← hexp_lhs]
    have := Real.exp_lt_exp.mpr hlog_bd
    rwa [Real.exp_log (by positivity)] at this
  have hlt16 : (S.card : ℝ) < (N : ℝ) / (16 * Real.log (N : ℝ) ^ 4) := by
    rw [lt_div_iff₀ (by positivity)]
    have h1 := (lt_div_iff₀ hS_pos_R).mp hexp_lt
    linarith
  exact lt_of_lt_of_le hlt16 (div_le_div_of_nonneg_left hN_pos.le hceil4_pos hceil4_le)

end OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R2_H1_R1_H1_R1
