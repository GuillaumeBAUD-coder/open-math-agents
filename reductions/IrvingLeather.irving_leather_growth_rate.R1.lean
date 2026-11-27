import FormalConjectures.Paper.IrvingLeatherStableMatchings
import Mathlib.Analysis.Subadditive
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

-- Reduction IrvingLeather.irving_leather_growth_rate.R1 of The Irving–Leather conjecture on stable matchings — irving leather growth rate
-- Credit: @tatashbar
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- Proved here with no hypothesis: a_k^(1/2^k) is increasing (a_{k+1} >= a_k^2) and bounded by 3
-- (3 a_k <= 3^(2^k)), so it converges to c := sup_k a_k^(1/2^k), numerically about 2.280142.
-- (The truncated subtraction in irvingLeatherCount never truncates: 2 a_k^2 <= a_{k+1} <= 3 a_k^2.)
-- H1 and H2 are KNOWN classical results that are not yet formalized:
--   H1 = supermultiplicativity (put two instances side by side, each block ranked first),
--   H2 = the Irving-Leather construction (the inequality half of irving_leather_pow_two).
-- H3 is the OPEN core: M(n) <= c^n for all n (no size beats the Irving-Leather rate).
-- All three are needed: without H2 the constant sequence M = 1 would satisfy H1 and H3.
-- main: Fekete's lemma (Mathlib Subadditive.tendsto_lim) on -log M(n), with the limit
-- identified along n = 2^k by squeezing between log a_k / 2^k and log c.

open Filter
open scoped Topology

namespace OMA.R_IrvingLeather_irving_leather_growth_rate_R1

open IrvingLeather

/-- Supermultiplicativity of the maximum number of stable matchings: putting two instances side
by side (everyone ranks their own block first) multiplies the numbers of stable matchings. -/
def H1 : Prop :=
  ∀ m n : ℕ, maxStableMatchings m * maxStableMatchings n ≤ maxStableMatchings (m + n)

/-- The Irving–Leather construction: at size `2 ^ k` there is a profile with at least `a_k`
stable matchings. (This is the inequality half of `irving_leather_pow_two`.) -/
def H2 : Prop :=
  ∀ k : ℕ, irvingLeatherCount k ≤ maxStableMatchings (2 ^ k)

/-- The open core: no size beats the Irving–Leather growth rate, i.e.
`M(n) ≤ c ^ n` with `c = sup_k a_k ^ (1 / 2 ^ k) ≈ 2.280142`. -/
def H3 : Prop :=
  ∀ n : ℕ, (maxStableMatchings (n + 1) : ℝ) ^ (1 / ((n : ℝ) + 1)) ≤
    ⨆ k : ℕ, (irvingLeatherCount k : ℝ) ^ (1 / (2 : ℝ) ^ k)

lemma il_succ_succ (k : ℕ) :
    irvingLeatherCount (k + 1 + 1) =
      3 * irvingLeatherCount (k + 1) ^ 2 - 2 * irvingLeatherCount k ^ 4 := rfl

/-- `2 a_k^2 ≤ a_{k+1} ≤ 3 a_k^2`; in particular the truncated subtraction never truncates. -/
lemma il_bounds (k : ℕ) :
    1 ≤ irvingLeatherCount k ∧ 2 * irvingLeatherCount k ^ 2 ≤ irvingLeatherCount (k + 1) ∧
      irvingLeatherCount (k + 1) ≤ 3 * irvingLeatherCount k ^ 2 := by
  induction k with
  | zero => simp [irvingLeatherCount]
  | succ k ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    have hy4 : 2 * irvingLeatherCount k ^ 4 ≤ irvingLeatherCount (k + 1) ^ 2 := by
      have : 2 * irvingLeatherCount k ^ 2 * (2 * irvingLeatherCount k ^ 2) ≤
          irvingLeatherCount (k + 1) * irvingLeatherCount (k + 1) := Nat.mul_le_mul h2 h2
      nlinarith
    refine ⟨by nlinarith, ?_, ?_⟩
    · rw [il_succ_succ]
      apply Nat.le_sub_of_add_le
      linarith
    · rw [il_succ_succ]
      exact Nat.sub_le _ _

lemma il_le_pow (k : ℕ) : 3 * irvingLeatherCount k ≤ 3 ^ (2 ^ k) := by
  induction k with
  | zero => simp [irvingLeatherCount]
  | succ k ih =>
    have h := (il_bounds k).2.2
    calc 3 * irvingLeatherCount (k + 1) ≤ (3 * irvingLeatherCount k) ^ 2 := by nlinarith
      _ ≤ (3 ^ (2 ^ k)) ^ 2 := Nat.pow_le_pow_left ih 2
      _ = 3 ^ (2 ^ (k + 1)) := by rw [← pow_mul, pow_succ]

lemma il_rpow_mono (k : ℕ) :
    (irvingLeatherCount k : ℝ) ^ (1 / (2 : ℝ) ^ k) ≤
      (irvingLeatherCount (k + 1) : ℝ) ^ (1 / (2 : ℝ) ^ (k + 1)) := by
  have hb := il_bounds k
  have h0 : (0 : ℝ) ≤ irvingLeatherCount k := Nat.cast_nonneg _
  have hsqN : irvingLeatherCount k ^ 2 ≤ irvingLeatherCount (k + 1) := by linarith [hb.2.1]
  have hsq : (irvingLeatherCount k : ℝ) ^ (2 : ℕ) ≤ irvingLeatherCount (k + 1) := by
    exact_mod_cast hsqN
  calc (irvingLeatherCount k : ℝ) ^ (1 / (2 : ℝ) ^ k)
      = ((irvingLeatherCount k : ℝ) ^ (2 : ℕ)) ^ (1 / (2 : ℝ) ^ (k + 1)) := by
        rw [← Real.rpow_natCast (irvingLeatherCount k : ℝ) 2, ← Real.rpow_mul h0]
        congr 1
        rw [pow_succ]
        push_cast
        field_simp
    _ ≤ _ := Real.rpow_le_rpow (by positivity) hsq (by positivity)

lemma il_rpow_le_three (k : ℕ) :
    (irvingLeatherCount k : ℝ) ^ (1 / (2 : ℝ) ^ k) ≤ 3 := by
  have hN : irvingLeatherCount k ≤ 3 ^ (2 ^ k) := le_trans (by omega) (il_le_pow k)
  have hR : (irvingLeatherCount k : ℝ) ≤ (3 : ℝ) ^ (2 ^ k : ℕ) := by exact_mod_cast hN
  calc (irvingLeatherCount k : ℝ) ^ (1 / (2 : ℝ) ^ k)
      ≤ ((3 : ℝ) ^ (2 ^ k : ℕ)) ^ (1 / (2 : ℝ) ^ k) :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) hR (by positivity)
    _ = 3 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
        push_cast
        rw [mul_one_div_cancel (by positivity), Real.rpow_one]

theorem main : H1 → H2 → H3 → type_of% @IrvingLeather.irving_leather_growth_rate := by
  intro h1 h2 h3
  -- The Irving–Leather sequence converges to its supremum `c`.
  have hmono : Monotone (fun k : ℕ => (irvingLeatherCount k : ℝ) ^ (1 / (2 : ℝ) ^ k)) :=
    monotone_nat_of_le_succ il_rpow_mono
  have hbdd : BddAbove (Set.range
      (fun k : ℕ => (irvingLeatherCount k : ℝ) ^ (1 / (2 : ℝ) ^ k))) :=
    ⟨3, by rintro _ ⟨k, rfl⟩; exact il_rpow_le_three k⟩
  set c : ℝ := ⨆ k : ℕ, (irvingLeatherCount k : ℝ) ^ (1 / (2 : ℝ) ^ k) with hc
  have hxc : Tendsto (fun k : ℕ => (irvingLeatherCount k : ℝ) ^ (1 / (2 : ℝ) ^ k))
      atTop (𝓝 c) := tendsto_atTop_ciSup hmono hbdd
  have hx_le : ∀ k : ℕ, (irvingLeatherCount k : ℝ) ^ (1 / (2 : ℝ) ^ k) ≤ c :=
    fun k => le_ciSup hbdd k
  have hc1 : 1 ≤ c := by simpa [irvingLeatherCount] using hx_le 0
  have hcpos : 0 < c := by linarith
  refine ⟨c, ?_, hxc⟩
  -- Basic facts on `M`.
  have hM1 : 1 ≤ maxStableMatchings 1 := by simpa [irvingLeatherCount] using h2 0
  have hMpos : ∀ n : ℕ, 1 ≤ maxStableMatchings (n + 1) := by
    intro n
    induction n with
    | zero => exact hM1
    | succ n ih =>
      have := h1 (n + 1) 1
      nlinarith
  have hM0 : maxStableMatchings 0 ≤ 1 := by
    have := h1 0 1
    simp only [zero_add] at this
    nlinarith
  have hlog0 : Real.log (maxStableMatchings 0 : ℝ) ≤ 0 :=
    Real.log_nonpos (Nat.cast_nonneg _) (by exact_mod_cast hM0)
  -- Fekete's lemma for `u n = - log M(n)`.
  have hsub : Subadditive (fun n : ℕ => -Real.log (maxStableMatchings n : ℝ)) := by
    intro m n
    show -Real.log (maxStableMatchings (m + n) : ℝ) ≤
      -Real.log (maxStableMatchings m : ℝ) + -Real.log (maxStableMatchings n : ℝ)
    rcases m with _ | m
    · simp only [zero_add]; linarith
    rcases n with _ | n
    · simp only [add_zero]; linarith
    have hp1 : (0 : ℝ) < maxStableMatchings (m + 1) := by exact_mod_cast hMpos m
    have hp2 : (0 : ℝ) < maxStableMatchings (n + 1) := by exact_mod_cast hMpos n
    have hle : ((maxStableMatchings (m + 1) : ℝ)) * maxStableMatchings (n + 1) ≤
        maxStableMatchings (m + 1 + (n + 1)) := by exact_mod_cast h1 (m + 1) (n + 1)
    have := Real.log_le_log (mul_pos hp1 hp2) hle
    rw [Real.log_mul hp1.ne' hp2.ne'] at this
    linarith
  -- From H3: log M(n) / n ≤ log c.
  have hlogM : ∀ n : ℕ, Real.log (maxStableMatchings n : ℝ) / n ≤ Real.log c := by
    intro n
    rcases n with _ | n
    · simp only [CharP.cast_eq_zero, div_zero]; exact Real.log_nonneg hc1
    have hp : (0 : ℝ) < maxStableMatchings (n + 1) := by exact_mod_cast hMpos n
    have := Real.log_le_log (Real.rpow_pos_of_pos hp _) (h3 n)
    rw [Real.log_rpow hp] at this
    push_cast
    rw [div_eq_mul_one_div, mul_comm]
    exact this
  have hbddF : BddBelow (Set.range
      (fun n : ℕ => (-Real.log (maxStableMatchings n : ℝ)) / n)) := by
    refine ⟨-Real.log c, ?_⟩
    rintro _ ⟨n, rfl⟩
    have := hlogM n
    simp only [neg_div]
    linarith
  have hF := hsub.tendsto_lim hbddF
  have hg : Tendsto (fun n : ℕ => Real.log (maxStableMatchings n : ℝ) / n) atTop
      (𝓝 (-hsub.lim)) := by
    have := hF.neg
    refine this.congr (fun n => ?_)
    simp only [neg_div, neg_neg]
  -- Identify the limit along `n = 2 ^ k`.
  have hg2 : Tendsto (fun k : ℕ => Real.log (maxStableMatchings (2 ^ k) : ℝ) / ((2 ^ k : ℕ) : ℝ))
      atTop (𝓝 (-hsub.lim)) :=
    hg.comp (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)
  have hlogx : Tendsto (fun k : ℕ => Real.log ((irvingLeatherCount k : ℝ) ^ (1 / (2 : ℝ) ^ k)))
      atTop (𝓝 (Real.log c)) :=
    (Real.continuousAt_log hcpos.ne').tendsto.comp hxc
  have hg2' : Tendsto (fun k : ℕ => Real.log (maxStableMatchings (2 ^ k) : ℝ) / ((2 ^ k : ℕ) : ℝ))
      atTop (𝓝 (Real.log c)) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlogx tendsto_const_nhds (fun k => ?_)
      (fun k => hlogM (2 ^ k))
    have ha : (0 : ℝ) < irvingLeatherCount k := by exact_mod_cast (il_bounds k).1
    have hle : (irvingLeatherCount k : ℝ) ≤ maxStableMatchings (2 ^ k) := by exact_mod_cast h2 k
    show Real.log ((irvingLeatherCount k : ℝ) ^ (1 / (2 : ℝ) ^ k)) ≤
      Real.log (maxStableMatchings (2 ^ k) : ℝ) / ((2 ^ k : ℕ) : ℝ)
    rw [Real.log_rpow ha]
    push_cast
    have h2k : (0 : ℝ) < 2 ^ k := by positivity
    rw [le_div_iff₀ h2k]
    have hl := Real.log_le_log ha hle
    have he : 1 / (2 : ℝ) ^ k * Real.log (irvingLeatherCount k : ℝ) * 2 ^ k =
        Real.log (irvingLeatherCount k : ℝ) := by field_simp
    nlinarith [hl, he, h2k]
  have hL : -hsub.lim = Real.log c := tendsto_nhds_unique hg2 hg2'
  rw [hL] at hg
  -- Conclude for `M(n+1) ^ (1/(n+1))`.
  have hg' := (Real.continuous_exp.tendsto _).comp (hg.comp (tendsto_add_atTop_nat 1))
  rw [Real.exp_log hcpos] at hg'
  refine hg'.congr (fun n => ?_)
  have hp : (0 : ℝ) < maxStableMatchings (n + 1) := by exact_mod_cast hMpos n
  simp only [Function.comp_apply]
  rw [Real.rpow_eq_pow, Real.rpow_def_of_pos hp]
  congr 1
  push_cast
  ring

end OMA.R_IrvingLeather_irving_leather_growth_rate_R1
