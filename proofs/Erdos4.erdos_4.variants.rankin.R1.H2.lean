import OMAReductions.R_Erdos4_erdos_4_variants_rankin_R1
import Mathlib.NumberTheory.Chebyshev

-- Step Erdos4.erdos_4.variants.rankin.R1.H2: hypothesis H2 of reduction Erdos4.erdos_4.variants.rankin.R1
-- Credit: @OrangeHeadz

/-!
Informal plan (a weak Chebyshev bound: π(x) ≥ √x for x ≥ 4096).

Mathlib has Chebyshev's lower bound π(n) ≥ (n log 2 - log (n + 1)) / log n (Chebyshev.pi_ge).
So it is enough to show √x * log x ≤ x log 2 - log (x + 1) for x ≥ 4096.
Put s = √x and t = √s, so x = t⁴ and t ≥ 8. Then log x = 4 log t ≤ 4 t - 4 (from
log t ≤ t - 1) and log (x + 1) ≤ log 2 + log x. With log 2 > 0.69 the inequality reduces to
4 t³ - 4 t² + 0.7 + 4 t - 4 ≤ 0.69 t⁴, which holds for t ≥ 8.
Finally x = (√x)² ≤ π(x)², and the statement in ℕ follows by casting.
-/

theorem OMA.solution : OMA.R_Erdos4_erdos_4_variants_rankin_R1.H2 := by
  unfold OMA.R_Erdos4_erdos_4_variants_rankin_R1.H2
  refine ⟨4096, fun x hx => ?_⟩
  have hX : (4096 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  have hX0 : (0 : ℝ) < (x : ℝ) := by linarith
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = Real.sqrt (x : ℝ) := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = Real.sqrt s := ⟨_, rfl⟩
  have hs64 : 64 ≤ s := by
    rw [hs, Real.le_sqrt' (by norm_num)]
    have h : (64 : ℝ) ^ 2 = 4096 := by norm_num
    rw [h]
    exact hX
  have ht8 : 8 ≤ t := by
    rw [ht, Real.le_sqrt' (by norm_num)]
    have h : (8 : ℝ) ^ 2 = 64 := by norm_num
    rw [h]
    exact hs64
  have ht0 : 0 ≤ t := by linarith
  have hs2 : s ^ 2 = x := by
    rw [hs]
    exact Real.sq_sqrt hX0.le
  have ht2 : t ^ 2 = s := by
    rw [ht]
    exact Real.sq_sqrt (by linarith)
  have hlogs : Real.log s = Real.log x / 2 := by
    rw [hs]
    exact Real.log_sqrt hX0.le
  have hlogt' : Real.log t = Real.log s / 2 := by
    rw [ht]
    exact Real.log_sqrt (by linarith)
  have hlogt : Real.log t ≤ t - 1 := Real.log_le_sub_one_of_pos (by linarith)
  have hlog_le : Real.log x ≤ 4 * t - 4 := by linarith
  have hlogpos : 0 < Real.log x := Real.log_pos (by linarith)
  have hlog1 : Real.log ((x : ℝ) + 1) ≤ Real.log 2 + Real.log x := by
    rw [← Real.log_mul (by norm_num) hX0.ne']
    exact Real.log_le_log (by linarith) (by linarith)
  have hL : (0.69 : ℝ) < Real.log 2 := by
    have h := Real.log_two_gt_d9
    linarith
  have hL1 : Real.log 2 < (0.7 : ℝ) := by
    have h := Real.log_two_lt_d9
    linarith
  have hx4 : (x : ℝ) = t ^ 4 := by
    rw [← hs2, ← ht2]
    ring
  have h_a : s * Real.log x ≤ s * (4 * t - 4) :=
    mul_le_mul_of_nonneg_left hlog_le (by linarith)
  have h_b : s * (4 * t - 4) = 4 * t ^ 3 - 4 * t ^ 2 := by
    rw [← ht2]
    ring
  have h_c : (0.69 : ℝ) * t ^ 4 ≤ Real.log 2 * t ^ 4 :=
    mul_le_mul_of_nonneg_right hL.le (by positivity)
  have h_d : (5.52 : ℝ) * t ^ 3 ≤ 0.69 * t ^ 4 := by
    have h := mul_nonneg (pow_nonneg ht0 3) (sub_nonneg.mpr ht8)
    nlinarith [h]
  have h_e : 4 * t ≤ t ^ 3 := by
    have h := mul_nonneg ht0 (show (0 : ℝ) ≤ t ^ 2 - 4 by nlinarith)
    nlinarith [h]
  have key : s * Real.log x ≤ (x : ℝ) * Real.log 2 - Real.log ((x : ℝ) + 1) := by
    have hxL : (x : ℝ) * Real.log 2 = Real.log 2 * t ^ 4 := by
      rw [hx4]
      ring
    have ht3 : 0 ≤ t ^ 3 := pow_nonneg ht0 3
    have ht2' : 0 ≤ t ^ 2 := sq_nonneg t
    linarith
  have hpi := Chebyshev.pi_ge x
  have hsle : s ≤ (Nat.primeCounting x : ℝ) := by
    refine le_trans ?_ hpi
    rw [le_div_iff₀ hlogpos]
    exact key
  have hsq : (x : ℝ) ≤ (Nat.primeCounting x : ℝ) ^ 2 := by
    rw [← hs2]
    exact pow_le_pow_left₀ (by linarith) hsle 2
  exact_mod_cast hsq
