import OMAReductions.R_Erdos244_erdos_244_variants_Romanoff_R1
import Mathlib.NumberTheory.Chebyshev

-- Step Erdos244.erdos_244.variants.Romanoff.R1.H1: hypothesis H1 of reduction Erdos244.erdos_244.variants.Romanoff.R1
-- Credit: @OrangeHeadz

/-!
Informal plan (the first moment in Romanoff's theorem, from Chebyshev's lower bound).

Let y = (x - 1) / 2, so 2y + 1 ≤ x ≤ 2y + 2. Every pair (p, k) with p ≤ y prime and
k ≤ L = Nat.log C y has C ^ k ≤ y, hence p + C ^ k ≤ 2y < x. So the count is at least
π(y) (L + 1).
Now y < C ^ (L + 1) gives log y < (L + 1) log C, and Mathlib's Chebyshev.pi_ge gives
π(y) log y ≥ y log 2 - log (y + 1). Therefore
  π(y) (L + 1) log C ≥ y log 2 - log (y + 1) ≥ y / 2 ≥ x / 8   for y ≥ 49,
using log (y + 1) ≤ log 8 + (y + 1) / 8 - 1. So c = 1 / (8 log C) and x₀ = 100 work.
-/

theorem OMA.solution : OMA.R_Erdos244_erdos_244_variants_Romanoff_R1.H1 := by
  unfold OMA.R_Erdos244_erdos_244_variants_Romanoff_R1.H1
  intro C hC
  have hlogC : 0 < Real.log C := Real.log_pos (by exact_mod_cast hC)
  refine ⟨1 / (8 * Real.log C), by positivity, 100, fun x hx => ?_⟩
  obtain ⟨y, hy⟩ : ∃ y, y = (x - 1) / 2 := ⟨_, rfl⟩
  have hy1 : 2 * y + 1 ≤ x := by omega
  have hy2 : x ≤ 2 * y + 2 := by omega
  have hy49 : 49 ≤ y := by omega
  have hsub : ((Finset.range (y + 1)).filter Nat.Prime) ×ˢ (Finset.range (Nat.log C y + 1)) ⊆
      (Finset.range x ×ˢ Finset.range x).filter
        (fun q : ℕ × ℕ => q.1.Prime ∧ q.1 + C ^ q.2 < x) := by
    intro q hq
    rw [Finset.mem_product, Finset.mem_filter, Finset.mem_range, Finset.mem_range] at hq
    obtain ⟨⟨hq1, hq2⟩, hq3⟩ := hq
    have hpow : C ^ q.2 ≤ y := Nat.pow_le_of_le_log (by omega) (by omega)
    have hk : q.2 < C ^ q.2 := Nat.lt_pow_self hC
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range]
    exact ⟨⟨by omega, by omega⟩, hq2, by omega⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_product, Finset.card_range] at hcard
  have hpi : ((Finset.range (y + 1)).filter Nat.Prime).card = Nat.primeCounting y := by
    show _ = Nat.count Nat.Prime (y + 1)
    rw [Nat.count_eq_card_filter_range]
  rw [hpi] at hcard
  have hy0 : (0 : ℝ) < (y : ℝ) := by exact_mod_cast (by omega : 0 < y)
  have hy49' : (49 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy49
  have hylog : 0 < Real.log y := Real.log_pos (by exact_mod_cast (by omega : 1 < y))
  have hpi_ge := Chebyshev.pi_ge y
  rw [div_le_iff₀ hylog] at hpi_ge
  have hL : Real.log y < ((Nat.log C y + 1 : ℕ) : ℝ) * Real.log C := by
    have h1 : y < C ^ (Nat.log C y + 1) := Nat.lt_pow_succ_log_self hC y
    have h2 : (y : ℝ) < (C : ℝ) ^ (Nat.log C y + 1) := by exact_mod_cast h1
    have h3 := Real.log_lt_log hy0 h2
    rw [Real.log_pow] at h3
    exact h3
  have hlog1 : Real.log ((y : ℝ) + 1) ≤ Real.log 8 + (((y : ℝ) + 1) / 8 - 1) := by
    have h : Real.log (((y : ℝ) + 1) / 8) ≤ ((y : ℝ) + 1) / 8 - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_div (by positivity) (by norm_num)] at h
    linarith
  have hlog8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    norm_num
  have hl2a := Real.log_two_gt_d9
  have hl2b := Real.log_two_lt_d9
  have h69 : (y : ℝ) * 0.69 ≤ (y : ℝ) * Real.log 2 :=
    mul_le_mul_of_nonneg_left (by linarith) hy0.le
  have hmain : (y : ℝ) / 2 ≤ (y : ℝ) * Real.log 2 - Real.log ((y : ℝ) + 1) := by
    linarith
  have hpi0 : (0 : ℝ) ≤ (Nat.primeCounting y : ℝ) := Nat.cast_nonneg _
  have hN : (y : ℝ) / 2 ≤
      ((Nat.primeCounting y * (Nat.log C y + 1) : ℕ) : ℝ) * Real.log C := by
    have h1 : (Nat.primeCounting y : ℝ) * Real.log y ≤
        (Nat.primeCounting y : ℝ) * (((Nat.log C y + 1 : ℕ) : ℝ) * Real.log C) :=
      mul_le_mul_of_nonneg_left hL.le hpi0
    have h2 : ((Nat.primeCounting y * (Nat.log C y + 1) : ℕ) : ℝ) * Real.log C =
        (Nat.primeCounting y : ℝ) * (((Nat.log C y + 1 : ℕ) : ℝ) * Real.log C) := by
      push_cast
      ring
    rw [h2]
    linarith
  have hx8 : (x : ℝ) / 8 ≤ (y : ℝ) / 2 := by
    have h : (x : ℝ) ≤ 2 * (y : ℝ) + 2 := by exact_mod_cast hy2
    linarith
  have hfinal : 1 / (8 * Real.log C) * (x : ℝ) ≤
      ((Nat.primeCounting y * (Nat.log C y + 1) : ℕ) : ℝ) := by
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
    linarith
  exact le_trans hfinal (by exact_mod_cast hcard)
