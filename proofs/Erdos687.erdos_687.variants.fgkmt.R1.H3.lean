import OMAReductions.R_Erdos687_erdos_687_variants_fgkmt_R1
import Mathlib.NumberTheory.Chebyshev

/-!
# Chebyshev's estimate for primes in `(x, C x]`

Lower bound `π(N) log N ≥ N log 2 - log (N + 1)` from Mathlib (`Chebyshev.psi_ge`,
`Chebyshev.psi_le_primeCounting_mul_log`) and the upper bound `π(x) ≤ 8 x / log x`
(copied from the merged reduction `Erdos687.erdos_687.variants.iwaniec.R1` by @ItsNotTheGabs).
-/

namespace OMA_FGKMT_H3

open Filter Finset

lemma primeCounting_le_eight_mul_div_log {x : ℕ} (hx : 2 ≤ x) :
    (Nat.primeCounting x : ℝ) ≤ 8 * (x : ℝ) / Real.log (x : ℝ) := by
  have hx1 : (1 : ℝ) < (x : ℝ) := by exact_mod_cast (show 1 < x by omega)
  have hx0 : (0 : ℝ) ≤ (x : ℝ) := by positivity
  have hlogx_pos : 0 < Real.log (x : ℝ) := Real.log_pos hx1
  have hpi := Chebyshev.pi_le_log4_mul_div hx1
  rw [Nat.floor_natCast] at hpi
  have hlog_sqrt : Real.log √(x : ℝ) = Real.log (x : ℝ) / 2 := Real.log_sqrt hx0
  have hterm1 : Real.log 4 * (x : ℝ) / Real.log √(x : ℝ) ≤ 6 * (x : ℝ) / Real.log (x : ℝ) := by
    rw [hlog_sqrt]
    have hlog4 : Real.log (4 : ℝ) ≤ 3 := by
      linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)]
    have hrewrite : Real.log 4 * (x : ℝ) / (Real.log (x : ℝ) / 2) =
        (2 * Real.log 4) * (x : ℝ) / Real.log (x : ℝ) := by
      field_simp
    rw [hrewrite]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith) hx0) hlogx_pos.le
  have hterm2 : √(x : ℝ) ≤ 2 * (x : ℝ) / Real.log (x : ℝ) := by
    rw [le_div_iff₀ hlogx_pos]
    have hsqrt_pos : 0 < √(x : ℝ) := Real.sqrt_pos.mpr (by linarith)
    have hlog_le : Real.log √(x : ℝ) ≤ √(x : ℝ) := by
      linarith [Real.log_le_sub_one_of_pos hsqrt_pos]
    have hlogx_eq : Real.log (x : ℝ) = 2 * Real.log √(x : ℝ) := by linarith
    calc
      √(x : ℝ) * Real.log (x : ℝ) = 2 * (√(x : ℝ) * Real.log √(x : ℝ)) := by
        rw [hlogx_eq]; ring
      _ ≤ 2 * (√(x : ℝ) * √(x : ℝ)) := by
        gcongr
      _ = 2 * (x : ℝ) := by
        rw [Real.mul_self_sqrt hx0]
  have hsum : 6 * (x : ℝ) / Real.log (x : ℝ) + 2 * (x : ℝ) / Real.log (x : ℝ) =
      8 * (x : ℝ) / Real.log (x : ℝ) := by ring
  linarith

/-- `π(N) log N ≥ N log 2 / 2` for `N ≥ 100`. -/
lemma primeCounting_mul_log_ge {N : ℕ} (hN : 100 ≤ N) :
    (N : ℝ) * Real.log 2 / 2 ≤ (Nat.primeCounting N : ℝ) * Real.log N := by
  have h1 := Chebyshev.psi_ge N
  have h2 := Chebyshev.psi_le_primeCounting_mul_log N
  have hNR : (100 : ℝ) ≤ N := by exact_mod_cast hN
  have hpos : (0 : ℝ) < (N : ℝ) + 1 := by linarith
  have hsq : 10 ≤ Real.sqrt ((N : ℝ) + 1) := by
    rw [show (10 : ℝ) = Real.sqrt (10 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num; linarith)
  have hlog : Real.log ((N : ℝ) + 1) ≤ 2 * Real.sqrt ((N : ℝ) + 1) := by
    have h := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hpos)
    rw [Real.log_sqrt hpos.le] at h
    linarith [Real.sqrt_nonneg ((N : ℝ) + 1)]
  have hss := Real.mul_self_sqrt hpos.le
  have hl2 := Real.log_two_gt_d9
  have h3 : 2 * Real.sqrt ((N : ℝ) + 1) ≤ ((N : ℝ) + 1) / 5 := by
    rw [le_div_iff₀ (by norm_num)]
    nlinarith
  have h4 : Real.log ((N : ℝ) + 1) ≤ (N : ℝ) * Real.log 2 / 2 := by
    nlinarith
  have h5 : ((N : ℝ) + 1) = ((N + 1 : ℕ) : ℝ) := by push_cast; ring
  linarith

end OMA_FGKMT_H3

theorem OMA.solution : OMA.R_Erdos687_erdos_687_variants_fgkmt_R1.H3 := by
  intro A
  refine ⟨⌈8 * (max A 0 + 8)⌉₊ + 2, ?_⟩
  set C : ℕ := ⌈8 * (max A 0 + 8)⌉₊ + 2 with hC
  have hCR : 8 * (max A 0 + 8) ≤ (C : ℝ) := by
    have h := Nat.le_ceil (8 * (max A 0 + 8))
    rw [hC]
    push_cast
    linarith
  filter_upwards [Filter.eventually_ge_atTop (C + 100)] with x hx
  have hx2 : 2 ≤ x := by omega
  have hxC : C ≤ x := by omega
  have hxR : (100 : ℝ) ≤ x := by
    have : 100 ≤ x := by omega
    exact_mod_cast this
  have hC2 : 2 ≤ C := by omega
  have hCR2 : (2 : ℝ) ≤ C := by exact_mod_cast hC2
  set N := C * x with hN
  have hN100 : 100 ≤ N := by nlinarith
  have hNR : (N : ℝ) = (C : ℝ) * x := by rw [hN]; push_cast; ring
  have hlx : 0 < Real.log (x : ℝ) := Real.log_pos (by linarith)
  -- `π(N) ≤ π(x) + #(primes in (x, N])`
  have hsplit : Nat.primeCounting N ≤ Nat.primeCounting x +
      ((Finset.Ioc x N).filter Nat.Prime).card := by
    rw [← Nat.primesLE_card_eq_primeCounting, ← Nat.primesLE_card_eq_primeCounting]
    calc (Nat.primesLE N).card ≤ (Nat.primesLE x ∪ (Finset.Ioc x N).filter Nat.Prime).card := by
          apply Finset.card_le_card
          intro p hp
          have hp' := Nat.mem_primesLE.mp hp
          rw [Finset.mem_union, Finset.mem_filter, Finset.mem_Ioc]
          by_cases hpx : p ≤ x
          · exact Or.inl (Nat.mem_primesLE.mpr ⟨hpx, hp'.2⟩)
          · exact Or.inr ⟨⟨by omega, hp'.1⟩, hp'.2⟩
      _ ≤ _ := Finset.card_union_le _ _
  have hsplitR : (Nat.primeCounting N : ℝ) ≤ (Nat.primeCounting x : ℝ) +
      (((Finset.Ioc x N).filter Nat.Prime).card : ℝ) := by exact_mod_cast hsplit
  have hpix := OMA_FGKMT_H3.primeCounting_le_eight_mul_div_log hx2
  have hpiN := OMA_FGKMT_H3.primeCounting_mul_log_ge hN100
  -- `log N ≤ 2 log x`
  have hlogN : Real.log (N : ℝ) ≤ 2 * Real.log (x : ℝ) := by
    have hNle : (N : ℝ) ≤ (x : ℝ) ^ 2 := by
      rw [hNR, sq]
      have : (C : ℝ) ≤ x := by exact_mod_cast hxC
      nlinarith
    calc Real.log (N : ℝ) ≤ Real.log ((x : ℝ) ^ 2) :=
          Real.log_le_log (by rw [hNR]; positivity) hNle
      _ = 2 * Real.log (x : ℝ) := by rw [Real.log_pow]; norm_num
  have hlogNpos : 0 < Real.log (N : ℝ) := Real.log_pos (by
    have : (100 : ℝ) ≤ N := by exact_mod_cast hN100
    linarith)
  -- `π(N) ≥ C x log 2 / (4 log x)`
  have hl2 := Real.log_two_gt_d9
  have hpiN' : (C : ℝ) * x * Real.log 2 / (4 * Real.log x) ≤ (Nat.primeCounting N : ℝ) := by
    rw [div_le_iff₀ (by positivity)]
    have h1 : (Nat.primeCounting N : ℝ) * Real.log N ≤
        (Nat.primeCounting N : ℝ) * (2 * Real.log x) :=
      mul_le_mul_of_nonneg_left hlogN (Nat.cast_nonneg _)
    have hpiN2 : (C : ℝ) * x * Real.log 2 / 2 ≤ (Nat.primeCounting N : ℝ) * Real.log N := by
      rw [← hNR]; exact hpiN
    linarith
  -- conclude
  have hmain : A * x / Real.log x ≤
      (C : ℝ) * x * Real.log 2 / (4 * Real.log x) - 8 * x / Real.log x := by
    rw [div_sub_div _ _ (by positivity) hlx.ne', div_le_div_iff₀ hlx (by positivity)]
    have hx0 : (0 : ℝ) ≤ x := by linarith
    have hkey : A + 8 ≤ (C : ℝ) * Real.log 2 / 4 := by
      have : (C : ℝ) / 8 ≤ (C : ℝ) * Real.log 2 / 4 := by nlinarith
      have : A ≤ max A 0 := le_max_left _ _
      linarith
    have hl2x : 0 < Real.log x * Real.log x := by positivity
    have e : ((C : ℝ) * x * Real.log 2 * Real.log x - 4 * Real.log x * (8 * x)) * Real.log x =
        ((C : ℝ) * Real.log 2 / 4 - 8) * (4 * x * (Real.log x * Real.log x)) := by ring
    rw [e]
    have e2 : A * x * (4 * Real.log x * Real.log x) = A * (4 * x * (Real.log x * Real.log x)) := by
      ring
    rw [e2]
    apply mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  linarith
