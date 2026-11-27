import OMAReductions.R_Erdos1109_erdos_1109_variants_konyagin_upper_R1
import Mathlib

-- Step Erdos1109.erdos_1109.variants.konyagin_upper.R1.H2: hypothesis H2 of reduction Erdos1109.erdos_1109.variants.konyagin_upper.R1
-- Credit: @ivillar

/-!
# A subpower-loss lower bound for the number of primes up to `N ^ (4 / 15)`

With `x = N ^ (4 / 15)`, Mathlib's Chebyshev bound `Chebyshev.pi_ge'` gives
`((x - 1) * log 2 - log (x + 2)) / log x ≤ π ⌊x⌋₊`. For `x ≥ 100` the numerator is at least `x / 4`,
and `4 * log x ≤ 4 * log N ≤ N ^ η` for large `N`, so `N ^ (4 / 15 - η) = x / N ^ η ≤ π ⌊x⌋₊`.
-/

namespace Erdos1109PrimeCountStep

open Filter Finset Real

lemma numerator_ge {x : ℝ} (hx : 100 ≤ x) : x / 4 ≤ (x - 1) * log 2 - log (x + 2) := by
  have hs0 : 0 < √(x + 2) := sqrt_pos.mpr (by linarith)
  have h1 := log_le_sub_one_of_pos hs0
  rw [log_sqrt (by linarith)] at h1
  have h2 : √(x + 2) ≤ x / 8 := by
    rw [sqrt_le_left (by linarith)]
    nlinarith
  have h3 : log (x + 2) ≤ x / 4 - 2 := by linarith
  have h4 : (0.69 : ℝ) < log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have h5 : (x - 1) * 0.69 ≤ (x - 1) * log 2 :=
    mul_le_mul_of_nonneg_left h4.le (by linarith)
  linarith

theorem prime_count : ∀ η : ℝ, 0 < η → ∀ᶠ N : ℕ in atTop,
    (N : ℝ)^((4 : ℝ)/15-η) ≤
      (((range (⌊(N : ℝ)^((4 : ℝ)/15)⌋₊+1)).filter Nat.Prime).card : ℝ) := by
  intro η hη
  have hlog : ∀ᶠ N : ℕ in atTop, 4 * log (N : ℝ) ≤ (N : ℝ) ^ η := by
    have h := ((isLittleO_log_rpow_atTop hη).bound (show (0 : ℝ) < 1 / 4 by norm_num)).natCast_atTop
    filter_upwards [h, eventually_ge_atTop 1] with N hN hN1
    have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
    rw [norm_of_nonneg (rpow_nonneg hN0.le η)] at hN
    have := le_norm_self (log (N : ℝ))
    linarith
  have hbig : ∀ᶠ N : ℕ in atTop, (100 : ℝ) ≤ (N : ℝ) ^ ((4 : ℝ) / 15) :=
    ((tendsto_rpow_atTop (show (0 : ℝ) < 4 / 15 by norm_num)).comp
      tendsto_natCast_atTop_atTop).eventually_ge_atTop 100
  filter_upwards [hlog, hbig, eventually_ge_atTop 1] with N h4 hx hN1
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
  have hN1' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hx1 : (1 : ℝ) < (N : ℝ) ^ ((4 : ℝ) / 15) := by linarith
  have hx0 : (0 : ℝ) < (N : ℝ) ^ ((4 : ℝ) / 15) := by linarith
  have hlx : 0 < log ((N : ℝ) ^ ((4 : ℝ) / 15)) := log_pos hx1
  have hlx' : log ((N : ℝ) ^ ((4 : ℝ) / 15)) ≤ log (N : ℝ) := by
    rw [log_rpow hN0]
    have := log_nonneg hN1'
    nlinarith
  have hNη : 0 < (N : ℝ) ^ η := rpow_pos_of_pos hN0 η
  have hcard : (((range (⌊(N : ℝ)^((4 : ℝ)/15)⌋₊+1)).filter Nat.Prime).card : ℝ) =
      (Nat.primeCounting ⌊(N : ℝ)^((4 : ℝ)/15)⌋₊ : ℝ) := by
    rw [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
  rw [hcard]
  calc (N : ℝ) ^ ((4 : ℝ) / 15 - η)
      = (N : ℝ) ^ ((4 : ℝ) / 15) / (N : ℝ) ^ η := rpow_sub hN0 _ _
    _ ≤ ((N : ℝ) ^ ((4 : ℝ) / 15) / 4) / log ((N : ℝ) ^ ((4 : ℝ) / 15)) := by
        rw [div_le_div_iff₀ hNη hlx]
        nlinarith
    _ ≤ (((N : ℝ) ^ ((4 : ℝ) / 15) - 1) * log 2 - log ((N : ℝ) ^ ((4 : ℝ) / 15) + 2)) /
          log ((N : ℝ) ^ ((4 : ℝ) / 15)) :=
        div_le_div_of_nonneg_right (numerator_ge hx) hlx.le
    _ ≤ (Nat.primeCounting ⌊(N : ℝ)^((4 : ℝ)/15)⌋₊ : ℝ) := Chebyshev.pi_ge' hx1

end Erdos1109PrimeCountStep

theorem OMA.solution : OMA.R_Erdos1109_erdos_1109_variants_konyagin_upper_R1.H2 :=
  Erdos1109PrimeCountStep.prime_count
