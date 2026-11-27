import OMAReductions.R_Erdos1204_erdos_1204_variants_B_upper_R1
import Mathlib.NumberTheory.Chebyshev

open Filter

theorem OMA.solution : OMA.R_Erdos1204_erdos_1204_variants_B_upper_R1.H2 := by
  intro δ hδ
  have hπ := Chebyshev.eventually_primeCounting_le (zero_lt_one : (0 : ℝ) < 1)
  rw [eventually_atTop] at hπ
  obtain ⟨C, hC⟩ := hπ
  let K : ℕ := max (max ⌈C⌉₊ 2) ⌈Real.exp ((Real.log 4 + 1) / δ)⌉₊
  refine eventually_atTop.mpr ⟨K, ?_⟩
  intro k hk
  have hKceil : ⌈C⌉₊ ≤ K :=
    le_trans (le_max_left ⌈C⌉₊ 2) (le_max_left _ _)
  have hKexp : ⌈Real.exp ((Real.log 4 + 1) / δ)⌉₊ ≤ K := le_max_right _ _
  have hK2 : 2 ≤ K := le_trans (le_max_right ⌈C⌉₊ 2) (le_max_left _ _)
  have hkCnat : ⌈C⌉₊ ≤ k := le_trans hKceil hk
  have hkexp : ⌈Real.exp ((Real.log 4 + 1) / δ)⌉₊ ≤ k := le_trans hKexp hk
  have hk2 : 2 ≤ k := le_trans hK2 hk
  have hkC : C ≤ (k : ℝ) := (Nat.le_ceil C).trans (by exact_mod_cast hkCnat)
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hk1 : (1 : ℝ) < (k : ℝ) := by exact_mod_cast (show 1 < k by omega)
  have hlogpos : 0 < Real.log (k : ℝ) := Real.log_pos hk1
  have hke : Real.exp ((Real.log 4 + 1) / δ) ≤ (k : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hkexp)
  have hlogle : (Real.log 4 + 1) / δ ≤ Real.log (k : ℝ) :=
    (Real.le_log_iff_exp_le hk0).mpr hke
  have hcoef : (Real.log 4 + 1) ≤ Real.log (k : ℝ) * δ := (div_le_iff₀ hδ).mp hlogle
  have hcheb := hC (k : ℝ) hkC
  simp only [Nat.floor_natCast] at hcheb
  have hratio : (Real.log 4 + 1) * (k : ℝ) / Real.log (k : ℝ) ≤ δ * (k : ℝ) := by
    rw [div_le_iff₀ hlogpos]
    nlinarith
  exact hcheb.trans hratio
