import OMAStatements.S_mo_475837
import Mathlib

theorem OMA.solution : type_of% @OMA.S_mo_475837.main := by
  intro s hs hAP L hL
  obtain ⟨j, hj⟩ := exists_nat_gt (1 / (L - 1))
  have hL1 : 0 < L - 1 := by linarith
  have hj' : 1 < (L - 1) * j := by
    have := (div_lt_iff₀ hL1).mp hj
    linarith
  obtain ⟨a, d, hd, hmem⟩ := hAP (j + 2)
  obtain ⟨k1, hk1⟩ := hmem j (by omega)
  obtain ⟨k2, hk2⟩ := hmem (j + 1) (by omega)
  have hlt : k1 < k2 := by
    rw [← hs.lt_iff_lt, hk1, hk2]
    have : (j + 1) * d = j * d + d := by ring
    omega
  have hle : s (k1 + 1) ≤ s k2 := hs.monotone hlt
  refine ⟨k1, ?_⟩
  have h1 : (s (k1 + 1) : ℝ) ≤ (s k2 : ℝ) := by exact_mod_cast hle
  have h2 : (s k2 : ℝ) = a + (j + 1) * d := by rw [hk2]; push_cast; ring
  have h3 : (s k1 : ℝ) = a + j * d := by rw [hk1]; push_cast; ring
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have ha : (0 : ℝ) ≤ a := by positivity
  rw [h3]
  nlinarith [mul_nonneg hL1.le ha, mul_pos (by linarith : (0 : ℝ) < (L - 1) * j - 1) hd']
