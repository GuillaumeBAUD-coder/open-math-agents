import OMAStatements.S_mo_475837
import Mathlib

-- Problem: mo-475837, a strictly increasing sequence of naturals whose range contains
-- arbitrarily long arithmetic progressions has consecutive ratios below any L > 1.
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- Pick j with (L - 1) j > 1 and a progression a, a + d, ..., a + (j + 1) d in the range.
-- If s k = a + j d, then s (k + 1) <= a + (j + 1) d, because the latter is a later term of s,
-- and a + (j + 1) d < L (a + j d).

theorem OMA.solution : type_of% @OMA.S_mo_475837.main := by
  intro s hs hap L hL
  have hL1 : 0 < L - 1 := by linarith
  obtain ⟨j, hj⟩ := exists_nat_gt (1 / (L - 1))
  have hj' : 1 < (j : ℝ) * (L - 1) := (div_lt_iff₀ hL1).mp hj
  obtain ⟨a, d, hd, hmem⟩ := hap (j + 2)
  obtain ⟨k, hk⟩ := hmem j (by omega)
  obtain ⟨k', hk'⟩ := hmem (j + 1) (by omega)
  have hlt : s k < s k' := by
    rw [hk, hk', Nat.add_mul, one_mul]
    omega
  have hkk : k < k' := hs.lt_iff_lt.mp hlt
  have hle : s (k + 1) ≤ s k' := hs.monotone hkk
  refine ⟨k, ?_⟩
  have h1 : (s (k + 1) : ℝ) ≤ (a : ℝ) + ((j : ℝ) + 1) * d := by
    have h : (s (k + 1) : ℝ) ≤ (s k' : ℝ) := by exact_mod_cast hle
    rw [hk'] at h
    push_cast at h
    linarith
  have h2 : (s k : ℝ) = (a : ℝ) + (j : ℝ) * d := by
    rw [hk]
    push_cast
    ring
  rw [h2]
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  nlinarith [mul_pos hd' (sub_pos.mpr hj'), mul_nonneg hL1.le ha]
