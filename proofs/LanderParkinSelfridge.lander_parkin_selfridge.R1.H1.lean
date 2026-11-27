import OMAReductions.R_LanderParkinSelfridge_lander_parkin_selfridge_R1

-- The Lander, Parkin and Selfridge conjecture for exponents k <= 4.
-- If n + m < k <= 4 then (n, m) is (1, 1), (1, 2) or (2, 1). One term against one term gives a ^ k = b ^ k with
-- a different from b, impossible. One term against two happens only for k = 4 and is a ^ 4 = b ^ 4 + c ^ 4,
-- excluded by Fermat's theorem for exponent four (Mathlib's fermatLastTheoremFour).
-- These are the classical small cases, not progress on the conjecture, which is open from k = 5 on.

theorem OMA.solution : OMA.R_LanderParkinSelfridge_lander_parkin_selfridge_R1.H1 := by
  intro k n m x y hk hn hm hx hy hxy h
  by_contra hlt
  have h4 : FermatLastTheoremFor 4 := fermatLastTheoremFour
  have hn' : n = 1 ∨ n = 2 := by omega
  have hm' : m = 1 ∨ m = 2 := by omega
  rcases hn' with rfl | rfl <;> rcases hm' with rfl | rfl
  · simp only [Fin.sum_univ_one] at h
    have hk0 : k ≠ 0 := by omega
    exact hxy 0 0 (Nat.pow_left_injective hk0 h)
  · obtain rfl : k = 4 := by omega
    simp only [Fin.sum_univ_one, Fin.sum_univ_two] at h
    exact h4 (y 0) (y 1) (x 0) (hy 0).ne' (hy 1).ne' (hx 0).ne' h.symm
  · obtain rfl : k = 4 := by omega
    simp only [Fin.sum_univ_one, Fin.sum_univ_two] at h
    exact h4 (x 0) (x 1) (y 0) (hx 0).ne' (hx 1).ne' (hy 0).ne' h
  · omega
