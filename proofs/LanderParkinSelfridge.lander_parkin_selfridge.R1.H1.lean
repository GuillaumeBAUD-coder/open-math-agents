import OMAReductions.R_LanderParkinSelfridge_lander_parkin_selfridge_R1

/-!
# Proof of `LanderParkinSelfridge.lander_parkin_selfridge.R1.H1`

The Lander–Parkin–Selfridge conjecture for exponents `k ≤ 4`:
- For `k ≤ 2`, `0 < n` and `0 < m` already give `k ≤ 2 ≤ n + m`.
- For `k = 3`, the only case with `n + m < 3` is `n = m = 1`, which gives `x 0 ^ 3 = y 0 ^ 3`,
  hence `x 0 = y 0`, contradicting `x 0 ≠ y 0`.
- For `k = 4`, the cases with `n + m < 4` are `(n, m) ∈ {(1, 1), (2, 1), (1, 2)}`; the first
  gives `x 0 = y 0`, and the latter two contradict Fermat's Last Theorem for exponent `4`
  (`fermatLastTheoremFour`).
-/

theorem OMA.solution : OMA.R_LanderParkinSelfridge_lander_parkin_selfridge_R1.H1 := by
  intro k n m x y hk4 hn hm hx hy hxy hsum
  by_contra hlt
  have hcases : (k = 3 ∧ n = 1 ∧ m = 1) ∨
      (k = 4 ∧ n = 1 ∧ m = 1) ∨
      (k = 4 ∧ n = 2 ∧ m = 1) ∨
      (k = 4 ∧ n = 1 ∧ m = 2) := by omega
  rcases hcases with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · simp only [Fin.sum_univ_one] at hsum
    exact hxy 0 0 (Nat.pow_left_injective (by norm_num : 3 ≠ 0) hsum)
  · simp only [Fin.sum_univ_one] at hsum
    exact hxy 0 0 (Nat.pow_left_injective (by norm_num : 4 ≠ 0) hsum)
  · simp only [Fin.sum_univ_two, Fin.sum_univ_one] at hsum
    exact fermatLastTheoremFour (x 0) (x 1) (y 0)
      (Nat.ne_of_gt (hx 0)) (Nat.ne_of_gt (hx 1)) (Nat.ne_of_gt (hy 0)) hsum
  · simp only [Fin.sum_univ_one, Fin.sum_univ_two] at hsum
    exact fermatLastTheoremFour (y 0) (y 1) (x 0)
      (Nat.ne_of_gt (hy 0)) (Nat.ne_of_gt (hy 1)) (Nat.ne_of_gt (hx 0)) hsum.symm
