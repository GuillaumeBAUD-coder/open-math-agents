import OMAReductions.R_LanderParkinSelfridge_lander_parkin_selfridge_R1
import Mathlib

-- Step LanderParkinSelfridge.lander_parkin_selfridge.R1.H1: hypothesis H1 of reduction LanderParkinSelfridge.lander_parkin_selfridge.R1
-- Credit: @ivillar

/-!
Lander, Parkin and Selfridge for exponents up to four: a counterexample would need
`n + m < k ≤ 4`, i.e. `a ^ k = b ^ k` with `a ≠ b`, or `a ^ 4 = b ^ 4 + c ^ 4`, which is excluded
by Fermat's theorem for exponent four (Mathlib's `fermatLastTheoremFour`).
-/
namespace F2LPS

theorem small : ∀ (k n m : ℕ) (x : Fin n → ℕ) (y : Fin m → ℕ), k ≤ 4 →
    0 < n → 0 < m → (∀ i, 0 < x i) → (∀ j, 0 < y j) → (∀ i j, x i ≠ y j) →
    ∑ i, x i ^ k = ∑ j, y j ^ k → k ≤ n + m := by
  intro k n m x y hk hn hm hx hy hxy h
  by_contra hcon
  have hlt : n + m < k := not_le.mp hcon
  rcases (by omega : (n = 1 ∧ m = 1) ∨ (n = 1 ∧ m = 2 ∧ k = 4) ∨ (n = 2 ∧ m = 1 ∧ k = 4)) with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · rw [Fin.sum_univ_one, Fin.sum_univ_one] at h
    exact hxy 0 0 (Nat.pow_left_injective (by omega : k ≠ 0) h)
  · rw [Fin.sum_univ_one, Fin.sum_univ_two] at h
    exact fermatLastTheoremFour (y 0) (y 1) (x 0) (hy 0).ne' (hy 1).ne' (hx 0).ne' h.symm
  · rw [Fin.sum_univ_two, Fin.sum_univ_one] at h
    exact fermatLastTheoremFour (x 0) (x 1) (y 0) (hx 0).ne' (hx 1).ne' (hy 0).ne' h

end F2LPS

theorem OMA.solution : OMA.R_LanderParkinSelfridge_lander_parkin_selfridge_R1.H1 :=
  F2LPS.small
