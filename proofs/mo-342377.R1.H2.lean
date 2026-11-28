import OMAReductions.R_mo_342377_R1

/-!
# Proof of `mo-342377.R1.H2`

Proves that `(a - 1) * (a + 2) ≠ Nat.ascFactorial c 4` for all `a, c ≥ 2`.

Writing `m = c ^ 2 + 3 * c`, we have `Nat.ascFactorial c 4 = c * (c + 1) * (c + 2) * (c + 3) = m * (m + 2)`.
For `c ≥ 2`, `m ≥ 10`, and `(m - 1) * (m + 2) < m * (m + 2) < m * (m + 3)`, so `(a - 1) * (a + 2)`
(which is of the form `x * (x + 3)` with `x = a - 1`) strictly skips over `m * (m + 2)`.
-/

theorem OMA.solution : OMA.R_mo_342377_R1.H2 := by
  intro a c ha hc heq
  have h4 : Nat.ascFactorial c 4 = c * (c + 1) * (c + 2) * (c + 3) := by
    simp [show (4 : ℕ) = 0 + 1 + 1 + 1 + 1 by rfl, Nat.ascFactorial_succ, Nat.ascFactorial_zero]
    ring
  rw [h4] at heq
  set x : ℕ := a - 1
  have hxa : a + 2 = x + 3 := by omega
  rw [hxa] at heq
  set m : ℕ := c ^ 2 + 3 * c
  have hm_eq : c * (c + 1) * (c + 2) * (c + 3) = m * (m + 2) := by
    dsimp [m]; ring
  rw [hm_eq] at heq
  have hm_ge : 10 ≤ m := by dsimp [m]; nlinarith
  rcases lt_or_ge x m with hlt | hge
  · have hxle : x ≤ m - 1 := by omega
    have h1 : x * (x + 3) ≤ (m - 1) * (m + 2) := Nat.mul_le_mul hxle (by omega)
    have h2 : (m - 1) * (m + 2) + 2 = m * (m + 2) - m := by
      zify [show 1 ≤ m by omega, show m ≤ m * (m + 2) by nlinarith]
      ring
    nlinarith
  · have h1 : m * (m + 3) ≤ x * (x + 3) := Nat.mul_le_mul hge (by omega)
    nlinarith
