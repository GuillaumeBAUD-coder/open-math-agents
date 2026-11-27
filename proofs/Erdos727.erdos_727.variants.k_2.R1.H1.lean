import OMAReductions.R_Erdos727_erdos_727_variants_k_2_R1
import Mathlib

-- Step Erdos727.erdos_727.variants.k_2.R1.H1: hypothesis H1 of reduction Erdos727.erdos_727.variants.k_2.R1
-- Credit: @ivillar
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-! `(2n)! = C(2n, n) * (n!)^2` and `(n+2)! = (n+1)(n+2) * n!`, so both sides of the divisibility
carry the common factor `(n!)^2`, which cancels. -/

open Finset Nat in
theorem OMA.solution : OMA.R_Erdos727_erdos_727_variants_k_2_R1.H1 := by
  intro n
  have h1 : (2 * n).factorial = (2 * n).choose n * n.factorial ^ 2 := by
    have := Nat.choose_mul_factorial_mul_factorial (show n ≤ 2 * n by omega)
    rw [show 2 * n - n = n by omega] at this
    rw [← this]; ring
  have h2 : (n + 2).factorial ^ 2 = ((n + 1) * (n + 2)) ^ 2 * n.factorial ^ 2 := by
    rw [show n + 2 = n + 1 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]; ring
  rw [h1, h2]
  exact Nat.mul_dvd_mul_iff_right (by positivity)

