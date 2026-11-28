import OMAReductions.R_oeis_a160326_R1

-- Step oeis-a160326.R1.H1: hypothesis H1 of reduction oeis-a160326.R1
-- Fermat's two-square theorem, characterization direction: every prime factor
-- 3 mod 4 occurs to an even power, so n is a sum of two squares.  This is
-- exactly mathlib's Nat.eq_sq_add_sq_iff read from right to left.

theorem OMA.solution : OMA.R_oeis_a160326_R1.H1 :=
  fun n h => Nat.eq_sq_add_sq_iff.2 h
