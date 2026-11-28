import OMAReductions.R_oeis_a160326_R1

/-- Euler's sum of two squares theorem: the `3 mod 4` primes occur to even exponent
in `n` exactly when `n` is a sum of two squares. -/
theorem OMA.solution : OMA.R_oeis_a160326_R1.H1 :=
  fun n h => Nat.eq_sq_add_sq_iff.mpr h
