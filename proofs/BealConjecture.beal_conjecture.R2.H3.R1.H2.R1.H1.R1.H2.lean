import OMAReductions.R_BealConjecture_beal_conjecture_R2_H3_R1_H2_R1_H1_R1

-- Step BealConjecture.beal_conjecture.R2.H3.R1.H2.R1.H1.R1.H2: hypothesis H2 of reduction BealConjecture.beal_conjecture.R2.H3.R1.H2.R1.H1.R1
-- Credit: @stoyanov-x

theorem OMA.solution : OMA.R_BealConjecture_beal_conjecture_R2_H3_R1_H2_R1_H1_R1.H2 := by
  intro u v hv h
  have huv : v < u := by
    by_contra hvu
    have huveq : u ≤ v := by omega
    have hmono : u ^ 3 ≤ v ^ 3 := Nat.pow_le_pow_left huveq 3
    omega
  have hstep : (v + 1) ^ 3 ≤ u ^ 3 :=
    Nat.pow_le_pow_left (Nat.succ_le_iff.mpr huv) 3
  rw [h] at hstep
  have hvpos : 0 < v := Nat.pos_of_ne_zero hv
  have hcube : (v + 1) ^ 3 = v ^ 3 + 3 * v ^ 2 + 3 * v + 1 := by ring
  rw [hcube] at hstep
  have hgap : 0 < 3 * v ^ 2 + 3 * v := by positivity
  omega
