import OMAStatements.S_oeis_a111108

-- Problem: A111108: a(n) = A001333(n) - (-2)^(n-1), n > 0.
-- Upstream: formal-conjectures statements/oeis-a111108.lean:0 (declaration OMA.S_oeis_a111108.main)
-- Credit: @yuka30240 (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open OMA.S_oeis_a111108

-- The power-trace approach was suggested by anmolspace in the desk notes.
theorem OMA.solution : type_of% @OMA.S_oeis_a111108.main := by
  intro p hp hodd
  have : Fact p.Prime := ⟨hp⟩
  let M : Matrix (Fin 2) (Fin 2) (ZMod p) := !![2, 1; 1, 0]
  have square : M ^ 2 = M + M + 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [M, sq, Matrix.mul_fin_two, Matrix.one_apply]
  have trace_pow (n : ℕ) : (M ^ n).trace = 2 * (A001333 n : ZMod p) := by
    induction n using Nat.twoStepInduction with
    | zero => simp [A001333]
    | one => simp [M, A001333, Matrix.trace_fin_two]
    | more n ih ih' =>
      rw [pow_add M n 2, square, mul_add, mul_add, mul_one, ← pow_succ]
      simp only [Matrix.trace_add, ih, ih', A001333, Int.cast_add, Int.cast_mul, Int.cast_ofNat]
      ring
  have two : (2 : ZMod p) ≠ 0 :=
    (ZMod.isUnit_prime_of_not_dvd Nat.prime_two (hp.odd_of_ne_two hodd).not_two_dvd_nat).ne_zero
  have h := trace_pow p
  rw [ZMod.trace_pow_card, ZMod.pow_card] at h
  have hA : (A001333 p : ZMod p) = 1 := by
    apply mul_left_cancel₀ two
    simpa [M, Matrix.trace_fin_two] using h.symm
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  simp [a, hA, ZMod.pow_card_sub_one_eq_one (neg_ne_zero.mpr two)]
