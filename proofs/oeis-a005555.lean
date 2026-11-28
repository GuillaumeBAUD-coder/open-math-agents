import OMAStatements.S_oeis_a005555

-- Problem: A005555: A finite sequence associated with the Lie algebra E_8.
-- Upstream: formal-conjectures statements/oeis-a005555.lean:0 (declaration OMA.S_oeis_a005555.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Idea: compare constant coefficients. On the left it is a(0) * (0 - 1)^4 = a(0) = 1, on the
-- right it is 5, so the two power series differ (Plouffe's g.f. is wrong, as the entry says).

open OMA.S_oeis_a005555 in
theorem OMA.solution : type_of% @OMA.S_oeis_a005555.main := by
  intro H
  have h := congrArg (fun p : PowerSeries ℚ => PowerSeries.constantCoeff p) H
  simp only [map_mul, map_pow, map_sub, map_add, map_one, map_ofNat,
    PowerSeries.constantCoeff_mk, PowerSeries.constantCoeff_X] at h
  have ha : a 0 = 1 := rfl
  rw [ha] at h
  norm_num at h
