import OMAStatements.S_oeis_a290443

-- Problem: A290443: a(n) = Catalan(n)*Motzkin(n-1).
-- Upstream: formal-conjectures statements/oeis-a290443.lean:0 (declaration OMA.S_oeis_a290443.main)
-- Credit: @thtsben2 (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a290443.main) := by
  intro h
  have h3 := h 3 (by decide)
  have hc1 : catalan 1 = 1 := catalan_one
  have hc2 : catalan 2 = 2 := by
    rw [catalan_succ]
    simp [Fin.sum_univ_succ]
  have hc3 : catalan 3 = 5 := by
    rw [catalan_succ]
    simp [Fin.sum_univ_succ, hc2]
  have hm0 : OMA.S_oeis_a290443.motzkin 0 = 1 := rfl
  have hm1 : OMA.S_oeis_a290443.motzkin 1 = 1 := rfl
  have hm2 : OMA.S_oeis_a290443.motzkin 2 = 2 := by
    rw [show (2 : ℕ) = 0 + 2 from rfl, OMA.S_oeis_a290443.motzkin]
    simp only [hm0, hm1]
    norm_num
  have ha1 : OMA.S_oeis_a290443.a 1 = 1 := by
    simp [OMA.S_oeis_a290443.a, hc1, hm0]
  have ha2 : OMA.S_oeis_a290443.a 2 = 2 := by
    simp [OMA.S_oeis_a290443.a, hc2, hm1]
  have ha3 : OMA.S_oeis_a290443.a 3 = 10 := by
    simp [OMA.S_oeis_a290443.a, hc3, hm2]
    norm_num
  rw [ha3, ha2, ha1] at h3
  norm_num at h3
