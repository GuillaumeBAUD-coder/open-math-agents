import OMAStatements.S_oeis_a130729

-- Problem: A130729: Fermat numbers of order 3 or F(n,3) = 2^(2^n) + 3.
-- Upstream: formal-conjectures statements/oeis-a130729.lean:0 (declaration OMA.S_oeis_a130729.main)
-- Credit: @justusklocke-cloud (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

-- For odd n we have 2^n = 3q + 2, so 2^(2^n) = 8^q * 4, which is 4 modulo 7, and 4 + 3 = 7.

theorem OMA.solution : type_of% @OMA.S_oeis_a130729.main := by
  intro n hn
  obtain ⟨m, rfl⟩ := hn
  have h : ∃ q, 2 ^ (2 * m + 1) = 3 * q + 2 := by
    induction m with
    | zero => exact ⟨0, by norm_num⟩
    | succ m ih =>
      obtain ⟨q, hq⟩ := ih
      refine ⟨4 * q + 2, ?_⟩
      rw [show 2 * (m + 1) + 1 = (2 * m + 1) + 2 by ring, pow_add, hq]
      ring
  obtain ⟨q, hq⟩ := h
  unfold OMA.S_oeis_a130729.a
  rw [hq, pow_add, pow_mul]
  have h8 : (2 ^ 3) ^ q % 7 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  omega
