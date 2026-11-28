import OMAStatements.S_oeis_a077625

-- Problem: A077625: Largest term in periodic part of continued fraction expansion of square root of -1+2^n or 0 if -1+2^n is square.
-- Upstream: formal-conjectures statements/oeis-a077625.lean:0 (declaration OMA.S_oeis_a077625.main)
-- Credit: @wonsukchoi (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

-- For n ≥ 2, 2^n - 1 ≡ 3 (mod 4), while every square is 0 or 1 (mod 4).
theorem OMA.solution : type_of% @OMA.S_oeis_a077625.main := by
  intro n hn
  constructor
  · rintro ⟨r, hr⟩
    by_contra h
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    have e : 2 ^ (k + 2) = 4 * 2 ^ k := by ring
    have hpos : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    have h3 : r * r % 4 = 3 := by omega
    have hm : r * r % 4 = (r % 4) * (r % 4) % 4 := Nat.mul_mod _ _ _
    have hlt : r % 4 < 4 := Nat.mod_lt _ (by norm_num)
    generalize r * r = s at h3 hm
    generalize r % 4 = t at hm hlt
    interval_cases t <;> omega
  · rintro rfl
    exact ⟨1, by norm_num⟩
