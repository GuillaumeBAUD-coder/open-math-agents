import OMAStatements.S_oeis_a129995

-- Problem: A129995: a(n) = (n + 1)*(n^2 + 2)*(n^3 + 3)*(n^4 + 4)/4!.
-- Upstream: formal-conjectures statements/oeis-a129995.lean:0 (declaration OMA.S_oeis_a129995.main)
-- Credit: @oceancheol (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
--
-- This is a known and elementary fact (the OEIS entry itself says the integrality is known):
-- the product (n + 1)(n^2 + 2)(n^3 + 3)(n^4 + 4) only depends on n modulo 24 as far as
-- divisibility by 24 is concerned, and it vanishes modulo 24 for each of the 24 residues.

namespace OMA.A129995

lemma dvd24 (n : ℕ) : 24 ∣ (n + 1) * (n ^ 2 + 2) * (n ^ 3 + 3) * (n ^ 4 + 4) := by
  have h : n % 24 ≡ n [MOD 24] := Nat.mod_modEq n 24
  have key : (n % 24 + 1) * ((n % 24) ^ 2 + 2) * ((n % 24) ^ 3 + 3) * ((n % 24) ^ 4 + 4)
      ≡ (n + 1) * (n ^ 2 + 2) * (n ^ 3 + 3) * (n ^ 4 + 4) [MOD 24] :=
    (((h.add_right 1).mul ((h.pow 2).add_right 2)).mul ((h.pow 3).add_right 3)).mul
      ((h.pow 4).add_right 4)
  have hlt : n % 24 < 24 := Nat.mod_lt n (by norm_num)
  have h0 : (n % 24 + 1) * ((n % 24) ^ 2 + 2) * ((n % 24) ^ 3 + 3) * ((n % 24) ^ 4 + 4)
      ≡ 0 [MOD 24] := by
    generalize n % 24 = r at hlt
    interval_cases r <;> decide
  exact (Nat.modEq_zero_iff_dvd).mp (key.symm.trans h0)

end OMA.A129995

theorem OMA.solution : type_of% @OMA.S_oeis_a129995.main := by
  intro n
  obtain ⟨m, hm⟩ := OMA.A129995.dvd24 n
  refine ⟨(m : ℤ), ?_⟩
  unfold OMA.S_oeis_a129995.a OMA.S_oeis_a129995.numerator
  rw [hm]
  have h4 : (Nat.factorial 4 : ℚ) = 24 := by norm_num [Nat.factorial]
  rw [h4]
  push_cast
  ring
