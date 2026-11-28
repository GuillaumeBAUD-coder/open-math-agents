import OMAStatements.S_oeis_a008407

-- Problem: A008407: Minimal difference s(n) between beginning and end of n consecutive large primes (n-tuplet) permitted by divisibility consideration
-- Upstream: formal-conjectures statements/oeis-a008407.lean:0 (declaration OMA.S_oeis_a008407.main)
-- Credit: @<your GitHub handle> (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open OMA.S_oeis_a008407

lemma OMA.width_bound_a008407 : a 5 ≤ 4 := by
  apply Nat.sInf_le
  refine ⟨Finset.range 5, ?_, ?_, ?_, ?_⟩
  · simp
  · simp
  · intro s hs
    have := Finset.mem_range.mp hs
    omega
  · intro p hp
    refine ⟨p, ?_⟩
    intro s hs
    exact ne_of_lt (Nat.mod_lt s hp.pos)

lemma OMA.harmonic_bound_a008407 : 1 < H 5 := by
  norm_num [H, show Finset.Icc 1 5 = {1, 2, 3, 4, 5} by decide]

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a008407.main) := by
  intro h
  have hpos := (h.2 5 (by norm_num)).1
  have hb : (a 5 : ℝ) ≤ 4 := by exact_mod_cast OMA.width_bound_a008407
  have hh := OMA.harmonic_bound_a008407
  norm_num at hpos
  linarith
