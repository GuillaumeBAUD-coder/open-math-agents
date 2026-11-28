import OMAReductions.R_CunninghamChain_infinitely_many_firstKind_chains_R1

-- Step CunninghamChain.infinitely_many_firstKind_chains.R1.H1: hypothesis H1 of reduction CunninghamChain.infinitely_many_firstKind_chains.R1
-- Credit: @Moti1125

/-
By Dirichlet's theorem there are arbitrarily large primes `p ≡ 1 (mod 3)`. For such `p > 3`,
`3 ∣ 2p + 1` and `2p + 1 > 3`, so `2p + 1` is composite: `p` starts a first-kind chain of
exact length one.
-/
theorem OMA.solution : OMA.R_CunninghamChain_infinitely_many_firstKind_chains_R1.H1 := by
  apply Set.infinite_of_forall_exists_gt
  intro N
  obtain ⟨p, hpN, hp, hmod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq (max N 3) (q := 3) (a := 1) (by norm_num) (by norm_num)
  refine ⟨p, ⟨by norm_num, ?_, ?_⟩, by omega⟩
  · intro i hi
    obtain rfl : i = 0 := by omega
    simpa [CunninghamChain.firstKindTerm] using hp
  · simp only [CunninghamChain.firstKindTerm]
    intro hq
    have h3 : 3 ∣ 2 * p + 1 := by
      have : p % 3 = 1 := hmod
      omega
    rcases hq.eq_one_or_self_of_dvd 3 h3 with h | h <;> omega
