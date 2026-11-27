import FormalConjectures.Wikipedia.RefactorableNumber

-- Problem: Zelinsky's Conjecture (2002, Conjecture 32)
-- Upstream: formal-conjectures FormalConjectures/Wikipedia/RefactorableNumber.lean:76 (declaration RefactorableNumber.zelinsky_refactorable_progression_conjecture)
-- Credit: @sho-404 (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

-- Proof idea: pick a prime p > n0 with p = 1 mod m and take n = n0 * p^(p-1).
-- Then d(n) = d(n0) * p, which divides n0 * p^(p-1), and n = n0 mod m.
theorem OMA.solution : type_of% @RefactorableNumber.zelinsky_refactorable_progression_conjecture := by
  intro m n₀ hm hn₀
  obtain ⟨hpos, hdvd⟩ := hn₀
  obtain ⟨p, hp, hlt, hmod⟩ := Nat.exists_prime_gt_modEq_one n₀ (Nat.one_le_iff_ne_zero.mp hm)
  have hcop : Nat.Coprime n₀ (p ^ (p - 1)) :=
    ((hp.coprime_iff_not_dvd.mpr fun hd => hlt.not_ge (Nat.le_of_dvd hpos hd)).symm).pow_right _
  have hcard : (p ^ (p - 1)).divisors.card = p := by
    rw [Nat.divisors_prime_pow hp, Finset.card_map, Finset.card_range]
    have := hp.two_le
    omega
  have hp0 : 0 < p ^ (p - 1) := pow_pos hp.pos _
  have hd : p ∣ p ^ (p - 1) := dvd_pow_self p (by have := hp.two_le; omega)
  refine ⟨n₀ * p ^ (p - 1), ?_, ⟨Nat.mul_pos hpos hp0, ?_⟩, ?_⟩
  · nlinarith [Nat.le_of_dvd hp0 hd]
  · rw [hcop.card_divisors_mul, hcard]
    exact Nat.mul_dvd_mul hdvd hd
  · simpa using Nat.ModEq.mul_left n₀ (hmod.pow (p - 1))
