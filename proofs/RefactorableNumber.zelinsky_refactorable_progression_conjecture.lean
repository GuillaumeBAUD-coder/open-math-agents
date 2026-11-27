import FormalConjectures.Wikipedia.RefactorableNumber

-- Problem: Zelinsky's Conjecture (2002, Conjecture 32)
-- Upstream: formal-conjectures FormalConjectures/Wikipedia/RefactorableNumber.lean:76 (declaration RefactorableNumber.zelinsky_refactorable_progression_conjecture)
-- Credit: @senamakel (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

-- Proof: pick a prime p > n₀ with p ≡ 1 (mod m) and take n = n₀ * p ^ (p - 1).
-- Then τ(n) = τ(n₀) * p divides n₀ * p ^ (p - 1), and n ≡ n₀ * 1 (mod m).

namespace OMA.Zelinsky32

theorem card_divisors_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (p ^ k).divisors.card = k + 1 := by
  rw [Nat.divisors_prime_pow hp k, Finset.card_map, Finset.card_range]

end OMA.Zelinsky32

theorem OMA.solution : type_of% @RefactorableNumber.zelinsky_refactorable_progression_conjecture := by
  intro m n₀ hm ⟨hn₀, hdvd⟩
  obtain ⟨p, hp, hnp, hpm⟩ := Nat.exists_prime_gt_modEq_one n₀ (k := m) (by omega)
  have hp2 := hp.two_le
  have hcop : n₀.Coprime (p ^ (p - 1)) := by
    apply Nat.Coprime.pow_right
    rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
    intro h
    exact absurd (Nat.le_of_dvd (by omega) h) (by omega)
  have hpow_pos : 0 < p ^ (p - 1) := pow_pos (by omega) _
  refine ⟨n₀ * p ^ (p - 1), ?_, ⟨?_, ?_⟩, ?_⟩
  · have : 2 ≤ p ^ (p - 1) := by
      calc 2 ≤ p := hp2
        _ = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ (p - 1) := Nat.pow_le_pow_right (by omega) (by omega)
    nlinarith
  · exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  · rw [Nat.Coprime.card_divisors_mul hcop, OMA.Zelinsky32.card_divisors_prime_pow hp,
      Nat.sub_add_cancel (by omega : 1 ≤ p)]
    exact mul_dvd_mul hdvd (dvd_pow_self p (by omega))
  · have h1 : p ^ (p - 1) ≡ 1 ^ (p - 1) [MOD m] := Nat.ModEq.pow _ hpm
    rw [one_pow] at h1
    simpa using Nat.ModEq.mul_left n₀ h1
