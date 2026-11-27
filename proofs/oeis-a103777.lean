import OMAStatements.S_oeis_a103777
import Mathlib

-- Problem: oeis-a103777, f(k) = 8k^2 + 4k + 1 is never prime at four consecutive arguments.
-- Credit: @justusklocke-cloud (the owner of the agent is credited as the solver)
--
-- f(j) is divisible by 5 when j is 3 or 4 modulo 5, and then f(j) >= 85 > 5, so it is not
-- prime. Any four consecutive integers contain such a j.

theorem OMA.solution : type_of% @OMA.S_oeis_a103777.main := by
  intro k hk
  obtain ⟨h0, h1, h2, h3⟩ := hk
  have key : ∀ j : ℕ, (j % 5 = 3 ∨ j % 5 = 4) → ¬ Nat.Prime (OMA.S_oeis_a103777.f j) := by
    intro j hj hp
    have hdiv : 5 ∣ OMA.S_oeis_a103777.f j := by
      unfold OMA.S_oeis_a103777.f
      rcases hj with h | h
      · obtain ⟨q, hq⟩ : ∃ q, j = 5 * q + 3 := ⟨j / 5, by omega⟩
        rw [hq]; exact ⟨40 * q ^ 2 + 52 * q + 17, by ring⟩
      · obtain ⟨q, hq⟩ : ∃ q, j = 5 * q + 4 := ⟨j / 5, by omega⟩
        rw [hq]; exact ⟨40 * q ^ 2 + 68 * q + 29, by ring⟩
    have h5 : 5 = OMA.S_oeis_a103777.f j :=
      (Nat.prime_dvd_prime_iff_eq Nat.prime_five hp).mp hdiv
    unfold OMA.S_oeis_a103777.f at h5
    have hj3 : 3 ≤ j := by omega
    nlinarith
  rcases (by omega : (k % 5 = 3 ∨ k % 5 = 4) ∨ ((k + 1) % 5 = 3 ∨ (k + 1) % 5 = 4) ∨
      ((k + 2) % 5 = 3 ∨ (k + 2) % 5 = 4) ∨ ((k + 3) % 5 = 3 ∨ (k + 3) % 5 = 4))
    with h | h | h | h
  · exact key _ h h0
  · exact key _ h h1
  · exact key _ h h2
  · exact key _ h h3
