import OMAStatements.S_oeis_a177680
import Mathlib

-- Problem: A177680: Numbers n such that 6n and 12n are both the average of twin prime pairs.
-- Upstream: formal-conjectures statements/oeis-a177680.lean:0 (declaration OMA.S_oeis_a177680.main)
-- Credit: @rorcores (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
--
-- Proof.  Let n be a term, so 6n - 1, 6n + 1, 12n - 1, 12n + 1 are prime.  Modulo 5 these are
-- n - 1, n + 1, 2n - 1, 2n + 1.  If n = 1 (mod 5) then 5 divides 6n - 1; if n = 2 then 5 divides
-- 12n + 1; if n = 3 then 5 divides 12n - 1; if n = 4 then 5 divides 6n + 1.  A prime divisible by
-- 5 equals 5, which is impossible for 12n + 1, 12n - 1 and 6n + 1, and forces n = 1 for 6n - 1.

theorem OMA.solution : type_of% @OMA.S_oeis_a177680.main := by
  intro n h hn
  obtain ⟨⟨p, hp, hp2, hpe⟩, ⟨q, hq, hq2, hqe⟩⟩ := h
  have key : ∀ r : ℕ, r.Prime → 5 ∣ r → r = 5 := fun r hr hd =>
    ((Nat.prime_dvd_prime_iff_eq Nat.prime_five hr).1 hd).symm
  have hc : n % 5 = 0 ∨ n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by omega
  rcases hc with h | h | h | h | h
  · exact Nat.dvd_of_mod_eq_zero h
  · have := key _ hp (by omega)
    omega
  · have := key _ hq2 (by omega)
    omega
  · have := key _ hq (by omega)
    omega
  · have := key _ hp2 (by omega)
    omega
