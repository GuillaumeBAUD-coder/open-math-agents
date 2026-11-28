import OMAStatements.S_oeis_a112041
import Mathlib

-- Problem: A112041: Numbers k such that 1*k + 1, 3*k + 1, 9*k + 1, 27*k + 1 are all primes.
-- Upstream: formal-conjectures statements/oeis-a112041.lean:0 (declaration OMA.S_oeis_a112041.main)
-- Credit: @rorcores (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
--
-- Proof.  Let k be a term.
-- (2 divides k)  If k is odd then k + 1 is an even prime, so k = 1, but then 3k + 1 = 4 is not
-- prime.
-- (5 divides k unless k = 4)  Modulo 5 the four numbers k + 1, 3k + 1, 9k + 1, 27k + 1 are
-- k + 1, 3k + 1, 4k + 1, 2k + 1.  If k = 1 (mod 5) then 5 divides 9k + 1; if k = 2 then 5 divides
-- 27k + 1; if k = 3 then 5 divides 3k + 1; if k = 4 then 5 divides k + 1.  A prime divisible by 5
-- equals 5, which is impossible for 9k + 1, 27k + 1 and 3k + 1 (given the residue of k) and forces
-- k = 4 for k + 1.

theorem OMA.solution : type_of% @OMA.S_oeis_a112041.main := by
  intro k h hk
  obtain ⟨h1, h3, h9, h27⟩ := h
  have key : ∀ q : ℕ, q.Prime → 5 ∣ q → q = 5 := fun q hq hd =>
    ((Nat.prime_dvd_prime_iff_eq Nat.prime_five hq).1 hd).symm
  have h2 : k % 2 = 0 := by
    by_contra hodd
    have hd : 2 ∣ 1 * k + 1 := by omega
    have he : 2 = 1 * k + 1 := (Nat.prime_dvd_prime_iff_eq Nat.prime_two h1).1 hd
    have hk1 : k = 1 := by omega
    rw [hk1] at h3
    exact absurd h3 (by norm_num)
  have h5 : k % 5 = 0 := by
    have hc : k % 5 = 0 ∨ k % 5 = 1 ∨ k % 5 = 2 ∨ k % 5 = 3 ∨ k % 5 = 4 := by omega
    rcases hc with h | h | h | h | h
    · exact h
    · have := key _ h9 (by omega)
      omega
    · have := key _ h27 (by omega)
      omega
    · have := key _ h3 (by omega)
      omega
    · have := key _ h1 (by omega)
      omega
  omega
