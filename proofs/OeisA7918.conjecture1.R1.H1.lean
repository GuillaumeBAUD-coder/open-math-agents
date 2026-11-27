import OMAReductions.R_OeisA7918_conjecture1_R1
import Mathlib

/-! The first term `p₀` of an `n`-term progression of primes with difference `d > 0` is a prime
with `n ≤ p₀`: otherwise the term with index `k = p₀ < n` is `p₀ (1 + d)`, which is not prime.
So `p₀` lies in the set whose infimum is `a n`. -/

open OeisA7918 in
theorem OMA.solution : OMA.R_OeisA7918_conjecture1_R1.H1 := by
  intro n p0 d hn hap
  obtain ⟨hd, hp⟩ := hap
  have hp0 : p0.Prime := by simpa using hp 0 hn
  have hge : n ≤ p0 := by
    rcases Nat.lt_or_ge p0 n with hlt | hge
    swap
    · exact hge
    exfalso
    have h := hp p0 hlt
    rw [show p0 + p0 * d = p0 * (1 + d) by ring] at h
    rcases Nat.prime_mul_iff.mp h with ⟨_, h1⟩ | ⟨_, h1⟩
    · omega
    · exact hp0.one_lt.ne' h1
  exact Nat.sInf_le ⟨hp0, hge⟩
