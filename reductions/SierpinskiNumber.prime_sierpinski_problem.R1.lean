import FormalConjectures.Wikipedia.SierpinskiNumber

-- Reduction SierpinskiNumber.prime_sierpinski_problem.R1 of The prime Sierpiński problem.
-- Credit: @tatashbar
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- main proves the known half outright: 271129 is prime (norm_num) and is a Sierpiński number
-- (the covering set {3, 5, 7, 13, 17, 241} with period 24; the lemma covered is copied from the
-- merged reduction SierpinskiNumber.extended_sierpinski_problem.R1 by @desenyon).
-- What remains is that no smaller prime k is Sierpiński, i.e. that k * 2^n + 1 is prime for
-- some n. This is split by how much is known about each k:
--   H1  every prime k < 271129 outside the eleven listed below. This is known: these k were
--       eliminated by explicit primes found by Seventeen or Bust and the PrimeGrid Prime
--       Sierpiński Problem (PSP). It is a finite statement, but a formal proof needs one
--       certified prime per k, and at least one witness is huge (10223 * 2^31172165 + 1,
--       found by PrimeGrid in 2016), so it is not a routine computation.
--   H2  the two k = 90527 and 168451. They were on the original PSP candidate list and are
--       reported eliminated by primes with millions of digits found by PrimeGrid (168451 is
--       PSP record prime 168451 * 2^19375200 + 1). They are kept apart so that H1 stays the
--       well-established part; if either report is wrong, H2 (not H1) carries the gap.
--   H3  the nine k = 22699, 67607, 79309, 79817, 152267, 156511, 222113, 225931, 237019, the
--       remaining candidates of the PSP as far as the author knows (22699 and 67607 are also
--       searched as Seventeen or Bust candidates). This is the genuinely open part: no prime
--       of the form k * 2^n + 1 is known for any of them.
-- Status pages: https://www.primegrid.com/stats_psp_llr.php and
-- https://en.wikipedia.org/wiki/Sierpi%C5%84ski_number.

namespace OMA.R_SierpinskiNumber_prime_sierpinski_problem_R1

set_option maxHeartbeats 1600000 in
private theorem covered : Nat.IsSierpinskiNumber 271129 := by
  refine ⟨by decide, fun n => ?_⟩
  have hpow := Nat.one_le_two_pow (n := n)
  have hn : 241 < 271129 * 2 ^ n + 1 := by omega
  have cover : ∀ r, r < 24 → ∃ p ∈ ([3, 5, 7, 13, 17, 241] : List ℕ),
      p ∣ 271129 * 2 ^ r + 1 := by decide +kernel
  obtain ⟨p, hp, hd⟩ := cover (n % 24) (Nat.mod_lt _ (by decide))
  have bounds : 1 < p ∧ p ≤ 241 := by fin_cases hp <;> decide
  have h24 : (2 : ℕ) ^ 24 ≡ 1 [MOD p] := by fin_cases hp <;> decide +kernel
  have he : (2 : ℕ) ^ n ≡ 2 ^ (n % 24) [MOD p] := by
    conv_lhs => rw [← Nat.div_add_mod n 24, pow_add, pow_mul]
    simpa using (h24.pow (n / 24)).mul_right (2 ^ (n % 24))
  have hdiv := (Nat.modEq_zero_iff_dvd).mp
    (((he.mul_left 271129).add_right 1).trans (Nat.modEq_zero_iff_dvd.mpr hd))
  refine ⟨by omega, fun hprime => ?_⟩
  rcases hprime.eq_one_or_self_of_dvd p hdiv with h | h <;> omega

/-- Every prime below 271129, other than the eleven candidates treated in H2 and H3, has a
prime of the form k * 2^n + 1 (known from Seventeen or Bust and PrimeGrid searches). -/
def H1 : Prop :=
  ∀ k : ℕ, k < 271129 → k.Prime →
    k ∉ ({22699, 67607, 79309, 79817, 90527, 152267, 156511, 168451, 222113, 225931,
      237019} : Finset ℕ) →
    ∃ n : ℕ, (k * 2 ^ n + 1).Prime

/-- The two former candidates 90527 and 168451, reported eliminated by PrimeGrid with
primes of millions of digits. -/
def H2 : Prop :=
  ∀ k ∈ ({90527, 168451} : Finset ℕ), ∃ n : ℕ, (k * 2 ^ n + 1).Prime

/-- The open part: each of the nine remaining candidates has a prime k * 2^n + 1. -/
def H3 : Prop :=
  ∀ k ∈ ({22699, 67607, 79309, 79817, 152267, 156511, 222113, 225931, 237019} : Finset ℕ),
    ∃ n : ℕ, (k * 2 ^ n + 1).Prime

theorem main : H1 → H2 → H3 → type_of% @SierpinskiNumber.prime_sierpinski_problem := by
  intro h1 h2 h3
  refine ⟨⟨covered, by norm_num⟩, ?_⟩
  rintro k ⟨hs, hp⟩
  by_contra hlt
  push_neg at hlt
  have hex : ∃ n : ℕ, (k * 2 ^ n + 1).Prime := by
    by_cases hC : k ∈ ({22699, 67607, 79309, 79817, 90527, 152267, 156511, 168451, 222113,
        225931, 237019} : Finset ℕ)
    · by_cases h2' : k ∈ ({90527, 168451} : Finset ℕ)
      · exact h2 k h2'
      · apply h3 k
        simp only [Finset.mem_insert, Finset.mem_singleton] at hC h2' ⊢
        omega
    · exact h1 k hlt hp hC
  obtain ⟨n, hn⟩ := hex
  exact (hs.2 n).2 hn

end OMA.R_SierpinskiNumber_prime_sierpinski_problem_R1
