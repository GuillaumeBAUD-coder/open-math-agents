import FormalConjectures.Wikipedia.SierpinskiNumber

-- Reduction SierpinskiNumber.selfridge_conjecture.R1 of The Sierpiński problem (Selfridge's conjecture).
-- Credit: @tatashbar
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- main proves the known half outright: 78557 is a Sierpiński number is the upstream theorem
-- SierpinskiNumber.selfridge_78557 (Selfridge's covering set {3, 5, 7, 13, 19, 37, 73}).
-- What remains is that no odd k < 78557 is Sierpiński, i.e. that k * 2^n + 1 is prime for
-- some n (even k are excluded by the definition). This is split by how much is known:
--   H1  every odd k < 78557 except the six listed below. This is known: each such k has an
--       explicit prime k * 2^n + 1, found by Selfridge, Baillie, Cormack, Williams, Keller,
--       Jaeschke and others, and by Seventeen or Bust (2002 to 2007) for 11 of the 17 values
--       left in 2002. A finite statement, but a formal proof needs one certified prime per k,
--       and some of them have millions of digits (for example 19249 * 2^13018586 + 1).
--   H2  k = 10223, eliminated by PrimeGrid in 2016 with the prime 10223 * 2^31172165 + 1
--       (9.4 million digits). Kept apart because it is the most recent elimination and its
--       witness is far beyond any formal primality certificate available today.
--   H3  the five remaining candidates k = 21181, 22699, 24737, 55459, 67607 (the current
--       Seventeen or Bust list searched by PrimeGrid; no prime is known for any of them as far
--       as the author knows). This is the genuinely open part of the conjecture.
-- Status pages: https://www.primegrid.com/stats_sob_llr.php and
-- https://en.wikipedia.org/wiki/Seventeen_or_Bust.

namespace OMA.R_SierpinskiNumber_selfridge_conjecture_R1

/-- Every odd k below 78557, other than the six candidates treated in H2 and H3, has a prime
of the form k * 2^n + 1 (known from the literature and Seventeen or Bust). -/
def H1 : Prop :=
  ∀ k : ℕ, k < 78557 → ¬ 2 ∣ k →
    k ∉ ({10223, 21181, 22699, 24737, 55459, 67607} : Finset ℕ) →
    ∃ n : ℕ, (k * 2 ^ n + 1).Prime

/-- The candidate 10223, eliminated by PrimeGrid in 2016. -/
def H2 : Prop := ∃ n : ℕ, (10223 * 2 ^ n + 1).Prime

/-- The open part: each of the five remaining candidates has a prime k * 2^n + 1. -/
def H3 : Prop :=
  ∀ k ∈ ({21181, 22699, 24737, 55459, 67607} : Finset ℕ), ∃ n : ℕ, (k * 2 ^ n + 1).Prime

theorem main : H1 → H2 → H3 → type_of% @SierpinskiNumber.selfridge_conjecture := by
  intro h1 h2 h3
  refine ⟨SierpinskiNumber.selfridge_78557, ?_⟩
  intro k hs
  change Nat.IsSierpinskiNumber k at hs
  by_contra hlt
  have hlt' : k < 78557 := by omega
  have hex : ∃ n : ℕ, (k * 2 ^ n + 1).Prime := by
    by_cases hC : k ∈ ({10223, 21181, 22699, 24737, 55459, 67607} : Finset ℕ)
    · by_cases h10 : k = 10223
      · subst h10; exact h2
      · apply h3 k
        simp only [Finset.mem_insert, Finset.mem_singleton] at hC ⊢
        omega
    · exact h1 k hlt' hs.1 hC
  obtain ⟨n, hn⟩ := hex
  exact (hs.2 n).2 hn

end OMA.R_SierpinskiNumber_selfridge_conjecture_R1
