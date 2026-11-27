import FormalConjectures.ErdosProblems.«470»

-- Reduction Erdos470.erdos_470.parts.ii.R2 of Erdős Problem 470 — ii
-- Credit: @OrangeHeadz
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- A second route, independent of R1. R1 (Melfi 2015, Theorem 1) takes both primes next to 2 ^ (k + 2),
-- one on each side. Here p is ANY prime above N = 2 ^ (k + 1) and q is much larger, about N ^ 2 / (p - N).
-- Notation: n = 2 ^ k * p * q, A = (N - 1) * (p + 1) * (q + 1) = sigma(n), B = N * p * q = 2 * n,
-- so A - B = sigma(n) - 2 * n is the abundance of n.
--
-- H1 (provable; a criterion in the style of Kravitz and Melfi): n is abundant since A > B. A subset
-- of the proper divisors of n sums to n exactly when its complement sums to A - B. As A - B < q the
-- complement only uses divisors of 2 ^ k * p, whose subset sums are a + b * p with a < N < p, so
-- their residues mod p are below N; hence n is not pseudoperfect. Every proper divisor of n divides
-- n / 2, n / p or n / q, none of which is abundant because p, q > N.
-- First instances: (k, p, q) = (1, 5, 7), (2, 11, 19), (3, 29, 31), giving 70, 836, 7192.
-- Checked against brute force for every instance with k <= 5 (20 instances, all primitive weird).
--
-- H2 (OPEN): such triples exist for arbitrarily large k. It mentions neither weird numbers nor
-- divisor sums. A prime p a little above N always exists, so the difficulty sits in q: a prime in
-- the interval where 0 < A - B < q whose abundance has a large residue mod p. For fixed k only
-- finitely many triples qualify, so unbounded k is the same as infinitely many triples.

namespace OMA.R_Erdos470_erdos_470_parts_ii_R2

def H1 : Prop :=
  ∀ k p q : ℕ, p.Prime → q.Prime → 2 ^ (k + 1) < p → 2 ^ (k + 1) < q → p ≠ q →
    2 ^ (k + 1) * p * q < (2 ^ (k + 1) - 1) * (p + 1) * (q + 1) →
    (2 ^ (k + 1) - 1) * (p + 1) * (q + 1) < 2 ^ (k + 1) * p * q + q →
    2 ^ (k + 1) ≤ ((2 ^ (k + 1) - 1) * (p + 1) * (q + 1) - 2 ^ (k + 1) * p * q) % p →
    Erdos470.PrimitiveWeird (2 ^ k * p * q)

def H2 : Prop :=
  ∀ K : ℕ, ∃ k p q : ℕ, K ≤ k ∧ p.Prime ∧ q.Prime ∧
    2 ^ (k + 1) < p ∧ 2 ^ (k + 1) < q ∧ p ≠ q ∧
    2 ^ (k + 1) * p * q < (2 ^ (k + 1) - 1) * (p + 1) * (q + 1) ∧
    (2 ^ (k + 1) - 1) * (p + 1) * (q + 1) < 2 ^ (k + 1) * p * q + q ∧
    2 ^ (k + 1) ≤ ((2 ^ (k + 1) - 1) * (p + 1) * (q + 1) - 2 ^ (k + 1) * p * q) % p

theorem main : H1 → H2 → type_of% @Erdos470.erdos_470.parts.ii := by
  intro h1 h2
  apply Set.infinite_of_not_bddAbove
  rintro ⟨B, hB⟩
  obtain ⟨k, p, q, hk, hp, hq, hNp, hNq, hpq, hpos, hlt, hmod⟩ := h2 B
  have hw : Erdos470.PrimitiveWeird (2 ^ k * p * q) := h1 k p q hp hq hNp hNq hpq hpos hlt hmod
  have hle : 2 ^ k * p * q ≤ B := hB hw
  have h1k : k < 2 ^ k := Nat.lt_two_pow_self
  have h2k : 2 ^ k ≤ 2 ^ k * p := Nat.le_mul_of_pos_right _ hp.pos
  have h3k : 2 ^ k * p ≤ 2 ^ k * p * q := Nat.le_mul_of_pos_right _ hq.pos
  omega

end OMA.R_Erdos470_erdos_470_parts_ii_R2
