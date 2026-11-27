import FormalConjectures.ErdosProblems.«470»

-- Reduction Erdos470.erdos_470.parts.ii.R1 of Erdős Problem 470 — ii
-- Credit: @biondadave
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- Notation: for k : ℕ put X = 2^(k+2), p = X - a and q = X + b, two primes on either side of
-- the power of two X, and n = 2^k * p * q.
--
-- H1 (KNOWN, published): G. Melfi, On the conditional infiniteness of primitive weird numbers,
--    J. Number Theory 147 (2015), 508-514, Theorem 1, in a slightly sharpened form.  Melfi
--    assumes b + 3 < a < 2^((k-1)/2); his proof only needs b + 3 < a and a * (a + b) < X, the
--    condition used here.  The argument: the abundance of n is
--      sigma(n) - 2n = 2^(k+1) * (a - b - 3) + (a - 1) * (b + 1),
--    and a sum of distinct proper divisors of n below p * q has the form A0 + p * B + q * C with
--    A0 < 2^(k+1) (a sum of distinct powers of two); such sums with B + C = h all lie in
--    [h * p, h * q + 2^(k+1)), and the abundance falls strictly between the blocks
--    h = (a - b - 4) / 2 and h + 1, so n is abundant but not pseudoperfect.  The maximal proper
--    divisors n / 2, n / p, n / q are not abundant, hence no proper divisor is weird.
--    Checked numerically for every k <= 14 and b < 600 (459 instances, all primitive weird).
--    Examples: (k, a, b) = (6, 5, 1) gives 4128448 and (6, 15, 1) gives 3963968.
-- H2 (OPEN, the core of the problem): for infinitely many k there are such primes, i.e. a prime
--    q = X + b just above X and a prime p = X - a just below it, farther away (b + 3 < a), both
--    within about sqrt(X).  Melfi notes this follows from p_(n+1) - p_n < sqrt(p_n) / 10 for all
--    large n, so from the conjectures of Cramer or Gonek.  It is not known to follow from the
--    Riemann Hypothesis (gaps O(sqrt(p) * log p)) or from Baker-Harman-Pintz (gaps < p^0.525):
--    both miss by more than a constant factor, and only the special points X = 2^(k+2) count.

namespace OMA.R_Erdos470_erdos_470_parts_ii_R1

-- Melfi 2015, Theorem 1 (sharpened size condition): two primes 2^(k+2) - a and 2^(k+2) + b with
-- b + 3 < a and a * (a + b) < 2^(k+2) give the primitive weird number 2^k * p * q.
def H1 : Prop :=
  ∀ k a b : ℕ, b + 3 < a → a * (a + b) < 2 ^ (k + 2) → (2 ^ (k + 2) - a).Prime →
    (2 ^ (k + 2) + b).Prime →
    Erdos470.PrimitiveWeird (2 ^ k * (2 ^ (k + 2) - a) * (2 ^ (k + 2) + b))

-- For infinitely many k there are primes 2^(k+2) - a and 2^(k+2) + b as in H1.
def H2 : Prop :=
  ∀ N : ℕ, ∃ k a b : ℕ, N ≤ k ∧ b + 3 < a ∧ a * (a + b) < 2 ^ (k + 2) ∧
    (2 ^ (k + 2) - a).Prime ∧ (2 ^ (k + 2) + b).Prime

theorem main : H1 → H2 → type_of% @Erdos470.erdos_470.parts.ii := by
  intro h1 h2
  apply Set.infinite_of_not_bddAbove
  rintro ⟨B, hB⟩
  obtain ⟨k, a, b, hk, hab, hsize, hp, hq⟩ := h2 (B + 1)
  have hmem : 2 ^ k * (2 ^ (k + 2) - a) * (2 ^ (k + 2) + b) ≤ B :=
    hB (h1 k a b hab hsize hp hq)
  have hk2 : k < 2 ^ k := Nat.lt_two_pow_self
  have hp1 : 1 ≤ 2 ^ (k + 2) - a := hp.one_lt.le
  have hq1 : 1 ≤ 2 ^ (k + 2) + b := hq.one_lt.le
  have hle : 2 ^ k ≤ 2 ^ k * (2 ^ (k + 2) - a) * (2 ^ (k + 2) + b) := by
    calc 2 ^ k = 2 ^ k * 1 * 1 := by ring
      _ ≤ 2 ^ k * (2 ^ (k + 2) - a) * (2 ^ (k + 2) + b) := by gcongr
  omega

end OMA.R_Erdos470_erdos_470_parts_ii_R1
