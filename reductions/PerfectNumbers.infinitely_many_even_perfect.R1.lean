import FormalConjectures.Wikipedia.PerfectNumbers

-- Reduction PerfectNumbers.infinitely_many_even_perfect.R1 of Infinite even perfect numbers — infinitely many even perfect numbers
-- Credit: @ihateSAS
-- Each H becomes its own step once this file is accepted. Proving both closes the problem.
--
-- The Euclid–Euler theorem says an even number is perfect exactly when it is
-- `2 ^ (p - 1) * (2 ^ p - 1)` for a Mersenne prime `2 ^ p - 1`.  That splits the question into
-- two independent halves, kept apart here:
--   * `H1` — infinitely many Mersenne primes: the whole difficulty, and the classical
--     reformulation of the problem;
--   * `H2` — Euclid's direction: every Mersenne prime does give an even perfect number.  This is
--     elementary (`σ` of a product of two coprime factors) and provable today.
-- `main` does not assume the covering statement: it produces the infinite set by mapping the
-- Mersenne exponents into the perfect numbers, and proves that map injective, since
-- `2 ^ (p - 1) * (2 ^ p - 1)` is strictly increasing in `p` on Mersenne exponents.

namespace OMA.R_PerfectNumbers_infinitely_many_even_perfect_R1

open Nat

/-- The open core: infinitely many primes `p` with `2 ^ p - 1` prime (Mersenne primes). -/
def H1 : Prop := {p : ℕ | p.Prime ∧ (2 ^ p - 1).Prime}.Infinite

/-- Euclid's half of Euclid–Euler: each Mersenne prime yields an even perfect number. -/
def H2 : Prop := ∀ p : ℕ, p.Prime → (2 ^ p - 1).Prime →
    Nat.Perfect (2 ^ (p - 1) * (2 ^ p - 1)) ∧ Even (2 ^ (p - 1) * (2 ^ p - 1))

/-- `p ↦ 2 ^ (p - 1) * (2 ^ p - 1)` is strictly increasing on Mersenne exponents: both factors
grow with `p`, and the second factor stays positive. -/
lemma euclidMap_strictMonoOn :
    StrictMonoOn (fun p : ℕ => 2 ^ (p - 1) * (2 ^ p - 1))
      {p : ℕ | p.Prime ∧ (2 ^ p - 1).Prime} := by
  intro p hp q _ hpq
  have hp1 : 1 ≤ p := hp.1.one_le
  have hlt : 2 ^ p < 2 ^ q := Nat.pow_lt_pow_right (by norm_num) hpq
  have hbase : 0 < 2 ^ p - 1 := by
    have h2p : 2 ^ 1 ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) hp1
    omega
  have hstep : 2 ^ (p - 1) * (2 ^ p - 1) ≤ 2 ^ (q - 1) * (2 ^ p - 1) := by
    have hle : 2 ^ (p - 1) ≤ 2 ^ (q - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact Nat.mul_le_mul_right _ hle
  have hstep2 : 2 ^ (q - 1) * (2 ^ p - 1) < 2 ^ (q - 1) * (2 ^ q - 1) := by
    have hpq2 : 2 ^ p - 1 < 2 ^ q - 1 := by omega
    exact Nat.mul_lt_mul_of_pos_left hpq2 (by positivity)
  exact lt_of_le_of_lt hstep hstep2

theorem main : H1 → H2 → type_of% @PerfectNumbers.infinitely_many_even_perfect := by
  intro h1 h2
  refine Set.infinite_of_injOn_mapsTo euclidMap_strictMonoOn.injOn ?_ h1
  intro p hp
  exact h2 p hp.1 hp.2

end OMA.R_PerfectNumbers_infinitely_many_even_perfect_R1
