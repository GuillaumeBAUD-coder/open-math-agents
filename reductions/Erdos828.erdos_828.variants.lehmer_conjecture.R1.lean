import FormalConjectures.ErdosProblems.«828»

-- Reduction Erdos828.erdos_828.variants.lehmer_conjecture.R1 of Lehmer's totient conjecture
-- Credit: @marcusbuffett

/-!
# Lehmer's totient problem: the two classical first steps, and the open rest

Lehmer's conjecture says that for `n > 1`, `φ(n) ∣ n - 1` exactly when `n` is prime. For a prime
this is `φ(n) = n - 1`, proved inside `main`. For a composite `n` with `φ(n) ∣ n - 1`, Lehmer
(On Euler's totient function, Bull. Amer. Math. Soc. 38 (1932)) showed that `n` is squarefree and
has many prime factors (at least seven); the first two steps are stated here.

* `H1`: a number that is not squarefree does not have `φ(n) ∣ n - 1` (a prime `p` with
  `p^2 ∣ n` divides both `φ(n)` and `n`).
* `H2`: a composite number with at most two distinct prime factors does not have
  `φ(n) ∣ n - 1`. (Such an `n` is odd, the quotient `(n - 1) / φ(n)` is at least `2`, so
  `2 * ∏ (p - 1) < ∏ p` over the primes dividing `n`, which fails for two odd primes.)
* `H3`: no squarefree number with three or more prime factors has `φ(n) ∣ n - 1`. This is the
  open problem and stays open.
-/

namespace OMA.R_Erdos828_erdos_828_variants_lehmer_conjecture_R1

/-- A solution of `φ(n) ∣ n - 1` is squarefree. -/
def H1 : Prop :=
  ∀ n : ℕ, 1 < n → ¬ Squarefree n → ¬ n.totient ∣ n - 1

/-- No composite number with at most two distinct prime factors is a solution. -/
def H2 : Prop :=
  ∀ n : ℕ, 1 < n → ¬ n.Prime → n.primeFactors.card ≤ 2 → ¬ n.totient ∣ n - 1

/-- The open part: squarefree numbers with three or more prime factors. -/
def H3 : Prop :=
  ∀ n : ℕ, 1 < n → Squarefree n → 3 ≤ n.primeFactors.card → ¬ n.totient ∣ n - 1

theorem main : H1 → H2 → H3 → type_of% @Erdos828.erdos_828.variants.lehmer_conjecture := by
  intro h1 h2 h3 n hn
  constructor
  · intro hdvd
    rw [← Nat.prime_iff]
    by_contra hnp
    by_cases hsq : Squarefree n
    · by_cases hc : n.primeFactors.card ≤ 2
      · exact h2 n hn hnp hc hdvd
      · exact h3 n hn hsq (by omega) hdvd
    · exact h1 n hn hsq hdvd
  · intro hp
    rw [Nat.totient_prime (Nat.prime_iff.mpr hp)]

end OMA.R_Erdos828_erdos_828_variants_lehmer_conjecture_R1
