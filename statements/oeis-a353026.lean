import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Order.Bounds.Basic

/-!
# OEIS A353026: least-exponent prime-factor greedy permutation

Source: https://oeis.org/A353026 (Scott R. Shannon, April 18, 2022).

The sequence starts 1, 2. Each subsequent term is the least unused positive
multiple of the smallest prime factor having minimum exponent in the
previous term. `Selected x p` states both parts of that selection: minimum
positive factorization exponent among prime divisors, then smallest prime
in a tie. Exponents of primes not dividing x are not candidates.

Indexing is shifted to zero. Every step excludes the entire previous
history. The target is existence and the conjectured positive-integer
permutation property. The separate empirical claim concerning the term
following a prime is not part of this statement.
-/

namespace OMA.S_oeis_a353026

def Selected (x p : ℕ) : Prop :=
  p.Prime ∧ p ∣ x ∧ ∀ q : ℕ, q.Prime → q ∣ x →
    x.factorization p ≤ x.factorization q ∧
      (x.factorization p = x.factorization q → p ≤ q)

def Greedy (a : ℕ → ℕ) : Prop :=
  a 0 = 1 ∧ a 1 = 2 ∧ ∀ n, ∃ p : ℕ,
    Selected (a (n+1)) p ∧
    IsLeast {m : ℕ | 0 < m ∧ p ∣ m ∧ ∀ i ≤ n+1, a i ≠ m} (a (n+2))

theorem main : (∃ a, Greedy a) ∧ ∀ a, Greedy a →
    Function.Injective a ∧ Set.range a = Set.Ioi 0 := by
  sorry

end OMA.S_oeis_a353026
