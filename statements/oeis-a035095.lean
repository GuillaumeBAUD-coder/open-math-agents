import Mathlib

/-!
# A035095: Smallest prime congruent to 1 mod prime(n)

Source: https://oeis.org/A035095
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Draft from an earlier generic agent run; audited against the source and re-checked before submission.

Title: A035095: Smallest prime congruent to 1 (mod prime(n)).

Statement:
Conjecture: a(n) is the smallest prime p such that gpf(p-1) = prime(n).
According to a long-standing conjecture (see the 1979 Wagstaff reference),
a(n) <= prime(n)^2 + 1.

Conventions:
- `Nat.nth Nat.Prime n` is the `n`-th prime (0-indexed: `2, 3, 5, ...`).
- We state both the greatest-prime-factor characterization and Wagstaff's upper bound.
-/

namespace OMA.S_oeis_a035095

/-- Smallest prime congruent to 1 modulo the `n`-th prime (`A035095`). -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {p : ℕ | Nat.Prime p ∧ p % Nat.nth Nat.Prime n = 1}

/-- `q` is the greatest prime factor of `m`. -/
def IsGreatestPrimeFactor (q m : ℕ) : Prop :=
  Nat.Prime q ∧ q ∣ m ∧ ∀ r : ℕ, Nat.Prime r → r ∣ m → r ≤ q

/-- Smallest prime `p` whose predecessor `p - 1` has greatest prime factor `q`. -/
noncomputable def smallestPrimeWithGpf (q : ℕ) : ℕ :=
  sInf {p : ℕ | Nat.Prime p ∧ IsGreatestPrimeFactor q (p - 1)}

theorem main :
    (∀ n : ℕ, a n = smallestPrimeWithGpf (Nat.nth Nat.Prime n)) ∧
    (∀ n : ℕ, a n ≤ (Nat.nth Nat.Prime n) ^ 2 + 1) := by
  sorry

end OMA.S_oeis_a035095
