import Mathlib

/-!
# OEIS A309284: Smallest quadratic non-residue modulo Euler-like pseudoprimes

Source: https://oeis.org/A309284 (OEIS Foundation, CC BY-SA 4.0).
`a(n)` is the smallest odd composite `k` such that `prime(n)^((k - 1) / 2) ≡ -1 (mod k)` and
`b^((k - 1) / 2) ≡ 1 (mod k)` for every natural `1 ≤ b < prime(n)`.

Conjecture (OEIS A309284): for every `n ≥ 1`, the smallest quadratic non-residue modulo `a(n)`
is `prime(n)` (i.e., `A020649(a(n)) = prime(n)`). In fact, this holds for every odd composite `k`
satisfying the defining congruence conditions.
-/

namespace OMA.S_oeis_a309284

/-- Predicate expressing that `k` is an odd composite satisfying the congruence conditions of
OEIS A309284 for the `n`-th prime `p = Nat.nth Nat.Prime (n - 1)`. -/
def IsCandidate (n k : ℕ) : Prop :=
  let p := Nat.nth Nat.Prime (n - 1)
  1 < k ∧ Odd k ∧ ¬ k.Prime ∧
    (p : ZMod k) ^ ((k - 1) / 2) = -1 ∧
    ∀ b : ℕ, 1 ≤ b → b < p → (b : ZMod k) ^ ((k - 1) / 2) = 1

/-- Conjecture on OEIS A309284: for every `n ≥ 1` and every odd composite `k` satisfying the
defining conditions of A309284 (in particular `k = a(n)`), the smallest quadratic non-residue
modulo `k` is `prime(n)`. -/
theorem main : ∀ n k : ℕ, 1 ≤ n → IsCandidate n k →
    let p := Nat.nth Nat.Prime (n - 1)
    (∀ b : ℕ, b < p → IsSquare (b : ZMod k)) ∧ ¬ IsSquare (p : ZMod k) := by
  sorry

end OMA.S_oeis_a309284
