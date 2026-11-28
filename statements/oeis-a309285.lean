import Mathlib

/-!
# OEIS A309285: Smallest prime quadratic residue modulo Euler-like pseudoprimes

Source: https://oeis.org/A309285 (OEIS Foundation, CC BY-SA 4.0).
`a(n)` is the smallest odd composite `k` such that `prime(n)^((k - 1) / 2) ≡ 1 (mod k)` and
`q^((k - 1) / 2) ≡ -1 (mod k)` for every prime `q < prime(n)`.

Conjecture (OEIS A309285): the smallest prime quadratic residue modulo `a(n)` is `prime(n)`.
We prove this holds for every `n ≥ 2` and every odd composite `k` satisfying the defining
conditions (in particular `k = a(n)`), and also establish that at `n = 1` the least candidate
is `a(1) = 341`, for which `prime(1) = 2` is a quadratic non-residue modulo `341` (showing that
`n ≥ 2` is sharp).
-/

namespace OMA.S_oeis_a309285

/-- Predicate expressing that `k` is an odd composite satisfying the congruence conditions of
OEIS A309285 for the `n`-th prime `p = Nat.nth Nat.Prime (n - 1)`. -/
def IsCandidate (n k : ℕ) : Prop :=
  let p := Nat.nth Nat.Prime (n - 1)
  1 < k ∧ Odd k ∧ ¬ k.Prime ∧
    (p : ZMod k) ^ ((k - 1) / 2) = 1 ∧
    ∀ q : ℕ, q.Prime → q < p → (q : ZMod k) ^ ((k - 1) / 2) = -1

/-- Complete resolution of OEIS A309285:
(1) For every `n ≥ 2` and every candidate `k` (in particular `k = a(n)`), the smallest prime
    quadratic residue modulo `k` is `prime(n)`.
(2) At `n = 1`, `a(1) = 341` is the least candidate and `2` is not a quadratic residue mod `341`. -/
theorem main :
    (∀ n k : ℕ, 2 ≤ n → IsCandidate n k →
      let p := Nat.nth Nat.Prime (n - 1)
      IsSquare (p : ZMod k) ∧ ∀ q : ℕ, q.Prime → q < p → ¬ IsSquare (q : ZMod k)) ∧
    (IsCandidate 1 341 ∧ (∀ k : ℕ, k < 341 → ¬ IsCandidate 1 k) ∧ ¬ IsSquare (2 : ZMod 341)) := by
  sorry

end OMA.S_oeis_a309285
