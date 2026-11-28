import Mathlib

/-!
# A241476: every prime p has a primitive root 0 < g < p with g - 1 a square

Source: https://oeis.org/A241476
Credit: @Evyrrun (agent: claude-code, model claude-opus-5-5)

A241476 (offset 1): `a(n)` is the least positive primitive root `g < prime(n)` modulo
`prime(n)` with `g - 1` a square, or `0` if no such `g` exists (data 1, 2, 2, 5, 2, 2, 5, ...).
For example `a(4) = 5` since `2^2 + 1 = 5` is a primitive root modulo `prime(4) = 7`, while
`0^2 + 1 = 1` and `1^2 + 1 = 2` are not.

Conjecture (comment of A241476): according to the conjecture in A239957, `a(n)` should be
always positive. A239957, part (i) (Zhi-Wei Sun): every prime `p` has a primitive root
`0 < g < p` of the form `k^2 + 1`, where `k` is an integer.

So `a(n) > 0` for all `n >= 1` says: for every prime `p` there is a `k` with `k^2 + 1 < p`
and `k^2 + 1` a primitive root modulo `p`. Since `k^2 = (-k)^2`, it is enough to take
`k : ℕ`, and `0 < k^2 + 1` holds automatically. For `p = 2` the witness is `k = 0`, `g = 1`
(numerically, the statement holds for every prime below 200000).

Conventions (as in the merged statement of A239963):
- An integer `g` is a primitive root modulo the prime `p` when its residue class generates the
  multiplicative group of `ZMod p`, i.e. has multiplicative order `p - 1`. This is written as
  `orderOf (g : ZMod p) = p - 1`; a multiple of `p` has `orderOf` equal to `0` and so is never a
  primitive root.
-/

namespace OMA.S_oeis_a241476

/-- `g` is a primitive root modulo `p`: its class in `ZMod p` has multiplicative order `p - 1`. -/
def IsPrimitiveRootMod (g p : ℕ) : Prop := orderOf (g : ZMod p) = p - 1

/-- A241476(n) > 0 for every n: every prime has a primitive root `k^2 + 1` below it. -/
theorem main :
    ∀ p : ℕ, Nat.Prime p → ∃ k : ℕ, k ^ 2 + 1 < p ∧ IsPrimitiveRootMod (k ^ 2 + 1) p := by
  sorry

end OMA.S_oeis_a241476
