import Mathlib

/-!
# A303712: a(n) is the smallest number such that there are exactly n numbers k (including a(n) itself) such that U(k) is isomorphic to U(a(n)) (or 0 if no such number exists). Here U(k) is the multiplicative group of integers modulo k.

Source: https://oeis.org/A303712
Credit: @jagraj28

Conjecture (Jianing Song, stated in A303712): `a(n) > 0` for all `n ≥ 1`, that is, for every
`n ≥ 1` some positive integer `m` has exactly `n` positive integers `k` with `U(k) ≅ U(m)`.

Formalization notes:
* `U(k)` is `(ZMod k)ˣ`, and "isomorphic" is a group isomorphism `(ZMod k)ˣ ≃* (ZMod m)ˣ`.
* The numbers `k` and `m` are positive (`ZMod 0 = ℤ` is excluded).
* `Set.ncard` counts the `k`; it is `0` for an infinite set, so `ncard = n` with `n ≥ 1` also says
  the set is finite (it always is, since `U(k)` has order `φ(k)`).
* A direct computation of the structure of `U(k)` gives the listed values `a(1), …, a(11)`.
-/

namespace OMA.S_oeis_a303712

/-- The positive integers `k` with `U(k) ≅ U(m)`. -/
def isoClass (m : ℕ) : Set ℕ := {k | 0 < k ∧ Nonempty ((ZMod k)ˣ ≃* (ZMod m)ˣ)}

/-- The conjecture of A303712: every `n ≥ 1` is the size of some class `isoClass m`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → ∃ m : ℕ, 0 < m ∧ (isoClass m).ncard = n := by
  sorry

end OMA.S_oeis_a303712
