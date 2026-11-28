import Mathlib

/-!
# A225563: no totient-trajectory splits into an odd number of equal-sum parts

Source: https://oeis.org/A225563 (OEIS Foundation, CC BY-SA 4.0)
Credit: @trador01 (agent: Claude Code, model claude-opus-5-5)

A225563 (offset 1): numbers whose totient-trajectory can be partitioned into two sets with the
same sum; data 3, 5, 7, 9, 11, 13, 15, 17, 25, 27, ...
(17's totient-trajectory {17, 16, 8, 4, 2, 1} splits as 17 + 4 + 2 + 1 = 16 + 8.)

The entry records:

  The "totient-trajectory" of a number m is the sequence obtained by starting with m and
  repeatedly applying the map x -> phi(x) (cf. A000010) until reaching 1.
  Conjecture: No totient-trajectory can be partitioned into an odd number of sets with the
  same sum.

Reading of the source:
* For `m ≥ 1`, the totient-trajectory is the set `{m, φ(m), φ(φ(m)), ..., 1}`. Its terms are
  distinct (φ(x) < x for x > 1), and it is reached within `m` steps, so it is the image of
  `i ↦ φ^[i] m` for `i ≤ m` (later iterates stay at 1, already included).
* "partitioned into k sets with the same sum": each element is put in exactly one of `k` parts
  (a map to `Fin k`), and all parts have the same sum. Since all elements are positive, no part
  is then empty.
* "an odd number of sets" means an odd `k ≥ 3`: with `k = 1` every set is trivially such a
  partition, so the claim is about odd `k > 1`.
-/

namespace OMA.S_oeis_a225563

/-- The totient-trajectory of `m`: `{m, φ(m), φ(φ(m)), ..., 1}`. -/
def trajectory (m : ℕ) : Finset ℕ := (Finset.range (m + 1)).image fun i => Nat.totient^[i] m

/-- `T` can be partitioned into `k` parts with equal sums. -/
def EqualSplit (T : Finset ℕ) (k : ℕ) : Prop :=
  ∃ c : ℕ → Fin k, ∀ j j' : Fin k,
    ∑ x ∈ T.filter (fun x => c x = j), x = ∑ x ∈ T.filter (fun x => c x = j'), x

/-- No totient-trajectory splits into an odd number `k ≥ 3` of parts with equal sums. -/
theorem main : ∀ m : ℕ, 1 ≤ m → ∀ k : ℕ, Odd k → 3 ≤ k → ¬ EqualSplit (trajectory m) k := by
  sorry

end OMA.S_oeis_a225563
