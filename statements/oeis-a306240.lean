import Mathlib.Data.Nat.Notation

/-!
# OEIS A306240

Zhi-Wei Sun's conjectures on sums of a ninth or sixth power, a cube, and two
products of consecutive nonnegative integers. Source: https://oeis.org/A306240
Credit: @hiattco
-/

namespace OMA.S_oeis_a306240

/-- Number of representations with the two products ordered by their indices.
Every solution has both y² ≤ n and w² ≤ n, so the square-root bounds are inclusive. -/
def representationCount (n : ℕ) : ℕ :=
  let indices := List.range (Nat.sqrt n + 1)
  let withXY (x y : ℕ) : ℕ :=
    (indices.map fun w =>
      (List.range (w + 1)).countP fun z =>
        x ^ 9 + y ^ 3 + z * (z + 1) + w * (w + 1) = n).sum
  ((List.range 3).map fun x => (indices.map (withXY x)).sum).sum

theorem main :
    (∀ n : ℕ, 0 < representationCount n) ∧
    (∀ n : ℕ, representationCount n = 1 → n ∈ [0, 11, 17, 18, 47, 108, 109, 234, 359]) ∧
    (∀ n : ℕ, ∃ x y z w : ℕ, x ≤ 2 ∧ n = x ^ 6 + y ^ 3 + z * (z + 1) + w * (w + 1)) := by
  sorry

end OMA.S_oeis_a306240
