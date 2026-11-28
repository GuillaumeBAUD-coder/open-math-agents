import Mathlib

/-!
# A379633: Irregular triangle read by rows in which row n lists the largest parts of the partitions
of n into consecutive parts (with the partitions ordered by increasing number of parts).

Source: https://oeis.org/A379633
Credit: @esracummings31-blip

Conjecture (OEIS A379633): the right border gives A212652.

Conventions.
* A partition of n into j consecutive parts is a, a+1, ..., a+j-1 with a >= 1 and j >= 1; its
  largest part is a+j-1. For fixed j there is at most one such partition, and a, j <= n.
  Row n lists the largest parts ordered by increasing j.
* The right border of the triangle is the last entry of each row.
* A212652(n) is the least positive integer M such that n = T(M) - T(k) for an integer k with
  0 <= k <= M, where T(r) = r(r+1)/2 (A000217).
-/

namespace OMA.S_oeis_a379633

/-- Row n of A379633. -/
def row (n : ℕ) : List ℕ :=
  (List.range (n + 1)).flatMap (fun j => (List.range (n + 1)).filterMap (fun a =>
    if 1 ≤ j ∧ 1 ≤ a ∧ ∑ i ∈ Finset.range j, (a + i) = n then some (a + j - 1) else none))

/-- Triangular numbers A000217. -/
def T (r : ℕ) : ℕ := r * (r + 1) / 2

/-- A212652. -/
noncomputable def A212652 (n : ℕ) : ℕ :=
  sInf {M : ℕ | 1 ≤ M ∧ ∃ k, k ≤ M ∧ n = T M - T k}

theorem main : ∀ n : ℕ, 1 ≤ n → (row n).getLast? = some (A212652 n) := by
  sorry

end OMA.S_oeis_a379633
