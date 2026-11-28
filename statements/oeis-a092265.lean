import Mathlib

/-!
# A092265: Sum of the smallest parts of distinct partitions

Source: https://oeis.org/A092265 (OEIS Foundation, CC BY-SA 4.0).

George Beck's identity compares this sum with A034296(n) + A237665(n).
A034296 counts the partitions whose distinct part values form a nonempty
interval of positive integers. A237665 counts those with at least two
distinct part values. The identity follows from Shane Chern's work
(https://arxiv.org/abs/1705.10700 and The Mathematics Student 88 (2019), 159–164).

The OEIS indexing starts at n = 1. The sum excludes the empty partition,
so both sides are also zero at n = 0 under these definitions.
-/

namespace OMA.S_oeis_a092265

/-- The least part, with value zero for the empty partition. -/
def smallestPart {n : ℕ} (p : Nat.Partition n) : ℕ :=
  if h : p.parts.toFinset.Nonempty then p.parts.toFinset.min' h else 0

/-- Gap-free partitions, including those with only one distinct part value. -/
def GapFree {n : ℕ} (p : Nat.Partition n) : Prop :=
  ∃ l r : ℕ, p.parts.toFinset = Finset.Icc l (l + r)

/-- Gap-free partitions with at least two distinct part values. -/
def ConsecutiveDistinctParts {n : ℕ} (p : Nat.Partition n) : Prop :=
  ∃ l r : ℕ, 1 ≤ r ∧ p.parts.toFinset = Finset.Icc l (l + r)

open Classical in
noncomputable def a034296 (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun p : Nat.Partition n => GapFree p)).card

open Classical in
noncomputable def a237665 (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun p : Nat.Partition n => ConsecutiveDistinctParts p)).card

/-- The sum of smallest parts in nonempty distinct partitions. -/
noncomputable def a (n : ℕ) : ℕ :=
  ∑ p ∈ (Finset.univ : Finset (Nat.Partition n)).filter
    (fun p => p.parts.Nodup ∧ p.parts ≠ 0), smallestPart p

theorem main : ∀ n : ℕ, a n = a034296 n + a237665 n := by
  sorry

end OMA.S_oeis_a092265
