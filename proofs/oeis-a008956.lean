import OMAStatements.S_oeis_a008956
import Mathlib

/-!
# OEIS A008956: row sums of the central-factorial triangle

Let `R(n) = ∑_{k ≤ n} T(n, k)` where `T(n+1, k+1) = (2n+1)² T(n, k) + T(n, k+1)`,
`T(n, 0) = 1` and `T(n, k) = 0` for `k > n`. Summing the recurrence over `k`,

  `R(n+1) = 1 + (2n+1)² R(n) + (R(n) - 1) = ((2n+1)² + 1) R(n)`,

so `R(n) = ∏_{j < n} ((2j+1)² + 1)` by induction.
-/

open Finset OMA.S_oeis_a008956

namespace OMA.A008956

lemma entry_zero (n : ℕ) : entry n 0 = 1 := by
  cases n <;> simp [entry]

/-- Entries above the diagonal vanish. -/
lemma entry_eq_zero : ∀ n k : ℕ, n < k → entry n k = 0 := by
  intro n
  induction n with
  | zero =>
    intro k hk
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    simp [entry]
  | succ n ih =>
    intro k hk
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [entry, ih k' (by omega), ih (k' + 1) (by omega), Nat.mul_zero]

lemma absOdd_succ (n : ℕ) :
    absOddCoefficient (n + 1) = absOddCoefficient n * ((2 * n + 1) ^ 2 + 1) :=
  Finset.prod_range_succ _ _

end OMA.A008956

open OMA.A008956 in
theorem OMA.solution : type_of% @OMA.S_oeis_a008956.main := by
  intro n
  induction n with
  | zero => simp [entry, absOddCoefficient]
  | succ n ih =>
    -- shifting the index in row `n`
    have hshift : ∑ k ∈ range (n + 1), entry n (k + 1) + 1 = ∑ k ∈ range (n + 1), entry n k := by
      rw [Finset.sum_range_succ, entry_eq_zero n (n + 1) (by omega), add_zero,
        Finset.sum_range_succ' (fun k => entry n k) n, entry_zero]
    -- the recurrence summed over `k`
    have hstep : ∑ k ∈ range (n + 1), entry (n + 1) (k + 1)
        = (2 * n + 1) ^ 2 * ∑ k ∈ range (n + 1), entry n k
          + ∑ k ∈ range (n + 1), entry n (k + 1) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [entry]
    rw [Finset.sum_range_succ' _ (n + 1), entry_zero, hstep, absOdd_succ, ← ih, add_assoc, hshift]
    ring
