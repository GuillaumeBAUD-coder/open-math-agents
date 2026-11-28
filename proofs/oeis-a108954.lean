import OMAStatements.S_oeis_a108954
import Mathlib

/-!
# A108954: `π(2n) - π(n)` counts the `i ∈ {1, …, n}` with `i + n` prime

`π(2j) - π(j)` is the number of primes in `(j, 2j]`, i.e. the number of `k < j` with
`j + 1 + k` prime; the shift `k ↦ k + 1` identifies these with the `i ∈ {1, …, j}` such that
`i + j` is prime.  For `j = 0` both sides are `0`.
-/

namespace OMA.S_oeis_a108954

open Finset

/-- The count of primes in `(j, 2j]`. -/
lemma key (j : ℕ) : Nat.primeCounting (2 * j) - Nat.primeCounting j =
    ((Icc 1 j).filter (fun i => Nat.Prime (i + j))).card := by
  have e : 2 * j + 1 = (j + 1) + j := by ring
  rw [Nat.primeCounting, Nat.primeCounting, Nat.primeCounting', e, Nat.count_add,
    Nat.add_sub_cancel_left, Nat.count_eq_card_filter_range]
  refine Finset.card_bij (fun k _ => k + 1) ?_ ?_ ?_
  · intro k hk
    simp only [mem_filter, mem_range, mem_Icc] at hk ⊢
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    rw [show k + 1 + j = j + 1 + k by ring]
    exact hk.2
  · intro x _ y _ h
    omega
  · intro i hi
    simp only [mem_filter, mem_Icc] at hi
    refine ⟨i - 1, ?_, by omega⟩
    simp only [mem_filter, mem_range]
    refine ⟨by omega, ?_⟩
    rw [show j + 1 + (i - 1) = i + j by omega]
    exact hi.2

end OMA.S_oeis_a108954

open OMA.S_oeis_a108954 in
theorem OMA.solution : type_of% @OMA.S_oeis_a108954.main := by
  congr 1
  funext n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [if_neg hn.ne']
    exact key n
