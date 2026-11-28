import OMAStatements.S_oeis_a059163
import Mathlib

/-!
Credit: @ivillar
Proof: write h = A001511(floor(n/3) + 1) = v + 1. The three innermost phrases of the element of
W'3{2,2}* with this index are (2^v, 2^(v+1), 2^v), (2^(v+1), 2^(v+2), 2^(v+1)) and
(2^v, 2^(v+1), 2^v), with sums 2^(v+2), 2^(v+3) and 2^(v+2). The phrase of W2{2}* with the same
index is (v+1, v+2, v+1), so in each of the three cases n mod 3 = 0, 1, 2 the term a(n) equals
2^(1 + A059129(n)).
-/

open OMA.S_oeis_a059163 in
theorem OMA.solution : type_of% @OMA.S_oeis_a059163.main := by
  intro n
  have hr : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  have ht : ∀ t : ℕ, padicValNat 2 (n / 3 + 1) + 1 + t - 1 = padicValNat 2 (n / 3 + 1) + t := by
    intro t
    omega
  unfold a A059129
  rcases hr with h | h | h <;>
    simp only [h, element', element, phrase, ruler, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, List.getD_cons_zero, List.getD_cons_succ, Nat.add_sub_cancel, ht] <;>
    ring
