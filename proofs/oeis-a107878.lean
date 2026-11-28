import OMAStatements.S_oeis_a107878

/-! Credit: @unserus

By induction on the number of parts, the number of lists produced by subparts r low high inc is
nested r (high + 1 - low) inc: both unfold to a sum over the first choice, and the two sums
agree after reversing the summation index. -/

namespace OMAA107878Helpers
open OMA.S_oeis_a107878

theorem list_sum_range (d : ℕ) (g : ℕ → ℕ) :
    ((List.range d).map g).sum = ∑ j ∈ Finset.range d, g j := by
  induction d with
  | zero => simp
  | succ d ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

theorem len (r : ℕ) : ∀ low high inc : ℕ,
    (subparts r low high inc).length = nested r (high + 1 - low) inc := by
  induction r with
  | zero => intro low high inc; simp [subparts, nested]
  | succ r ih =>
    intro low high inc
    simp only [subparts, nested, List.length_flatMap, List.length_map]
    rw [list_sum_range]
    simp only [ih]
    rw [← Finset.sum_range_reflect]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    congr 1
    omega

end OMAA107878Helpers

open OMAA107878Helpers OMA.S_oeis_a107878 in
theorem OMA.solution : type_of% @OMA.S_oeis_a107878.main := by
  intro n
  rw [a, len]
