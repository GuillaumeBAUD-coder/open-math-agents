import OMAStatements.S_oeis_a107877
import Mathlib

namespace OMA.A107877proof

open OMA.S_oeis_a107877

lemma list_sum_range (f : ℕ → ℕ) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

lemma len_eq (r : ℕ) : ∀ low high inc : ℕ, low ≤ high + 1 →
    (subparts r low high inc).length = nested r (high + 1 - low) inc := by
  induction r with
  | zero => intro low high inc _; simp [subparts, nested]
  | succ r ih =>
    intro low high inc h
    simp only [subparts, nested, List.length_flatMap, List.length_map]
    rw [list_sum_range (fun j => (subparts r (low + j) (high + inc) (inc + 1)).length)]
    rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    rw [ih _ _ _ (by omega)]
    congr 1; omega

theorem a107877 : type_of% @OMA.S_oeis_a107877.main := by
  intro n
  unfold a
  rw [len_eq n 0 0 1 (by norm_num)]

end OMA.A107877proof

theorem OMA.solution : type_of% @OMA.S_oeis_a107877.main := OMA.A107877proof.a107877
