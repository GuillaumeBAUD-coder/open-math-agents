import OMAStatements.S_oeis_a362560
import Mathlib

namespace A362560Aux
open OMA.S_oeis_a362560

lemma ws_eq (y : List ℕ) :
    weightedSum y = ∑ i ∈ Finset.range y.length, (i + 1) * y.getD i 0 := by
  unfold weightedSum
  rw [Finset.sum_range]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [List.getD_eq_getElem y 0 i.isLt]
  rfl

lemma sum_eq (y : List ℕ) : ∑ i ∈ Finset.range y.length, y.getD i 0 = y.sum := by
  rw [Finset.sum_range, ← Fin.sum_univ_getElem y]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [List.getD_eq_getElem y 0 i.isLt]

lemma ws_rev (y : List ℕ) :
    weightedSum y.reverse = ∑ i ∈ Finset.range y.length, (y.length - i) * y.getD i 0 := by
  rw [ws_eq, List.length_reverse,
    ← Finset.sum_range_reflect (fun i => (y.length - i) * y.getD i 0) y.length]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have hi' : i < y.length := Finset.mem_range.mp hi
  rw [List.getD_reverse i hi']
  have : y.length - (y.length - 1 - i) = i + 1 := by omega
  rw [this]

lemma key (y : List ℕ) :
    weightedSum y + weightedSum y.reverse = (y.length + 1) * y.sum := by
  rw [ws_eq, ws_rev, ← Finset.sum_add_distrib, ← sum_eq y, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have hi' : i < y.length := Finset.mem_range.mp hi
  have : (i + 1) + (y.length - i) = y.length + 1 := by omega
  rw [← add_mul, this]
end A362560Aux

open OMA.S_oeis_a362560 in
theorem OMA.solution : type_of% @OMA.S_oeis_a362560.main := by
  intro n y hn hy
  have hsum : y.sum = n := hy.2.2
  have key := A362560Aux.key y
  rw [hsum] at key
  have h2 : n ∣ weightedSum y + weightedSum y.reverse := ⟨y.length + 1, by rw [key]; ring⟩
  constructor
  · intro h
    exact (Nat.dvd_add_iff_right h).mpr h2
  · intro h
    exact (Nat.dvd_add_iff_left h).mpr h2
