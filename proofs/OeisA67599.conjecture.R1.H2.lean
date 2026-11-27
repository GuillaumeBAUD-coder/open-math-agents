import OMAReductions.R_OeisA67599_conjecture_R1

-- Step OeisA67599.conjecture.R1.H2: hypothesis H2 of reduction OeisA67599.conjecture.R1
-- Credit: @carterleffen
-- Reduction OeisA67599.conjecture.R1 by @ArtemCherbaev; sequence A067599 (OEIS).
-- H2 := ∀ q : ℕ, 7 < q → q.Prime →     OeisA67599.a (2401 * q) = 740 * 10 ^ (Nat.digits 10 q).length + 10 * q + 1
-- Proof: 2401 * q = 7^4 * q, so its sorted prime factor list is [7, 7, 7, 7, q]; the encoding
-- concatenates 7, 4, q, 1.

namespace OMA.S_OeisA67599_conjecture_R1_H2

theorem primeFactorsList_eq {q : ℕ} (hq : 7 < q) (hp : q.Prime) :
    Nat.primeFactorsList (2401 * q) = [7, 7, 7, 7, q] := by
  have hperm : List.Perm [7, 7, 7, 7, q] (Nat.primeFactorsList (2401 * q)) := by
    apply Nat.primeFactorsList_unique
    · simp only [List.prod_cons, List.prod_nil]
      ring
    · intro p hmem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl | rfl | rfl | rfl
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · exact hp
  refine (List.Perm.eq_of_sortedLE ?_ (Nat.primeFactorsList_sorted _) hperm).symm
  rw [List.sortedLE_iff_pairwise]
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
    List.Pairwise.nil, and_true]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro b (rfl | rfl | rfl | rfl) <;> omega
  · rintro b (rfl | rfl | rfl) <;> omega
  · rintro b (rfl | rfl) <;> omega
  · exact ⟨fun b hb => by omega, fun b hb => hb.elim⟩

theorem dedup_eq {q : ℕ} (hq : 7 < q) : List.dedup [7, 7, 7, 7, q] = [7, q] := by
  rw [List.dedup_cons_of_mem (by simp), List.dedup_cons_of_mem (by simp),
    List.dedup_cons_of_mem (by simp), List.dedup_cons_of_notMem (by simp; omega),
    List.dedup_cons_of_notMem (by simp), List.dedup_nil]

end OMA.S_OeisA67599_conjecture_R1_H2

open OMA.S_OeisA67599_conjecture_R1_H2 in
theorem OMA.solution : OMA.R_OeisA67599_conjecture_R1.H2 := by
  intro q hq hp
  have hfl := primeFactorsList_eq hq hp
  have hd := dedup_eq hq
  have hne : q ≠ 7 := by omega
  have c7 : List.count 7 [7, 7, 7, 7, q] = 4 := by
    simp [Ne.symm hne]
  have cq : List.count q [7, 7, 7, 7, q] = 1 := by
    simp [List.count_cons, Ne.symm hne]
  unfold OeisA67599.a
  rw [if_neg (by omega)]
  simp only [hfl, hd, c7, cq, List.flatMap_cons, List.flatMap_nil, List.cons_append,
    List.nil_append, List.append_nil, List.foldl_cons, List.foldl_nil,
    OeisA67599.concatenateNats]
  have d7 : Nat.digits 10 7 = [7] := by norm_num
  have d4 : Nat.digits 10 4 = [4] := by norm_num
  have d1 : Nat.digits 10 1 = [1] := by norm_num
  rw [d7, d4, d1]
  simp only [List.length_cons, List.length_nil]
  ring
