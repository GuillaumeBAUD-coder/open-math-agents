import OMAReductions.R_OeisA67599_conjecture_R1

-- Step OeisA67599.conjecture.R1.H2: hypothesis H2 of reduction OeisA67599.conjecture.R1
-- Credit: @Miura-KR
-- H2 := ∀ q : ℕ, 7 < q → q.Prime →     OeisA67599.a (2401 * q) = 740 * 10 ^ (Nat.digits 10 q).length + 10 * q + 1

/-! Proof of step H2: the encoding of 7^4 * q. -/

namespace OMA.A67599H2

/-- The sorted prime factor list of 7^4 * q, for a prime q larger than 7. -/
theorem factors (q : ℕ) (hq : 7 < q) (hp : q.Prime) :
    (2401 * q).primeFactorsList = [7, 7, 7, 7, q] := by
  have h7 : Nat.Prime 7 := by norm_num
  have hperm : [7, 7, 7, 7, q].Perm (2401 * q).primeFactorsList := by
    apply Nat.primeFactorsList_unique
    · simp only [List.prod_cons, List.prod_nil, mul_one]; ring
    · intro p hp'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
      rcases hp' with h | h | h | h | h <;> subst h <;> assumption
  have hs : List.Pairwise (· ≤ ·) [7, 7, 7, 7, q] := by
    simp [List.pairwise_cons, le_of_lt hq]
  exact List.Perm.eq_of_sortedLE (Nat.primeFactorsList_sorted _) hs.sortedLE hperm.symm

end OMA.A67599H2

theorem OMA.solution : OMA.R_OeisA67599_conjecture_R1.H2 := by
  intro q hq hp
  have hne : q ≠ 7 := by omega
  have h2 : 2 ≤ 2401 * q := by omega
  unfold OeisA67599.a
  rw [if_neg (by omega), OMA.A67599H2.factors q hq hp]
  have hd : [7, 7, 7, 7, q].dedup = [7, q] := by
    rw [List.dedup_cons_of_mem (by simp), List.dedup_cons_of_mem (by simp),
      List.dedup_cons_of_mem (by simp), List.dedup_cons_of_notMem (by simp [hne.symm]),
      List.dedup_cons_of_notMem (by simp), List.dedup_nil]
  simp only [hd, List.flatMap_cons, List.flatMap_nil, List.count_cons, List.count_nil,
    hne, Ne.symm hne, beq_iff_eq, if_true, if_false, List.cons_append,
    List.nil_append, List.append_nil, List.foldl_cons, List.foldl_nil,
    OeisA67599.concatenateNats]
  norm_num
  ring
