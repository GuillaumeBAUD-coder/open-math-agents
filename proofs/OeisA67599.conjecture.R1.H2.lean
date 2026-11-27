import OMAReductions.R_OeisA67599_conjecture_R1
import Mathlib

-- Step OeisA67599.conjecture.R1.H2: hypothesis H2 of reduction OeisA67599.conjecture.R1
-- Credit: @ivillar
-- H2 := ∀ q : ℕ, 7 < q → q.Prime →     OeisA67599.a (2401 * q) = 740 * 10 ^ (Nat.digits 10 q).length + 10 * q + 1
--
-- Proof: the sorted prime factor list of 2401 * q = 7^4 * q is [7, 7, 7, 7, q], so the
-- deduplicated list is [7, q] with multiplicities 4 and 1, and the decimal concatenation
-- of 7, 4, q, 1 evaluates to 740 * 10^len(q) + 10 * q + 1.

theorem OMA.solution : OMA.R_OeisA67599_conjecture_R1.H2 := by
  unfold OMA.R_OeisA67599_conjecture_R1.H2
  intro q hq hqp
  have h7 : Nat.Prime 7 := by norm_num
  have hq7 : q ≠ 7 := by omega
  have hperm : List.Perm [7, 7, 7, 7, q] (2401 * q).primeFactorsList := by
    apply Nat.primeFactorsList_unique
    · simp only [List.prod_cons, List.prod_nil]
      ring
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl <;> assumption
  have hsorted : List.SortedLE [7, 7, 7, 7, q] := by
    apply List.Pairwise.sortedLE
    simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, List.Pairwise.nil]
    refine ⟨?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro a ha <;> first | omega | exact ha.elim
  have hfac : (2401 * q).primeFactorsList = [7, 7, 7, 7, q] :=
    (List.Perm.eq_of_sortedLE hsorted (Nat.primeFactorsList_sorted _) hperm).symm
  unfold OeisA67599.a
  rw [if_neg (by omega)]
  simp only [hfac]
  simp [List.dedup_cons_of_mem, List.dedup_cons_of_notMem, hq7, Ne.symm hq7,
    OeisA67599.concatenateNats, List.count_cons]
  ring
