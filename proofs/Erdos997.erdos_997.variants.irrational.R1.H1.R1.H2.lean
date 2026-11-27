import OMAReductions.R_Erdos997_erdos_997_variants_irrational_R1_H1_R1

-- Step Erdos997.erdos_997.variants.irrational.R1.H1.R1.H2:
-- hypothesis H2 of reduction Erdos997.erdos_997.variants.irrational.R1.H1.R1
-- Credit: @hayalows
--
-- H2 is the combinatorial half of the Shiu reduction: a run of k consecutive
-- good indices is itself a block in which the good indices outnumber (k-1) times
-- one more than the bad ones. Taking l = m and r = m + k, the block has no bad
-- index and exactly k good indices, so the inequality reads (k-1)*(0+1) < k.

open Finset

theorem OMA.solution :
    OMA.R_Erdos997_erdos_997_variants_irrational_R1_H1_R1.H2 := by
  intro good k hk ⟨m, hm⟩
  refine ⟨m, m + k, ?_⟩
  have htrue : (Ico m (m + k)).filter (fun i => good i = true) = Ico m (m + k) :=
    filter_true_of_mem (fun i hi => hm i hi)
  have hfalse : (Ico m (m + k)).filter (fun i => good i = false) = ∅ :=
    filter_false_of_mem (fun i hi h => by
      have hgood := hm i hi
      rw [h] at hgood
      exact Bool.false_ne_true hgood)
  have hcard : (Ico m (m + k)).card = k := by
    rw [Nat.card_Ico]
    omega
  rw [htrue, hfalse]
  simp only [card_empty, Nat.zero_add, mul_one, hcard]
  omega
