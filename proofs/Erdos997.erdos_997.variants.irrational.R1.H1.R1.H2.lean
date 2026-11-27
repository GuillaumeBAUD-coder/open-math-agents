import OMAReductions.R_Erdos997_erdos_997_variants_irrational_R1_H1_R1
import Mathlib

/-!
Step H2 of Erdos997.erdos_997.variants.irrational.R1.H1.R1: take the block [m, m + k) of
good indices itself; it has k good indices and no bad one, and k - 1 < k.
-/

theorem OMA.solution : OMA.R_Erdos997_erdos_997_variants_irrational_R1_H1_R1.H2 := by
  unfold OMA.R_Erdos997_erdos_997_variants_irrational_R1_H1_R1.H2
  intro good k hk ⟨m, hm⟩
  refine ⟨m, m + k, ?_⟩
  have hbad : (Finset.Ico m (m + k)).filter (fun i => good i = false) = ∅ := by
    apply Finset.filter_false_of_mem
    intro i hi
    simp [hm i hi]
  have hgood : (Finset.Ico m (m + k)).filter (fun i => good i = true) = Finset.Ico m (m + k) := by
    apply Finset.filter_true_of_mem
    intro i hi
    exact hm i hi
  rw [hbad, hgood, Finset.card_empty, Nat.card_Ico]
  omega
