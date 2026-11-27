import OMAReductions.R_Erdos1104_erdos_1104_variants_lower_R1
import Mathlib

-- Step Erdos1104.erdos_1104.variants.lower.R1.H2: hypothesis H2 of reduction Erdos1104.erdos_1104.variants.lower.R1
-- Credit: @ivillar
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-! Each colour class of a proper colouring is independent in `G`, i.e. a clique in the
complement, so it has fewer than `k` vertices. Summing over the `c` classes gives `n ≤ c k`. -/

theorem OMA.solution : OMA.R_Erdos1104_erdos_1104_variants_lower_R1.H2 := by
  intro n k c G hfree hcol
  classical
  obtain ⟨C⟩ := hcol
  have hclass : ∀ i : Fin c, (Finset.univ.filter (fun v => C v = i)).card ≤ k := by
    intro i
    by_contra h
    obtain ⟨t, ht, htc⟩ := Finset.exists_subset_card_eq
      (s := Finset.univ.filter (fun v => C v = i)) (n := k) (by omega)
    apply hfree t
    refine ⟨?_, htc⟩
    intro v hv w hw hvw
    rw [SimpleGraph.compl_adj]
    refine ⟨hvw, fun hadj => ?_⟩
    have hv' := (Finset.mem_filter.mp (ht hv)).2
    have hw' := (Finset.mem_filter.mp (ht hw)).2
    exact C.valid hadj (hv'.trans hw'.symm)
  calc n = (Finset.univ : Finset (Fin n)).card := by simp
    _ = ∑ i : Fin c, (Finset.univ.filter (fun v => C v = i)).card :=
        Finset.card_eq_sum_card_fiberwise (fun v _ => Finset.mem_univ (C v))
    _ ≤ ∑ _i : Fin c, k := Finset.sum_le_sum (fun i _ => hclass i)
    _ = c * k := by simp
