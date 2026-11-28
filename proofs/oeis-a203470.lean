import OMAStatements.S_oeis_a203470
import Mathlib

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Sketch: (1) peel off the top factor of the outer product. (2) each inner product is an ascFactorial of length j-2, divisible by (j-2)!; reindex to get superfactorial.

namespace OMA.A203470Proof
open OMA.S_oeis_a203470
theorem inner_dvd (j : ℕ) : (j - 2).factorial ∣ ∏ i ∈ Finset.Ico 2 j, (i + j) := by
  rw [Finset.prod_Ico_eq_prod_range]
  have h : ∏ k ∈ Finset.range (j - 2), (2 + k + j) = (j + 2).ascFactorial (j - 2) := by
    rw [Nat.ascFactorial_eq_prod_range]
    apply Finset.prod_congr rfl
    intro k _; ring
  rw [h]
  exact Nat.factorial_dvd_ascFactorial _ _

theorem reindex (n : ℕ) (hn : 1 ≤ n) :
    ∏ j ∈ Finset.Icc 2 (n + 1), (j - 2).factorial = ∏ k ∈ Finset.Icc 0 (n - 1), k.factorial := by
  apply Finset.prod_nbij' (fun j => j - 2) (fun k => k + 2)
  · intro a ha; simp only [Finset.mem_Icc] at ha ⊢; omega
  · intro a ha; simp only [Finset.mem_Icc] at ha ⊢; omega
  · intro a ha; simp only [Finset.mem_Icc] at ha ⊢; omega
  · intro a ha; simp only [Finset.mem_Icc] at ha ⊢; omega
  · intro a _; rfl

end OMA.A203470Proof

open OMA.S_oeis_a203470 in
theorem OMA.solution : type_of% @OMA.S_oeis_a203470.main := by
  refine ⟨fun n hn => ?_, fun n hn => ?_⟩
  · unfold a203470
    conv_rhs => rw [Finset.prod_Icc_succ_top (by omega)]
    exact Dvd.intro _ rfl
  · unfold a203470 superfactorial
    calc ∏ k ∈ Finset.Icc 1 (n - 1), k.factorial
        ∣ ∏ k ∈ Finset.Icc 0 (n - 1), k.factorial :=
          Finset.prod_dvd_prod_of_subset _ _ _ (Finset.Icc_subset_Icc (by omega) le_rfl)
      _ = ∏ j ∈ Finset.Icc 2 (n + 1), (j - 2).factorial := (OMA.A203470Proof.reindex n hn).symm
      _ ∣ _ := Finset.prod_dvd_prod_of_dvd _ _ (fun j _ => OMA.A203470Proof.inner_dvd j)
