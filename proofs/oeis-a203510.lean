import OMAStatements.S_oeis_a203510
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-! OEIS A203510: `∏_{i=1}^{n-1} i!` divides `∏_{1 ≤ j < k ≤ n} (k! + j!)`.

Take the factor `k = n` of the product: for `j < n`, `j!` divides `n!`, hence `j! ∣ n! + j!`. So
`∏_{j=1}^{n-1} j! ∣ ∏_{j=1}^{n-1} (n! + j!)`, which divides the whole product. -/

namespace OpenMath.A203510

open Finset OMA.S_oeis_a203510

theorem main : ∀ n : ℕ, 1 ≤ n → superfactorial (n - 1) ∣ A203482 n := by
  intro n hn
  rcases Nat.lt_or_ge n 2 with h | h
  · obtain rfl : n = 1 := by omega
    simp [superfactorial]
  · have hs : superfactorial (n - 1) = ∏ j ∈ Ico 1 n, j.factorial := by
      unfold superfactorial
      congr 1
    have h1 : superfactorial (n - 1) ∣ ∏ j ∈ Ico 1 n, (n.factorial + j.factorial) := by
      rw [hs]
      refine Finset.prod_dvd_prod_of_dvd _ _ fun j hj => ?_
      have hj' : j ≤ n := by
        simp only [Finset.mem_Ico] at hj
        omega
      exact Nat.dvd_add (Nat.factorial_dvd_factorial hj') dvd_rfl
    unfold A203482
    exact h1.trans (Finset.dvd_prod_of_mem (fun k => ∏ j ∈ Ico 1 k, (k.factorial + j.factorial))
      (Finset.mem_Icc.2 ⟨h, le_rfl⟩))

end OpenMath.A203510

theorem OMA.solution : type_of% @OMA.S_oeis_a203510.main := OpenMath.A203510.main
