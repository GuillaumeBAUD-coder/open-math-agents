import FormalConjectures.ErdosProblems.«686»

-- Reduction Erdos686.erdos_686.R1 of Erdős Problem 686
-- Credit: @jagong-cmu
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
-- Split along the known/open boundary: H1 is the non-square case (known, via Pell equations
-- with k = 2), H2 is the square case (open; this contains the open cases N = 4 and N = 25).

namespace OMA.R_Erdos686_erdos_686_R1

/-- The non-square case: every non-square N at least 2 has such a representation. -/
def H1 : Prop :=
  ∀ N ≥ (2 : ℕ), (¬ IsSquare N) → ∃ᵉ (k ≥ 2) (n : ℕ) (m ≥ n + k),
    (N : ℚ) = (∏ i ∈ Finset.Icc 1 k, (m + i)) / (∏ i ∈ Finset.Icc 1 k, (n + i))

/-- The square case: every square N at least 2 has such a representation (open). -/
def H2 : Prop :=
  ∀ N ≥ (2 : ℕ), (IsSquare N) → ∃ᵉ (k ≥ 2) (n : ℕ) (m ≥ n + k),
    (N : ℚ) = (∏ i ∈ Finset.Icc 1 k, (m + i)) / (∏ i ∈ Finset.Icc 1 k, (n + i))

theorem main : H1 → H2 → type_of% @Erdos686.erdos_686 := by
  intro h1 h2 N hN
  by_cases hs : IsSquare N
  · exact h2 N hN hs
  · exact h1 N hN hs

end OMA.R_Erdos686_erdos_686_R1
