import FormalConjectures.ErdosProblems.«1130»

-- Reduction Erdos1130.erdos_1130.parts.i.R1 of Erdős Problem 1130 — i
-- Credit: @ashnewmanjones
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
-- The split follows the literature proof: Erdős inequality (Kilgore, de Boor and Pinkus)
-- plus a node set whose Lebesgue constant is O(log n) (the Chebyshev nodes, Erdős 1961).

namespace OMA.R_Erdos1130_erdos_1130_parts_i_R1

open Erdos1129 Erdos1130

-- The Erdős inequality (Kilgore 1977/78, de Boor and Pinkus 1978): for any two node sets
-- x and y with n ≥ 2 nodes, the smallest local maximum Υ(x) of the Lebesgue function of x
-- is at most the Lebesgue constant of y. Equivalently Υ(x) ≤ Λ*, the minimal Lebesgue constant.
def H1 : Prop :=
  ∀ (n : ℕ) (x y : Fin n → ℝ), 2 ≤ n → IsNodeSet x → IsNodeSet y →
    upsilon x ≤ lebesgueConstant y

-- Some node set has Lebesgue constant O(log n): for instance the Chebyshev nodes, whose
-- Lebesgue constant is below (2/π) log n + O(1) (Erdős 1961, p. 236).
def H2 : Prop :=
  ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n →
    ∃ y : Fin n → ℝ, IsNodeSet y ∧ lebesgueConstant y ≤ C * Real.log n

theorem main : H1 → H2 → type_of% @Erdos1130.erdos_1130.parts.i := by
  rintro h1 ⟨C, hC⟩
  refine ⟨max C 1, lt_of_lt_of_le one_pos (le_max_right _ _), ?_⟩
  intro n x hn hx
  obtain ⟨y, hy, hyC⟩ := hC n hn
  have hlog : 0 ≤ Real.log n :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  calc upsilon x ≤ lebesgueConstant y := h1 n x y hn hx hy
    _ ≤ C * Real.log n := hyC
    _ ≤ max C 1 * Real.log n := mul_le_mul_of_nonneg_right (le_max_left _ _) hlog

end OMA.R_Erdos1130_erdos_1130_parts_i_R1
