import FormalConjectures.ErdosProblems.«930»

-- Reduction Erdos930.erdos_930.R1 of Erdős Problem 930
-- Credit: @sntntHb
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- Sketch: split by the number r of intervals.
--   H1: the Erdős–Selfridge theorem (1975): a product of k ≥ 2 consecutive positive integers is
--       never a perfect power. This is stated exactly as upstream variants.consecutive_integers.
--       main derives the case r = 1 from it with k = 2: the single interval Icc a b with
--       1 ≤ a and a + 1 ≤ b is Icc (n + 1) (n + j) for n = a - 1 and j = b - a + 1 ≥ 2.
--   H2: every r ≥ 2. This is the open part (for r = 2 the intervals must be long, see Erdős 363).
-- main: case split on r = 1 or r ≥ 2. No computer search was used.

namespace OMA.R_Erdos930_erdos_930_R1

open Erdos930 Finset

def H1 : Prop :=
  ∀ n k : ℕ, 0 ≤ n → 2 ≤ k → ¬ IsPower (∏ m ∈ Icc (n + 1) (n + k), m)

def H2 : Prop :=
  ∀ r ≥ 2, ∃ k, ∀ I₁ I₂ : Fin r → ℕ,
    (∀ i : Fin r, 0 < I₁ i ∧ I₁ i + k ≤ I₂ i + 1) →
      (∀ i j : Fin r, i < j → I₂ i < I₁ j) →
        ¬ IsPower (∏ i : Fin r, ∏ m ∈ Icc (I₁ i) (I₂ i), m)

theorem main : H1 → H2 → type_of% @Erdos930.erdos_930 := by
  intro h1 h2 r hr
  rcases (by omega : r = 1 ∨ 2 ≤ r) with rfl | h
  · refine ⟨2, fun I₁ I₂ hI _ => ?_⟩
    obtain ⟨ha, hb⟩ := hI 0
    rw [Fin.prod_univ_one]
    have e1 : I₁ 0 = (I₁ 0 - 1) + 1 := by omega
    have e2 : I₂ 0 = (I₁ 0 - 1) + (I₂ 0 - I₁ 0 + 1) := by omega
    rw [e2, e1]
    simp only [Nat.add_sub_cancel]
    have := h1 (I₁ 0 - 1) (I₂ 0 - I₁ 0 + 1) (Nat.zero_le _) (by omega)
    convert this using 4 <;> omega
  · simpa [H2] using h2 r h

end OMA.R_Erdos930_erdos_930_R1
