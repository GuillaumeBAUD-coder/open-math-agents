import FormalConjectures.ErdosProblems.«159»
import Mathlib.Tactic

/-!
# Reduction R1 of Erdős Problem 159 (Erdos159.erdos_159)

Target (erdosproblems.com/159, $100 prize offered by Erdős): there is `c > 0` with
`R(C_4, K_n) ≪ n^(2-c)`, formally

  `∃ c > 0, ∃ C, ∀ n ≥ 1, graphRamsey (cycleGraph 4) (completeGraph (Fin n)) ≤ C * n^(2-c)`.

State of the art (erdosproblems.com/159, edited 2026-03): `n^(3/2)/(log n)^(3/2) ≪ R(C_4,K_n)
≪ n^2/(log n)^2`, the upper bound due to Szemerédi (in [EFRS78]) and the lower bound to Spencer
[Sp77]. So the problem is exactly the question whether the upper bound can be pushed below every
polylogarithmic saving, and it is open; the known bounds are not enough, `n^2/(log n)^2` being
larger than `n^(2-c)` for every fixed `c > 0` and large `n`.

This is an `∃`-type asymptotic statement, and the file splits it in the standard way for such
statements, with the arithmetic of the merge (including the powers) proved here:

* `H1` is the research content: the bound for all `n >= 4`, with `0 < c < 1` and a positive
  constant. This is the whole difficulty of the problem; it is not a published theorem.
* `H2` is the finitely many remaining cases `1 <= n < 4`, bounded by one absolute constant: a
  finite statement that can be discharged by explicit Ramsey constructions, and it is *not*
  derivable from `H1`'s constants, so assuming it costs nothing.

`main` merges the two: for `n >= 4` use `H1`, for `1 <= n < 4` use `H2` together with
`n^(2-c) >= 1` (which holds because `1 <= n` and `0 < 2 - c`), and take the maximum constant.
-/

namespace OMA.R_Erdos159_erdos_159_R3

/-- The asymptotic case of Erdős Problem 159: one polynomial saving below `n^2`, for `n >= 4`. -/
def H1 : Prop :=
  ∃ (c : ℝ), 0 < c ∧ c < 1 ∧ ∃ (C : ℝ), 0 < C ∧
    ∀ (n : ℕ), 4 ≤ n →
      (SimpleGraph.graphRamsey (SimpleGraph.cycleGraph 4)
        (SimpleGraph.completeGraph (Fin n)) : ℝ) ≤ C * (n : ℝ) ^ (2 - c)

/-- The finitely many small cases `1 <= n < 4` of Erdős Problem 159, with one absolute
constant. -/
def H2 : Prop :=
  ∃ (C : ℝ), 0 ≤ C ∧
    ∀ (n : ℕ), 1 ≤ n → n < 4 →
      (SimpleGraph.graphRamsey (SimpleGraph.cycleGraph 4)
        (SimpleGraph.completeGraph (Fin n)) : ℝ) ≤ C

theorem main : H1 → H2 → type_of% @Erdos159.erdos_159 := by
  intro h1 h2
  obtain ⟨c, hc0, hc1, C, hC0, hbound⟩ := h1
  obtain ⟨C₀, hC₀, hbnd₀⟩ := h2
  refine ⟨c, hc0, max C C₀, ?_⟩
  intro n hn
  have hpow : (1 : ℝ) ≤ (n : ℝ) ^ (2 - c) := by
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hexp : (0 : ℝ) ≤ 2 - c := by linarith
    exact Real.one_le_rpow hn1 hexp
  have hpow0 : (0 : ℝ) ≤ (n : ℝ) ^ (2 - c) := le_trans zero_le_one hpow
  by_cases hsmall : n < 4
  · have hb := hbnd₀ n hn hsmall
    have h1' : C₀ ≤ C₀ * (n : ℝ) ^ (2 - c) := by
      calc C₀ = C₀ * 1 := (mul_one C₀).symm
        _ ≤ C₀ * (n : ℝ) ^ (2 - c) := by
            exact mul_le_mul_of_nonneg_left hpow hC₀
    have h2' : C₀ * (n : ℝ) ^ (2 - c) ≤ max C C₀ * (n : ℝ) ^ (2 - c) := by
      exact mul_le_mul_of_nonneg_right (le_max_right C C₀) hpow0
    linarith
  · have hbig : 4 ≤ n := by omega
    have hb := hbound n hbig
    have h2' : C * (n : ℝ) ^ (2 - c) ≤ max C C₀ * (n : ℝ) ^ (2 - c) := by
      exact mul_le_mul_of_nonneg_right (le_max_left C C₀) hpow0
    linarith

end OMA.R_Erdos159_erdos_159_R3
