import FormalConjectures.ErdosProblems.«462»
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.LSeries.RiemannZeta

open Filter
open scoped BigOperators

namespace OMA.R_Erdos462_erdos_462_R1

/-- Alpöge's verified theorem, stated using Mathlib's `RiemannHypothesis`. -/
def H1 : Prop := RiemannHypothesis

/-- Cramér's prime-in-short-interval theorem at natural starting points.
The registry's proof of the conditional prime gap bound establishes a stronger
real-variable statement in Cramer.vfb. -/
def H2 : Prop := RiemannHypothesis →
  ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℕ in atTop,
    ∃ p : ℕ, p.Prime ∧ x ≤ p ∧
      (p : ℝ) ≤ (x : ℝ) + C * Real.sqrt x * Real.log x

theorem main : H1 → H2 → type_of% @Erdos462.erdos_462 := by
  intro rh cramer
  obtain ⟨C, hC, hPrimes⟩ := cramer rh
  refine ⟨C, 1, hC, zero_lt_one, ?_⟩
  obtain ⟨N, hN⟩ := exists_nat_gt (Real.exp 1)
  have hLarge : ∀ᶠ x : ℕ in atTop, N ≤ x := eventually_ge_atTop N
  filter_upwards [hPrimes, hLarge] with x hx hNx
  obtain ⟨p, hp, hxp, hpUpper⟩ := hx
  have hExp : Real.exp 1 ≤ (x : ℝ) := hN.le.trans (Nat.cast_le.mpr hNx)
  have hxPos : 0 < (x : ℝ) := (Real.exp_pos 1).trans_le hExp
  have hLog : 1 ≤ Real.log x := (Real.le_log_iff_exp_le hxPos).2 hExp
  have hLogSq : Real.log x ≤ (Real.log x) ^ 2 := by
    nlinarith [sq_nonneg (Real.log x - 1)]
  let s := Finset.Icc x ⌊(x : ℝ) + C * Real.sqrt x * (Real.log x) ^ 2⌋₊
  have hpMem : p ∈ s := by
    apply Finset.mem_Icc.mpr
    refine ⟨hxp, Nat.le_floor ?_⟩
    exact hpUpper.trans (add_le_add_right
      (mul_le_mul_of_nonneg_left hLogSq (mul_nonneg hC.le (Real.sqrt_nonneg _))) _)
  have hpWeight : (p.minFac : ℝ) / (p : ℝ) = 1 := by
    rw [hp.minFac_eq, div_self (Nat.cast_ne_zero.mpr hp.ne_zero)]
  rw [← hpWeight]
  have hNonneg (n : ℕ) (_ : n ∈ s) : 0 ≤ (n.minFac : ℝ) / (n : ℝ) :=
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  exact Finset.single_le_sum hNonneg hpMem

end OMA.R_Erdos462_erdos_462_R1
