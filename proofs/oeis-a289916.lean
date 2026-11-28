import OMAStatements.S_oeis_a289916
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.Round
import Mathlib.Data.Rat.Floor

/-!
# Strict growth of OEIS A289916

Clark Kimberling's original sequence is the reciprocal of the series with coefficients
`(-1)^n round(9(n+1)/7)`. This file proves the bridge to Colin Barker's rational
generating function and derives strict increase. The floor expression below implements
nearest-integer rounding exactly because a rational with odd denominator 7 cannot be a half-integer.
Sources include https://oeis.org/A289916 and the prior proof of strict increase for Barker's
rational form in the TrureTuring repository, commit 687878cf845802aba2692eeb304cb960d1306431.
See D5/S1/Recurrence/Algebraic/OEISA289916StrictIncrease.lean in that repository.
-/
namespace A289916
open PowerSeries
open scoped PowerSeries

def rounded (n : ℕ) : ℤ := (((18 * (n + 1) + 7) / 14 : ℕ) : ℤ)
def signed (n : ℕ) : ℤ := (-1 : ℤ) ^ n * rounded n
noncomputable def D : ℤ⟦X⟧ := mk signed
noncomputable def A : ℤ⟦X⟧ := invOfUnit D 1
noncomputable def a (n : ℕ) : ℤ := coeff n A
noncomputable def N : ℤ⟦X⟧ := 1 + X ^ 1 + X ^ 7 + X ^ 8
noncomputable def Q : ℤ⟦X⟧ := 1 - X ^ 1 - X ^ 1 + X ^ 2 - X ^ 3 + X ^ 4 - X ^ 5 - X ^ 5 + X ^ 6

theorem rounded_eq_round (n : ℕ) : rounded n = round (9 * ((n : ℚ) + 1) / 7) := by
  rw [round_eq]
  have e : 9 * ((n : ℚ) + 1) / 7 + 1 / 2 =
      ((18 * (n + 1) + 7 : ℕ) : ℚ) / ((14 : ℕ) : ℚ) := by
    push_cast
    ring
  rw [e, Rat.floor_natCast_div_natCast]
  exact Int.natCast_ediv _ _

theorem rounded_shift (n : ℕ) : rounded (n + 7) = rounded n + 9 := by
  unfold rounded
  omega

theorem signed_shift (n : ℕ) : signed (n + 7) = -signed n - 9 * (-1 : ℤ) ^ n := by
  simp only [signed, pow_add, rounded_shift]
  ring

theorem denominator_identity : D * N = Q := by
  ext n
  simp only [D, N, Q, mul_add, mul_one, map_add, map_sub, coeff_mul_X_pow', coeff_mk,
    coeff_X_pow, coeff_one]
  by_cases h : n < 8
  · interval_cases n <;> decide
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 8 := ⟨n - 8, by omega⟩
    have h0 := signed_shift m
    have h1 := signed_shift (m + 1)
    change signed (m + 8) = -signed (m + 1) - 9 * (-1 : ℤ) ^ (m+1) at h1
    simp only [pow_succ] at h1
    simp [show ¬m+8 = 1 by omega,
      show ¬m+8 = 2 by omega, show ¬m+8 = 3 by omega, show ¬m+8 = 4 by omega,
      show ¬m+8 = 5 by omega, show ¬m+8 = 6 by omega, h0, h1]

theorem reciprocal_identity : A * D = 1 := by
  apply invOfUnit_mul
  rw [D, constantCoeff_mk]
  decide

theorem rational_identity : A * Q = N := by
  rw [← denominator_identity, ← mul_assoc, reciprocal_identity, one_mul]

noncomputable def lag (n k : ℕ) : ℤ := if k ≤ n then a (n-k) else 0

def pulse (n : ℕ) : ℤ := (if n = 0 then 1 else 0) + (if n = 1 then 1 else 0) +
  (if n = 7 then 1 else 0) + (if n = 8 then 1 else 0)

theorem recurrence (n : ℕ) : a n - lag n 1 - lag n 1 + lag n 2 - lag n 3 + lag n 4 -
    lag n 5 - lag n 5 + lag n 6 = pulse n := by
  have h := congrArg (coeff n) rational_identity
  simpa only [Q, N, a, lag, pulse, mul_add, mul_sub, mul_one, map_add, map_sub,
    coeff_mul_X_pow', coeff_X_pow, coeff_one] using h

theorem strict_growth : StrictMono a := by
  have h0 := recurrence 0
  have h1 := recurrence 1
  have h2 := recurrence 2
  have h3 := recurrence 3
  have h4 := recurrence 4
  have h5 := recurrence 5
  norm_num [lag, pulse] at h0 h1 h2 h3 h4 h5
  have hp : ∀ n, 0 < a n ∧ a n < a (n+1) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      by_cases hs : n < 5
      · interval_cases n <;> norm_num <;> omega
      · obtain ⟨m,rfl⟩ : ∃ m, n = m+5 := ⟨n-5, by omega⟩
        have hr := recurrence (m+6)
        have nonneg : 0 ≤ pulse (m+6) := by unfold pulse; split_ifs <;> omega
        have g0 := ih m (by omega)
        have g2 := ih (m+2) (by omega)
        have g4 := ih (m+4) (by omega)
        change 0 < a (m+2) ∧ a (m+2) < a (m+3) at g2
        change 0 < a (m+4) ∧ a (m+4) < a (m+5) at g4
        change 0 < a (m+5) ∧ a (m+5) < a (m+6)
        simp [lag] at hr
        omega
  exact strictMono_nat_of_lt_succ fun n => (hp n).2

/-- The exact original reciprocal series has strictly increasing coefficients. -/
theorem original_strict_growth : StrictMono (fun n : ℕ => coeff n (invOfUnit
    (mk (fun k : ℕ => (-1 : ℤ)^k * round (9 * ((k : ℚ) + 1) / 7))) 1)) := by
  have hs : signed = (fun k : ℕ => (-1 : ℤ)^k * round (9 * ((k : ℚ) + 1) / 7)) := by
    funext k
    simp only [signed, rounded_eq_round]
  intro i j hij
  simpa only [a, A, D, hs] using strict_growth hij

end A289916

theorem OMA.solution : type_of% @OMA.S_oeis_a289916.main := by
  exact A289916.original_strict_growth
