import OMAStatements.S_oeis_a008749
import Mathlib

namespace A008749Aux

/-- The expected coefficients of `(1 - X) * f`: constant term one, then the sequence `bSeq`. -/
def cS : ℕ → ℤ
  | 0 => 1
  | n + 1 => (OMA.S_oeis_a008749.bSeq n : ℤ)

open PowerSeries in
lemma coeff_term (f : ℕ → ℤ) (c : ℤ) (k n : ℕ) :
    coeff n (mk f * (C c * X ^ k)) = if k ≤ n then c * f (n - k) else 0 := by
  rw [← mul_assoc, mul_comm (mk f) (C c), mul_assoc, coeff_C_mul, coeff_mul_X_pow']
  split_ifs <;> simp [coeff_mk]

open OMA.S_oeis_a008749 in
lemma brec (m : ℕ) : cS (m + 7) - cS (m + 5) - cS (m + 4) + cS (m + 2) = 0 := by
  simp only [cS, bSeq]
  split_ifs <;> omega

open PowerSeries OMA.S_oeis_a008749 in
lemma key : PowerSeries.mk cS * ((1 - X ^ 2) * (1 - X ^ 3)) = (1 + X ^ 6 : PowerSeries ℤ) := by
  have hP : ((1 - X ^ 2) * (1 - X ^ 3) : PowerSeries ℤ) =
      C (1 : ℤ) * X ^ 0 + C (-1 : ℤ) * X ^ 2 + C (-1 : ℤ) * X ^ 3 + C (1 : ℤ) * X ^ 5 := by
    simp only [map_one, map_neg]
    ring
  have hN : (1 + X ^ 6 : PowerSeries ℤ) = C (1 : ℤ) * X ^ 0 + C (1 : ℤ) * X ^ 6 := by
    simp only [map_one]
    ring
  rw [hP, hN]
  ext n
  simp only [mul_add, map_add, coeff_term, PowerSeries.coeff_C_mul_X_pow]
  rcases Nat.lt_or_ge n 7 with hs | hs
  · interval_cases n <;> simp [cS, bSeq]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 7 := ⟨n - 7, by omega⟩
    rw [if_pos (show 0 ≤ m + 7 by omega), if_pos (show 2 ≤ m + 7 by omega),
      if_pos (show 3 ≤ m + 7 by omega), if_pos (show 5 ≤ m + 7 by omega),
      if_neg (show ¬ (m + 7 = 0) by omega), if_neg (show ¬ (m + 7 = 6) by omega)]
    rw [show m + 7 - 0 = m + 7 from by omega, show m + 7 - 2 = m + 5 from by omega,
      show m + 7 - 3 = m + 4 from by omega, show m + 7 - 5 = m + 2 from by omega]
    have h := brec m
    linarith

end A008749Aux

open PowerSeries OMA.S_oeis_a008749 A008749Aux in
theorem OMA.solution : type_of% @OMA.S_oeis_a008749.main := by
  intro f hf
  have hne : ((1 - X ^ 2) * (1 - X ^ 3) : PowerSeries ℤ) ≠ 0 := by
    intro h
    have h0 := congrArg (coeff 0) h
    simp at h0
  have h1 : ((1 - X ^ 2) * (1 - X ^ 3) : PowerSeries ℤ) * ((1 - X) * f) =
      ((1 - X ^ 2) * (1 - X ^ 3)) * PowerSeries.mk cS := by
    rw [mul_comm _ (PowerSeries.mk cS), key, ← hf]
    ring
  have h2 : (1 - X) * f = PowerSeries.mk cS := mul_left_cancel₀ hne h1
  refine ⟨?_, ?_⟩
  · have h3 := congrArg (coeff 0) h2
    rw [sub_mul, one_mul, map_sub, coeff_zero_X_mul, coeff_mk] at h3
    simpa [cS] using h3
  · intro n
    have h3 := congrArg (coeff (n + 1)) h2
    rw [sub_mul, one_mul, map_sub, coeff_succ_X_mul, coeff_mk] at h3
    have h4 : cS (n + 1) = (bSeq n : ℤ) := rfl
    rw [h4] at h3
    linarith
