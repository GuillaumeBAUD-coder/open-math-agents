import OMAStatements.S_oeis_a034863
import Mathlib

/-!
# A034863: the conjectured P-recurrence

For n ≥ 4, 24 ∣ n!, so a(n) = (n!/24)·(4n³ − 30n² + 40n + 3) exactly. Writing (n+6)!/24 and
(n+5)!/24 as (n+6)(n+5) and (n+5) times (n+4)!/24, the three terms of the recurrence at n = m + 6
are polynomial multiples of (m+4)!/24, and the identity is checked by expanding.
-/

namespace PA034863

theorem a_eq (n : ℕ) :
    OMA.S_oeis_a034863.a (n + 4) =
      ((n + 4).factorial / 24 : ℕ) * (4 * ((n + 4 : ℕ) : ℤ) ^ 3 - 30 * ((n + 4 : ℕ) : ℤ) ^ 2 +
        40 * ((n + 4 : ℕ) : ℤ) + 3) := by
  unfold OMA.S_oeis_a034863.a
  have h24 : 24 ∣ (n + 4).factorial := Nat.factorial_dvd_factorial (show 4 ≤ n + 4 by omega)
  obtain ⟨q, hq⟩ := h24
  rw [hq, Nat.mul_div_cancel_left _ (by norm_num)]
  push_cast
  rw [mul_assoc, Int.mul_ediv_cancel_left _ (by norm_num)]

theorem fact_rel (n : ℕ) :
    (((n + 6).factorial / 24 : ℕ) : ℤ) = (n + 6) * (n + 5) * (((n + 4).factorial / 24 : ℕ) : ℤ) ∧
    (((n + 5).factorial / 24 : ℕ) : ℤ) = (n + 5) * (((n + 4).factorial / 24 : ℕ) : ℤ) := by
  have h24 : 24 ∣ (n + 4).factorial := Nat.factorial_dvd_factorial (show 4 ≤ n + 4 by omega)
  obtain ⟨q, hq⟩ := h24
  have e6 : (n + 6).factorial = 24 * ((n + 6) * (n + 5) * q) := by
    rw [Nat.factorial_succ, Nat.factorial_succ, hq]; ring
  have e5 : (n + 5).factorial = 24 * ((n + 5) * q) := by
    rw [Nat.factorial_succ, hq]; ring
  rw [e6, e5, hq, Nat.mul_div_cancel_left _ (by norm_num), Nat.mul_div_cancel_left _ (by norm_num),
    Nat.mul_div_cancel_left _ (by norm_num)]
  push_cast
  constructor <;> ring

end PA034863

theorem OMA.solution : type_of% @OMA.S_oeis_a034863.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
  rw [show m + 6 - 1 = (m + 1) + 4 by omega, show m + 6 - 2 = m + 4 by omega,
    show m + 6 = (m + 2) + 4 by omega, PA034863.a_eq, PA034863.a_eq, PA034863.a_eq]
  obtain ⟨h6, h5⟩ := PA034863.fact_rel m
  rw [show m + 2 + 4 = m + 6 by ring, show m + 1 + 4 = m + 5 by ring, h6, h5]
  push_cast
  ring
