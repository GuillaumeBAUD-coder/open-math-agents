import OMAStatements.S_oeis_a005251
import Mathlib

/-!
# Dement's identity for OEIS A005251

`a (n + 1) + |b n| = 2 * c (n + 1)`, where `a` (A005251), `b` (A078065) and `c` (A005314)
are given by their order-three recurrences.

Proof. Put `d n = (-1)^n * b n`. Multiplying the recurrence of `b` by `(-1)^(n+3)` shows that
`d` satisfies `d (n + 3) = 2 d (n + 2) - d (n + 1) + d n`, the same recurrence as `a` and `c`.
From `d 0, d 1, d 2 = 1, 3, 5` the same recurrence gives `0 ≤ d n ≤ d (n + 1)` for all `n`,
so `|b n| = d n`. The identity `a (n + 1) + d n = 2 c (n + 1)` is linear in sequences that
share one recurrence, so it holds for all `n` once it holds for `n = 0, 1, 2`,
where both sides are `2, 4, 6`.
-/

namespace OMA.P_oeis_a005251

open OMA.S_oeis_a005251 (a b c)

/-- `d n = (-1)^n * b n` is nonnegative and nondecreasing, and `a (n + 1) + d n = 2 c (n + 1)`,
stated for three consecutive indices so that the order-three recurrences can be used. -/
theorem key (n : ℕ) :
    (0 ≤ (-1 : ℤ) ^ n * b n ∧
      (-1 : ℤ) ^ n * b n ≤ (-1 : ℤ) ^ (n + 1) * b (n + 1) ∧
      (-1 : ℤ) ^ (n + 1) * b (n + 1) ≤ (-1 : ℤ) ^ (n + 2) * b (n + 2)) ∧
    (a (n + 1) + (-1 : ℤ) ^ n * b n = 2 * c (n + 1) ∧
      a (n + 2) + (-1 : ℤ) ^ (n + 1) * b (n + 1) = 2 * c (n + 2) ∧
      a (n + 3) + (-1 : ℤ) ^ (n + 2) * b (n + 2) = 2 * c (n + 3)) := by
  induction n with
  | zero => decide +kernel
  | succ n ih =>
    obtain ⟨⟨h0, h1, h2⟩, i0, i1, i2⟩ := ih
    have ha : a (n + 4) = 2 * a (n + 3) - a (n + 2) + a (n + 1) := rfl
    have hc : c (n + 4) = 2 * c (n + 3) - c (n + 2) + c (n + 1) := rfl
    have hb : b (n + 3) = -2 * b (n + 2) - b (n + 1) - b n := rfl
    have hd : (-1 : ℤ) ^ (n + 3) * b (n + 3) =
        2 * ((-1 : ℤ) ^ (n + 2) * b (n + 2)) - (-1 : ℤ) ^ (n + 1) * b (n + 1) +
          (-1 : ℤ) ^ n * b n := by
      rw [hb]; ring
    show (0 ≤ (-1 : ℤ) ^ (n + 1) * b (n + 1) ∧
        (-1 : ℤ) ^ (n + 1) * b (n + 1) ≤ (-1 : ℤ) ^ (n + 2) * b (n + 2) ∧
        (-1 : ℤ) ^ (n + 2) * b (n + 2) ≤ (-1 : ℤ) ^ (n + 3) * b (n + 3)) ∧
      (a (n + 2) + (-1 : ℤ) ^ (n + 1) * b (n + 1) = 2 * c (n + 2) ∧
        a (n + 3) + (-1 : ℤ) ^ (n + 2) * b (n + 2) = 2 * c (n + 3) ∧
        a (n + 4) + (-1 : ℤ) ^ (n + 3) * b (n + 3) = 2 * c (n + 4))
    exact ⟨⟨by linarith, h2, by linarith⟩, i1, i2, by linarith⟩

/-- The absolute value of `b n` is `(-1)^n * b n`. -/
theorem abs_b (n : ℕ) : |b n| = (-1 : ℤ) ^ n * b n := by
  have h0 := (key n).1.1
  rcases neg_one_pow_eq_or ℤ n with h | h <;> rw [h] at h0 ⊢
  · rw [abs_of_nonneg (by linarith)]; ring
  · rw [abs_of_nonpos (by linarith)]; ring

end OMA.P_oeis_a005251

theorem OMA.solution : type_of% @OMA.S_oeis_a005251.main := by
  intro n
  rw [OMA.P_oeis_a005251.abs_b n]
  exact (OMA.P_oeis_a005251.key n).2.1
