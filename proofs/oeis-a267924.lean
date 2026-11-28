import OMAStatements.S_oeis_a267924
import Mathlib

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Sketch: Rule 245 is l or (not r). By induction, row t+1 is ON everywhere except at cell t-1,
-- so a(n+1) = (2^(2n+3) - 1) - 2^2 = 2^(2n+3) - 5. The recurrence follows from this closed form,
-- and the generating function by comparing coefficients (a(0) = 1, a(1) = 3, a(2) = 27).
-- No computer search.

namespace OMA.A267924Proof
open PowerSeries OMA.S_oeis_a267924
lemma rule_eq (l c r : Bool) : rule l c r = (l || !r) := by
  cases l <;> cases c <;> cases r <;> decide

lemma rowS (t : ℕ) (i : ℤ) : row (t + 1) i = decide (i ≠ (t : ℤ) - 1) := by
  induction t generalizing i with
  | zero =>
    show rule _ _ _ = _
    simp only [row, rule_eq]
    rw [Bool.eq_iff_iff]; simp; omega
  | succ t ih =>
    show rule _ _ _ = _
    rw [ih, ih, ih, rule_eq, Bool.eq_iff_iff]; push_cast; simp; omega

lemma geo (m : ℕ) : ∑ k ∈ Finset.range m, (2 : ℤ) ^ k = 2 ^ m - 1 := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring

lemma aS (n : ℕ) : (a (n + 1) : ℤ) = 2 ^ (2 * n + 3) - 5 := by
  unfold a
  push_cast
  have h : ∀ k ∈ Finset.range (2 * (n + 1) + 1),
      (if row (n + 1) ((n : ℤ) + 1 - (k : ℤ)) = true then (2 : ℤ) ^ k else 0) =
        2 ^ k - if k = 2 then (2 : ℤ) ^ k else 0 := by
    intro k _
    rw [rowS]
    by_cases hk : k = 2
    · subst hk; simp; ring
    · simp [hk]; intro h; omega
  rw [Finset.sum_congr rfl h, Finset.sum_sub_distrib, geo, Finset.sum_ite_eq']
  rw [if_pos (by simp)]
  rw [show 2 * (n + 1) + 1 = 2 * n + 3 by ring]
  ring

theorem main_proof :
    (∀ n : ℕ, 2 < n → (a n : ℤ) = 5 * a (n - 1) - 4 * a (n - 2)) ∧
    PowerSeries.mk (fun n => (a n : ℤ)) * ((1 - X) * (1 - 4 * X)) = 1 - 2 * X + 16 * X ^ 2 := by
  have a0 : (a 0 : ℤ) = 1 := by decide
  have hrec : ∀ m : ℕ, (a (m + 3) : ℤ) = 5 * a (m + 2) - 4 * a (m + 1) := by
    intro m
    rw [aS, aS, aS]
    rw [show 2 * (m + 2) + 3 = (2 * m + 3) + 4 by ring, show 2 * (m + 1) + 3 = (2 * m + 3) + 2 by ring,
      pow_add, pow_add]
    ring
  refine ⟨fun n hn => ?_, ?_⟩
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
    simp only [show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega]
    exact hrec m
  · have hP : ((1 - X) * (1 - 4 * X) : PowerSeries ℤ) = X ^ 0 - X ^ 1 - X ^ 1 - X ^ 1 - X ^ 1 - X ^ 1
        + X ^ 2 + X ^ 2 + X ^ 2 + X ^ 2 := by ring
    have hQ : (1 - 2 * X + 16 * X ^ 2 : PowerSeries ℤ) = X ^ 0 - X ^ 1 - X ^ 1 + X ^ 2 + X ^ 2 + X ^ 2 + X ^ 2 + X ^ 2 + X ^ 2 + X ^ 2 + X ^ 2 + X ^ 2 + X ^ 2 + X ^ 2 + X ^ 2 + X ^ 2 + X ^ 2 + X ^ 2 + X ^ 2 := by ring
    rw [hP, hQ]
    ext n
    simp only [mul_sub, mul_add, map_sub, map_add, coeff_mul_X_pow', coeff_mk, coeff_X_pow]
    rcases Nat.lt_or_ge n 3 with h | h
    · interval_cases n
      · simp [a0]
      · simp [a0, aS 0]
      · simp [a0, aS 0, aS 1]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
      simp only [show 0 ≤ m + 3 by omega, show 1 ≤ m + 3 by omega, show 2 ≤ m + 3 by omega, if_true,
        show m + 3 ≠ 0 by omega, show m + 3 ≠ 1 by omega, show m + 3 ≠ 2 by omega, if_false,
        show m + 3 - 0 = m + 3 by omega, show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega]
      linear_combination hrec m
end OMA.A267924Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a267924.main := OMA.A267924Proof.main_proof
