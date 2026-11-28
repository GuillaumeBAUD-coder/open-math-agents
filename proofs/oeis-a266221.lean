import OMAStatements.S_oeis_a266221
import Mathlib

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Sketch: Rule 7 is (not l) and not (c and r). Stage 1 is ON except at cell 1, stage 2 is all OFF,
-- and from then on the stages alternate all OFF / all ON (induction). So black(2k+2) = 0 and
-- black(2k+3) = 4k+7, giving a(2k+1) = a(2k+2) = (k+1)(2k+3). The recurrence follows from the closed
-- form (parity of n), and the generating function by comparing coefficients.

namespace OMA.P_oeis_a266221

open OMA.S_oeis_a266221
open PowerSeries

theorem eca7 (l c r : Bool) : eca 7 l c r = (!l && !(c && r)) := by
  cases l <;> cases c <;> cases r <;> decide

theorem st1 (i : ℤ) : state 1 i = decide (i ≠ 1) := by
  simp only [state, eca7]
  by_cases h1 : i = 1
  · subst h1; decide
  · by_cases h0 : i = 0
    · subst h0; decide
    · by_cases h2 : i = -1
      · subst h2; decide
      · simp [h1, h0, h2, show i - 1 ≠ 0 by omega, show i + 1 ≠ 0 by omega]

theorem st_eo (k : ℕ) : (∀ i, state (2 * k + 2) i = false) ∧ (∀ i, state (2 * k + 3) i = true) := by
  induction k with
  | zero =>
    have h2 : ∀ i, state 2 i = false := by
      intro i
      show eca 7 (state 1 (i - 1)) (state 1 i) (state 1 (i + 1)) = false
      rw [eca7, st1, st1, st1]
      by_cases h : i = 2
      · subst h; decide
      · simp [show i - 1 ≠ 1 by omega]
    refine ⟨h2, fun i => ?_⟩
    show eca 7 (state 2 (i - 1)) (state 2 i) (state 2 (i + 1)) = true
    rw [eca7, h2, h2, h2]; rfl
  | succ k ih =>
    have h2 : ∀ i, state (2 * (k + 1) + 2) i = false := by
      intro i
      rw [show 2 * (k + 1) + 2 = (2 * k + 3) + 1 by ring]
      show eca 7 (state (2 * k + 3) (i - 1)) (state (2 * k + 3) i) (state (2 * k + 3) (i + 1)) = false
      rw [eca7, ih.2, ih.2, ih.2]; rfl
    refine ⟨h2, fun i => ?_⟩
    rw [show 2 * (k + 1) + 3 = (2 * (k + 1) + 2) + 1 by ring]
    show eca 7 (state _ (i - 1)) (state _ i) (state _ (i + 1)) = true
    rw [eca7, h2, h2, h2]; rfl

theorem black0 : black 0 = 1 := by decide

theorem black1 : black 1 = 2 := by
  unfold black
  simp only [st1]
  decide

theorem black_even (k : ℕ) : black (2 * k + 2) = 0 := by
  unfold black
  simp [(st_eo k).1]

theorem black_odd (k : ℕ) : black (2 * k + 3) = 4 * k + 7 := by
  unfold black
  simp [(st_eo k).2]
  ring

theorem a_succ (n : ℕ) : a (n + 1) = a n + black (n + 1) := by
  unfold a; rw [Finset.sum_range_succ]

theorem closed (k : ℕ) : a (2 * k + 1) = (k + 1) * (2 * k + 3) ∧ a (2 * k + 2) = (k + 1) * (2 * k + 3) := by
  induction k with
  | zero =>
    have h1 : a 1 = 3 := by rw [a_succ, black1]; unfold a; simp [black0]
    refine ⟨h1, ?_⟩
    rw [a_succ, show 0 + 1 + 1 = 2 * 0 + 2 by rfl, black_even, h1]
  | succ k ih =>
    have h1 : a (2 * (k + 1) + 1) = (k + 2) * (2 * k + 5) := by
      rw [show 2 * (k + 1) + 1 = (2 * k + 2) + 1 by ring, a_succ, ih.2,
        show 2 * k + 2 + 1 = 2 * k + 3 by ring, black_odd]; ring
    refine ⟨by rw [h1]; ring, ?_⟩
    rw [show 2 * (k + 1) + 2 = (2 * (k + 1) + 1) + 1 by ring, a_succ, h1,
      show 2 * (k + 1) + 1 + 1 = 2 * (k + 1) + 2 by ring, black_even]; ring

theorem a0 : a 0 = 1 := by unfold a; simp [black0]

theorem cf (n : ℕ) (hn : 0 < n) : 2 * (a n : ℤ) = (n + 1) * (n - (-1) ^ n + 1) := by
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [show 2 * (j + 1) = 2 * j + 2 by ring, (closed j).2, pow_add, pow_mul]
    push_cast; ring
  · rw [(closed k).1, pow_succ, pow_mul]
    push_cast; ring

theorem rec5 (n : ℕ) (hn : 5 < n) :
    (a n : ℤ) = a (n - 1) + 2 * a (n - 2) - 2 * a (n - 3) - a (n - 4) + a (n - 5) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
  have e1 := cf (m + 6) (by omega)
  have e2 := cf (m + 6 - 1) (by omega)
  have e3 := cf (m + 6 - 2) (by omega)
  have e4 := cf (m + 6 - 3) (by omega)
  have e5 := cf (m + 6 - 4) (by omega)
  have e6 := cf (m + 6 - 5) (by omega)
  rw [show m + 6 - 1 = m + 5 by omega] at e2 ⊢
  rw [show m + 6 - 2 = m + 4 by omega] at e3 ⊢
  rw [show m + 6 - 3 = m + 3 by omega] at e4 ⊢
  rw [show m + 6 - 4 = m + 2 by omega] at e5 ⊢
  rw [show m + 6 - 5 = m + 1 by omega] at e6 ⊢
  push_cast at e1 e2 e3 e4 e5 e6
  rcases neg_one_pow_eq_or ℤ m with hm | hm <;>
    simp only [pow_add, hm] at e1 e2 e3 e4 e5 e6 <;> norm_num at e1 e2 e3 e4 e5 e6 <;> linarith

theorem ps (f : ℕ → ℤ) (n k : ℕ) :
    PowerSeries.coeff n (PowerSeries.mk f * PowerSeries.X ^ k) = if k ≤ n then f (n-k) else 0 := by
  rw [PowerSeries.coeff_mul_X_pow']; simp

theorem ps1 (f : ℕ → ℤ) (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.mk f * PowerSeries.X) = if 1 ≤ n then f (n-1) else 0 := by
  rw [← ps, pow_one]

theorem main_proof :
    (∀ n : ℕ, 0 < n → 2 * (a n : ℤ) = (n + 1) * (n - (-1) ^ n + 1)) ∧
    (∀ n : ℕ, 5 < n →
      (a n : ℤ) = a (n - 1) + 2 * a (n - 2) - 2 * a (n - 3) - a (n - 4) + a (n - 5)) ∧
    mk (fun n => (a n : ℤ)) * ((1 - X) ^ 3 * (1 + X) ^ 2) =
      (1 + 2 * X - 2 * X ^ 2 + 3 * X ^ 3 + X ^ 4 - X ^ 5 : PowerSeries ℤ) := by
  refine ⟨cf, rec5, ?_⟩
  have v1 : a 1 = 3 := (closed 0).1
  have v2 : a 2 = 3 := (closed 0).2
  have v3 : a 3 = 10 := (closed 1).1
  have v4 : a 4 = 10 := (closed 1).2
  have v5 : a 5 = 21 := (closed 2).1
  rw [show ((1 - X) ^ 3 * (1 + X) ^ 2 : PowerSeries ℤ) =
      1 - X - PowerSeries.C (2:ℤ) * X ^ 2 + PowerSeries.C (2:ℤ) * X ^ 3 + X ^ 4 - X ^ 5 by
        simp only [map_ofNat]; ring,
    show (1 + 2 * X - 2 * X ^ 2 + 3 * X ^ 3 + X ^ 4 - X ^ 5 : PowerSeries ℤ) =
      1 + PowerSeries.C (2:ℤ) * X - PowerSeries.C (2:ℤ) * X ^ 2 + PowerSeries.C (3:ℤ) * X ^ 3
        + X ^ 4 - X ^ 5 by simp only [map_ofNat]]
  ext n
  simp only [mul_add, mul_sub, mul_one, map_add, map_sub, mul_left_comm _ (PowerSeries.C _),
    PowerSeries.coeff_C_mul, ps, ps1, PowerSeries.coeff_X, PowerSeries.coeff_mk,
    PowerSeries.coeff_X_pow, PowerSeries.coeff_one]
  rcases (show n ≤ 5 ∨ 6 ≤ n by omega) with h | h
  · interval_cases n <;> simp [a0, v1, v2, v3, v4, v5]
  · have hr := rec5 n (by omega)
    simp [show ¬ n ≤ 5 by omega, show n ≠ 0 by omega, show n ≠ 1 by omega, show n ≠ 2 by omega,
      show n ≠ 3 by omega, show n ≠ 4 by omega, show n ≠ 5 by omega,
      show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega, show 4 ≤ n by omega,
      show 5 ≤ n by omega]
    linarith

end OMA.P_oeis_a266221

theorem OMA.solution : type_of% @OMA.S_oeis_a266221.main := OMA.P_oeis_a266221.main_proof
