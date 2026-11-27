import OMAStatements.S_oeis_a259661

-- Problem: A259661: Binary representation of the middle column of the "Rule 54" elementary cellular automaton starting with a single ON (black) cell.
-- Upstream: formal-conjectures statements/oeis-a259661.lean:0 (declaration OMA.S_oeis_a259661.main)
-- Credit: @caa1982 (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace R54
open OMA.S_oeis_a259661
def f (t : ℕ) (i : ℤ) : Bool :=
  decide (-(t : ℤ) ≤ i ∧ i ≤ t ∧ ((t % 2 = 0 ∧ (i + t) % 4 = 0) ∨ (t % 2 = 1 ∧ (i + t) % 4 ≠ 3)))

lemma rule54 (l c r : Bool) : ruleOut 54 l c r = xor c (l || r) := by
  cases l <;> cases c <;> cases r <;> rfl

lemma cell_eq (t : ℕ) (i : ℤ) : cell 54 t i = f t i := by
  induction t generalizing i with
  | zero =>
    simp only [cell, f]
    by_cases h : i = 0 <;> simp [h] <;> omega
  | succ t ih =>
    show ruleOut 54 (cell 54 t (i - 1)) (cell 54 t i) (cell 54 t (i + 1)) = _
    rw [rule54, ih, ih, ih]
    cases h1 : f t (i - 1) <;> cases h2 : f t i <;> cases h3 : f t (i + 1) <;>
      cases h4 : f (t + 1) i <;>
      simp only [f, decide_eq_true_eq, decide_eq_false_iff_not] at h1 h2 h3 h4 <;>
      first | rfl | (exfalso; omega)

def c (t : ℕ) : ℤ := if t % 4 < 2 then 1 else 0

lemma center (t : ℕ) : (if cell 54 t 0 then (1:ℤ) else 0) = c t := by
  rw [cell_eq]
  unfold c
  cases h : f t 0 <;> simp only [f, decide_eq_true_eq, decide_eq_false_iff_not] at h <;>
    simp only [Bool.false_eq_true, ↓reduceIte] <;> split_ifs <;> first | rfl | (exfalso; omega)

lemma a_succ (n : ℕ) : a (n+1) = 10 * a n + c (n+1) := by
  unfold a
  rw [Finset.sum_range_succ, Nat.sub_self, pow_zero, center]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  rw [Finset.mem_range] at ht
  split_ifs
  · rw [show n + 1 - t = (n - t) + 1 by omega, pow_succ]; ring
  · simp

lemma rec1 (m : ℕ) : a (m+4) = 11 * a (m+3) - 11 * a (m+2) + 11 * a (m+1) - 10 * a m := by
  have h1 := a_succ (m+3)
  have h2 := a_succ (m+2)
  have h3 := a_succ (m+1)
  have h4 := a_succ m
  have hc : c (m+3+1) - c (m+2+1) + c (m+1+1) - c (m+1) = 0 := by
    unfold c; split_ifs <;> omega
  linarith

open PowerSeries in
theorem sol :
    (∀ n > 3, a n = 11 * a (n - 1) - 11 * a (n - 2) + 11 * a (n - 3) - 10 * a (n - 4)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) * (1 - 10 * X) * (1 + X ^ 2)) = 1) := by
  refine ⟨?_, ?_⟩
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    rw [show m + 4 - 1 = m + 3 by omega, show m + 4 - 2 = m + 2 by omega,
      show m + 4 - 3 = m + 1 by omega, show m + 4 - 4 = m by omega]
    exact rec1 m
  · have hC1 : (C (11:ℚ) : ℚ⟦X⟧) = 11 := map_ofNat C 11
    have hC2 : (C (10:ℚ) : ℚ⟦X⟧) = 10 := map_ofNat C 10
    have hP : ∀ A : ℚ⟦X⟧, A * ((1 - X) * (1 - 10 * X) * (1 + X ^ 2)) =
        A - C (11:ℚ) * (A * X^1) + C (11:ℚ) * (A * X^2) - C (11:ℚ) * (A * X^3)
          + C (10:ℚ) * (A * X^4) := by
      intro A; rw [hC1, hC2]; ring
    rw [hP]
    ext n
    simp only [map_add, map_sub, coeff_C_mul, coeff_mul_X_pow', coeff_mk, coeff_one]
    have a0 : a 0 = 1 := by decide
    have a1 : a 1 = 11 := by decide
    have a2 : a 2 = 110 := by decide
    have a3 : a 3 = 1100 := by decide
    rcases n with _ | _ | _ | _ | n
    · norm_num [a0]
    · norm_num [a0, a1]
    · norm_num [a0, a1, a2]
    · norm_num [a0, a1, a2, a3]
    · simp only [show n + 1 + 1 + 1 + 1 = n + 4 by omega]
      simp only [show 1 ≤ n + 4 by omega, show n + 4 - 1 = n + 3 by omega, show 2 ≤ n + 4 by omega, show 3 ≤ n + 4 by omega, show 4 ≤ n + 4 by omega,
        if_true, show n + 4 - 2 = n + 2 by omega, show n + 4 - 3 = n + 1 by omega,
        show n + 4 - 4 = n by omega]
      simp
      have := rec1 n
      have h : ((a (n+4) : ℤ) : ℚ) = 11 * (a (n+3) : ℚ) - 11 * (a (n+2) : ℚ) + 11 * (a (n+1) : ℚ)
          - 10 * (a n : ℚ) := by
        rw [this]; push_cast; ring
      linarith

end R54

theorem OMA.solution : type_of% @OMA.S_oeis_a259661.main := R54.sol
