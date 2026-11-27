import OMAStatements.S_oeis_a213203
import Mathlib

namespace A213203aux

open OMA.S_oeis_a213203 in
lemma G_closed (n : ℕ) (hn : 0 < n) (L : ℕ) :
    2 * (∑ k ∈ Finset.Icc 1 L, if n ∣ k then -(k : ℤ) else (k : ℤ))
      = (L : ℤ) * ((L : ℤ) + 1)
        - 2 * (n : ℤ) * ((L / n : ℕ) : ℤ) * (((L / n : ℕ) : ℤ) + 1) := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [Finset.sum_Icc_succ_top (by omega), mul_add, ih, Nat.succ_div]
    by_cases h : n ∣ L + 1
    · simp only [if_pos h]
      obtain ⟨c, hc⟩ := h
      have hc0 : c ≠ 0 := by
        rintro rfl
        rw [mul_zero] at hc
        omega
      obtain ⟨d, rfl⟩ : ∃ d, c = d + 1 := ⟨c - 1, by omega⟩
      have e1 : n * (d + 1) = n * d + n := by ring
      have e2 : d * n = n * d := by ring
      have e3 : (d + 1) * n = n * d + n := by ring
      have hq : L / n = d := Nat.div_eq_of_lt_le (by omega) (by omega)
      rw [hq]
      have hL : ((L : ℤ) + 1) = (n : ℤ) * ((d : ℤ) + 1) := by exact_mod_cast hc
      push_cast
      linear_combination (-4 : ℤ) * hL
    · simp only [if_neg h]
      push_cast
      ring

open OMA.S_oeis_a213203 in
lemma a_closed (i : ℕ) :
    2 * a (i + 1) = ((i : ℤ) + 1) * (i.factorial : ℤ)
      * (((i : ℤ) - 1) * (i.factorial : ℤ) - 1) := by
  unfold a
  rw [G_closed (i + 1) (by omega), Nat.factorial_succ, Nat.mul_div_cancel_left _ (by omega)]
  push_cast
  ring

end A213203aux

theorem OMA.solution : type_of% @OMA.S_oeis_a213203.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  rw [show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega,
    show m + 5 - 3 = m + 2 by omega, show m + 5 - 4 = m + 1 by omega]
  have c5 : 2 * OMA.S_oeis_a213203.a (m + 5) = _ := A213203aux.a_closed (m + 4)
  have c4 : 2 * OMA.S_oeis_a213203.a (m + 4) = _ := A213203aux.a_closed (m + 3)
  have c3 : 2 * OMA.S_oeis_a213203.a (m + 3) = _ := A213203aux.a_closed (m + 2)
  have c2 : 2 * OMA.S_oeis_a213203.a (m + 2) = _ := A213203aux.a_closed (m + 1)
  have c1 : 2 * OMA.S_oeis_a213203.a (m + 1) = _ := A213203aux.a_closed m
  have f1 : ((m + 1).factorial : ℤ) = ((m : ℤ) + 1) * (m.factorial : ℤ) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  have f2 : ((m + 2).factorial : ℤ) = ((m : ℤ) + 2) * ((m + 1).factorial : ℤ) := by
    rw [Nat.factorial_succ (m + 1)]
    push_cast
    ring
  have f3 : ((m + 3).factorial : ℤ) = ((m : ℤ) + 3) * ((m + 2).factorial : ℤ) := by
    rw [Nat.factorial_succ (m + 2)]
    push_cast
    ring
  have f4 : ((m + 4).factorial : ℤ) = ((m : ℤ) + 4) * ((m + 3).factorial : ℤ) := by
    rw [Nat.factorial_succ (m + 3)]
    push_cast
    ring
  rw [f4, f3, f2, f1] at c5
  rw [f3, f2, f1] at c4
  rw [f2, f1] at c3
  rw [f1] at c2
  push_cast at c5 c4 c3 c2 c1 ⊢
  have h2 : 2 * (OMA.S_oeis_a213203.a (m + 5)
      + (-(((m : ℤ) + 5) ^ 2) - ((m : ℤ) + 5) - 11) * OMA.S_oeis_a213203.a (m + 4)
      + (((m : ℤ) + 5) ^ 3 + 7 * ((m : ℤ) + 5) ^ 2 - 13 * ((m : ℤ) + 5) + 39)
        * OMA.S_oeis_a213203.a (m + 3)
      - 2 * (((m : ℤ) + 5) - 2) * (4 * ((m : ℤ) + 5) ^ 2 - 2 * ((m : ℤ) + 5) - 15)
        * OMA.S_oeis_a213203.a (m + 2)
      + 20 * (((m : ℤ) + 5) - 2) * (((m : ℤ) + 5) - 3) * (((m : ℤ) + 5) - 4)
        * OMA.S_oeis_a213203.a (m + 1)) = 0 := by
    linear_combination c5
      + (-(((m : ℤ) + 5) ^ 2) - ((m : ℤ) + 5) - 11) * c4
      + (((m : ℤ) + 5) ^ 3 + 7 * ((m : ℤ) + 5) ^ 2 - 13 * ((m : ℤ) + 5) + 39) * c3
      - 2 * (((m : ℤ) + 5) - 2) * (4 * ((m : ℤ) + 5) ^ 2 - 2 * ((m : ℤ) + 5) - 15) * c2
      + 20 * (((m : ℤ) + 5) - 2) * (((m : ℤ) + 5) - 3) * (((m : ℤ) + 5) - 4) * c1
  linarith
