import OMAStatements.S_oeis_a057300
import Mathlib

namespace A057300aux

open OMA.S_oeis_a057300 in
lemma a_eq (n : ℕ) : a n = 4 * a (n / 4) + swapDigit (n % 4) := by
  by_cases h : n = 0
  · subst h
    have h0 : a 0 = 0 := by
      rw [a]
      simp
    simp [h0, swapDigit]
  · conv_lhs => rw [a]
    rw [if_neg h]

open OMA.S_oeis_a057300 in
lemma a_four (q r : ℕ) (hr : r < 4) : a (4 * q + r) = 4 * a q + swapDigit r := by
  rw [a_eq (4 * q + r)]
  have h1 : (4 * q + r) / 4 = q := by omega
  have h2 : (4 * q + r) % 4 = r := by omega
  rw [h1, h2]

open OMA.S_oeis_a057300 in
lemma sw0 : swapDigit 0 = 0 := by decide
open OMA.S_oeis_a057300 in
lemma sw1 : swapDigit 1 = 2 := by decide
open OMA.S_oeis_a057300 in
lemma sw2 : swapDigit 2 = 1 := by decide
open OMA.S_oeis_a057300 in
lemma sw3 : swapDigit 3 = 3 := by decide

open OMA.S_oeis_a057300 in
lemma both (n : ℕ) : a (2 * n) + 2 * a n = 5 * n ∧ a (2 * n + 1) + 2 * a n = 5 * n + 2 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have a0 : a 0 = 0 := by
      have h := a_four 0 0 (by norm_num)
      rw [sw0] at h
      simp at h
      omega
    have a1 : a 1 = 2 := by
      have h := a_four 0 1 (by norm_num)
      rw [sw1, a0] at h
      simpa using h
    by_cases hn : n = 0
    · subst hn
      simp [a0, a1]
    · obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 4 ∧ n = 4 * q + r :=
        ⟨n / 4, n % 4, by omega, by omega⟩
      obtain ⟨ih1, ih2⟩ := ih q (by omega)
      have hr' : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
      rcases hr' with rfl | rfl | rfl | rfl
      · have e := a_four q 0 (by norm_num)
        have e2 := a_four (2 * q) 0 (by norm_num)
        have e3 := a_four (2 * q) 1 (by norm_num)
        rw [sw0] at e e2
        rw [sw1] at e3
        rw [show 2 * (4 * q + 0) = 4 * (2 * q) + 0 by ring,
          show 4 * (2 * q) + 0 + 1 = 4 * (2 * q) + 1 by ring]
        constructor <;> omega
      · have e := a_four q 1 (by norm_num)
        have e2 := a_four (2 * q) 2 (by norm_num)
        have e3 := a_four (2 * q) 3 (by norm_num)
        rw [sw1] at e
        rw [sw2] at e2
        rw [sw3] at e3
        rw [show 2 * (4 * q + 1) = 4 * (2 * q) + 2 by ring,
          show 4 * (2 * q) + 2 + 1 = 4 * (2 * q) + 3 by ring]
        constructor <;> omega
      · have e := a_four q 2 (by norm_num)
        have e2 := a_four (2 * q + 1) 0 (by norm_num)
        have e3 := a_four (2 * q + 1) 1 (by norm_num)
        rw [sw2] at e
        rw [sw0] at e2
        rw [sw1] at e3
        rw [show 2 * (4 * q + 2) = 4 * (2 * q + 1) + 0 by ring,
          show 4 * (2 * q + 1) + 0 + 1 = 4 * (2 * q + 1) + 1 by ring]
        constructor <;> omega
      · have e := a_four q 3 (by norm_num)
        have e2 := a_four (2 * q + 1) 2 (by norm_num)
        have e3 := a_four (2 * q + 1) 3 (by norm_num)
        rw [sw3] at e
        rw [sw2] at e2
        rw [sw3] at e3
        rw [show 2 * (4 * q + 3) = 4 * (2 * q + 1) + 2 by ring,
          show 4 * (2 * q + 1) + 2 + 1 = 4 * (2 * q + 1) + 3 by ring]
        constructor <;> omega

end A057300aux

theorem OMA.solution : type_of% @OMA.S_oeis_a057300.main := by
  intro n
  exact A057300aux.both n
