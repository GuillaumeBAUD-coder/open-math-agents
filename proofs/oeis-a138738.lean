import OMAStatements.S_oeis_a138738
import Mathlib

/-!
# Proof of OEIS A138738 Conjecture

1. For `m' >= 2` and `n >= 1`, `6 ∣ E m' n` because every active term in `E m' n` has
   `m' <= k`, so `(m' + 1)!` divides `(k + 1)! / (k - m')!`, and `6 = 3! ∣ (m' + 1)!`.
2. For `m' = 1`: `E 1 1 = 0`, `E 1 2 = 2`, and by strong induction `6 ∣ E 1 n` for all `n >= 3`
   (at `k = 1`, `2 * n * E 1 (n - 1)` is divisible by `6`; at `k >= 2`, `6 ∣ E 2 (k - 1)`).
3. For `m' = 0`: splitting off `k = 0` in `E 0 (n + 1)` leaves `E 0 n` plus terms with
   `k >= 1`, each divisible by `6` (`E 1 1 = 0`, `(2 + 1) * E 1 2 = 6`, and `6 ∣ E 1 k` for `k >= 3`).
   By induction, `a(n) = E 0 n ≡ 1 [MOD 6]` for all `n`.
-/

namespace OeisA138738Proof

open Finset OMA.S_oeis_a138738

private lemma fact_dvd_fact_div {m' k : ℕ} (h : m' ≤ k) :
    (m' + 1).factorial ∣ (k + 1).factorial / (k - m').factorial := by
  have hch := Nat.choose_mul_factorial_mul_factorial (show m' + 1 ≤ k + 1 by omega)
  have hsub : k + 1 - (m' + 1) = k - m' := by omega
  rw [hsub] at hch
  have hdiv : (k + 1).factorial / (k - m').factorial =
      Nat.choose (k + 1) (m' + 1) * (m' + 1).factorial := by
    apply Nat.eq_of_mul_eq_mul_right (Nat.factorial_pos (k - m'))
    rw [Nat.div_mul_cancel (Nat.factorial_dvd_factorial (by omega))]
    exact hch.symm
  rw [hdiv]
  exact dvd_mul_left _ _

private lemma six_dvd_E_of_ge_two {m' n : ℕ} (hm : 2 ≤ m') (hn : 1 ≤ n) :
    6 ∣ E m' n := by
  rcases Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0) with ⟨n', rfl⟩
  rw [E]
  apply Finset.dvd_sum
  intro k _
  split_ifs with hle
  · have h6 : 6 ∣ (m' + 1).factorial :=
      dvd_trans (by decide : 6 ∣ (3 : ℕ).factorial) (Nat.factorial_dvd_factorial (by omega))
    have hd := dvd_trans h6 (fact_dvd_fact_div hle)
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hd _) _) _
  · exact dvd_zero 6

private lemma E_one_one : E 1 1 = 0 := by
  rw [E]; simp

private lemma E_one_two : E 1 2 = 2 := by
  rw [E]; simp [Fin.sum_univ_two, E]

private lemma six_dvd_E_one : ∀ n : ℕ, 3 ≤ n → 6 ∣ E 1 n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    rcases Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0) with ⟨m, rfl⟩
    rw [E]
    apply Finset.dvd_sum
    intro k _
    split_ifs with hle
    · by_cases hk1 : k.1 = 1
      · rw [hk1]
        simp only [Nat.choose_one_right, Nat.sub_self, Nat.factorial_zero, Nat.div_one]
        have h2f : (1 + 1).factorial = 2 := by decide
        rw [h2f]
        by_cases hm2 : m = 2
        · subst hm2; simp [E_one_one]
        · by_cases hm3 : m = 3
          · subst hm3; simp [E_one_two]; exact ⟨E 2 0 * 2, by ring⟩
          · have hih : 6 ∣ E 1 (m - 1) := ih (m - 1) (by omega) (by omega)
            exact dvd_mul_of_dvd_right hih _
      · have hk2 : 2 ≤ k.1 := by omega
        have hd : 6 ∣ E 2 (k.1 - 1) := six_dvd_E_of_ge_two (by omega) (by omega)
        exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hd _) _
    · exact dvd_zero 6

private lemma E_zero_mod_six (n : ℕ) : E 0 n ≡ 1 [MOD 6] := by
  induction n with
  | zero => simp [E, Nat.ModEq]
  | succ n ih =>
    rw [E, Fin.sum_univ_succ]
    have hfirst :
        (if 0 ≤ (0 : Fin (n + 1)).1 then
          Nat.choose n (0 : Fin (n + 1)).1 * (((0 : Fin (n + 1)).1 + 1).factorial / ((0 : Fin (n + 1)).1 - 0).factorial) *
            E (0 + 1) ((0 : Fin (n + 1)).1 - 0) * E 0 (n - (0 : Fin (n + 1)).1)
        else 0) = E 0 n := by
      simp [E]
    rw [hfirst]
    have hrest : 6 ∣ ∑ k : Fin n,
        if 0 ≤ k.succ.1 then
          Nat.choose n k.succ.1 * ((k.succ.1 + 1).factorial / (k.succ.1 - 0).factorial) *
            E (0 + 1) (k.succ.1 - 0) * E 0 (n - k.succ.1)
        else 0 := by
      apply Finset.dvd_sum
      intro k _
      simp only [Nat.zero_le, ↓reduceIte, Nat.sub_zero, zero_add]
      have hk1 : 1 ≤ k.succ.1 := by simp
      by_cases h1 : k.succ.1 = 1
      · rw [h1, E_one_one]; simp
      · by_cases h2 : k.succ.1 = 2
        · rw [h2, E_one_two]
          have h3 : (2 + 1).factorial / (2 : ℕ).factorial = 3 := by decide
          rw [h3]
          refine ⟨Nat.choose n 2 * E 0 (n - 2), ?_⟩
          ring
        · have hd : 6 ∣ E 1 k.succ.1 := six_dvd_E_one k.succ.1 (by omega)
          exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hd _) _
    have h0 : (∑ k : Fin n,
        if 0 ≤ k.succ.1 then
          Nat.choose n k.succ.1 * ((k.succ.1 + 1).factorial / (k.succ.1 - 0).factorial) *
            E (0 + 1) (k.succ.1 - 0) * E 0 (n - k.succ.1)
        else 0) ≡ 0 [MOD 6] :=
      Nat.modEq_zero_iff_dvd.mpr hrest
    simpa using ih.add h0

end OeisA138738Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a138738.main :=
  OeisA138738Proof.E_zero_mod_six
