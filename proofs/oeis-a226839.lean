import OMAStatements.S_oeis_a226839
import Mathlib

/-!
# Proof of OEIS A226839 Conjecture

For `m >= 2`, `T_m = m * (m + 1) / 2` satisfies `3 ∣ (T_m)! / m!`:
- For `m = 2`, `T_2 = 3` and `3! / 2! = 3`.
- For `m >= 3`, `m + 3 <= T_m`, so `(m + 1) * (m + 2) * (m + 3)` divides `(T_m)! / m!`,
  and one of three consecutive integers is divisible by `3`.
Hence in the recurrence for `a(n + 1)`, every term with `m >= 2` is divisible by `3`,
leaving only the `m = 1` term `a(n)`. By induction, `a(n) ≡ 1 [MOD 3]` for all `n`.
-/

namespace OeisA226839Proof

open OMA.S_oeis_a226839

private lemma three_dvd_three_consec (m : ℕ) :
    3 ∣ (m + 3) * (m + 2) * (m + 1) := by
  have h : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by omega
  rcases h with h0 | h1 | h2
  · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left ⟨m / 3 + 1, by omega⟩ _) _
  · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right ⟨m / 3 + 1, by omega⟩ _) _
  · exact dvd_mul_of_dvd_right ⟨m / 3 + 1, by omega⟩ _

private lemma three_dvd_tri_fact_div (m : ℕ) (hm : 2 ≤ m) :
    3 ∣ (tri m).factorial / m.factorial := by
  by_cases hm2 : m = 2
  · subst hm2
    decide
  · have hm3 : 3 ≤ m := by omega
    have htri : m + 3 ≤ tri m := by
      unfold tri
      have hsq : 2 * (m + 3) ≤ m * (m + 1) := by nlinarith
      omega
    have hd1 : (m + 3).factorial ∣ (tri m).factorial := Nat.factorial_dvd_factorial htri
    have hd2 : m.factorial ∣ (tri m).factorial := Nat.factorial_dvd_factorial (by omega)
    obtain ⟨q, hq⟩ := hd1
    have hdiv : (tri m).factorial / m.factorial = (m + 3) * (m + 2) * (m + 1) * q := by
      apply Nat.eq_of_mul_eq_mul_right (Nat.factorial_pos m)
      rw [Nat.div_mul_cancel hd2, hq]
      simp only [Nat.factorial_succ]
      ring
    rw [hdiv]
    exact dvd_mul_of_dvd_left (three_dvd_three_consec m) q

private lemma a_mod_three (n : ℕ) : a n ≡ 1 [MOD 3] := by
  induction n with
  | zero => simp [a, Nat.ModEq]
  | succ n ih =>
    rw [a, Fin.sum_univ_succ]
    have htri1 : tri 1 = 1 := rfl
    simp only [Fin.val_zero, zero_add, htri1, Nat.le_add_left, ↓reduceIte,
      Nat.factorial_one, Nat.div_one, Nat.sub_self, Nat.choose_zero_right, mul_one,
      Nat.add_sub_cancel]
    have hsum : 3 ∣ ∑ i : Fin n,
        if tri (i.succ.1 + 1) ≤ n + 1 then
          ((tri (i.succ.1 + 1)).factorial / (i.succ.1 + 1).factorial) *
            Nat.choose n (tri (i.succ.1 + 1) - 1) * a (n + 1 - tri (i.succ.1 + 1))
        else 0 := by
      apply Finset.dvd_sum
      intro i _
      split_ifs
      · have hm : 2 ≤ i.succ.1 + 1 := by simp
        exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (three_dvd_tri_fact_div _ hm) _) _
      · exact dvd_zero 3
    have h0 : (∑ i : Fin n,
        if tri (i.succ.1 + 1) ≤ n + 1 then
          ((tri (i.succ.1 + 1)).factorial / (i.succ.1 + 1).factorial) *
            Nat.choose n (tri (i.succ.1 + 1) - 1) * a (n + 1 - tri (i.succ.1 + 1))
        else 0) ≡ 0 [MOD 3] :=
      Nat.modEq_zero_iff_dvd.mpr hsum
    simpa using ih.add h0

end OeisA226839Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a226839.main :=
  OeisA226839Proof.a_mod_three
