import OMAStatements.S_oeis_a268553
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

namespace OMA.P_oeis_a268553

open OMA.S_oeis_a268553

private lemma diagFactor_eq (n : ℕ) :
    diagFactor n = (3 * n).factorial / (n.factorial ^ 3) := by
  unfold diagFactor
  rw [Finset.sum_eq_single n]
  · rw [Finset.sum_eq_single n]
    · rw [Finset.sum_eq_single n]
      · rw [if_pos (by omega)]
        congr 1
        · congr 1; omega
        · ring
      · intro c _ hc; rw [if_neg (by omega)]
      · intro hn; exact absurd (Finset.mem_range.mpr (by omega)) hn
    · intro b _ hb
      apply Finset.sum_eq_zero; intro c _; rw [if_neg (by omega)]
    · intro hn; exact absurd (Finset.mem_range.mpr (by omega)) hn
  · intro a _ ha
    apply Finset.sum_eq_zero; intro b _
    apply Finset.sum_eq_zero; intro c _; rw [if_neg (by omega)]
  · intro hn; exact absurd (Finset.mem_range.mpr (by omega)) hn

private lemma fac_cube_dvd_three_mul (n : ℕ) :
    n.factorial ^ 3 ∣ (3 * n).factorial := by
  have h1 : n.factorial * (2 * n).factorial ∣ (3 * n).factorial := by
    refine ⟨Nat.choose (3 * n) n, ?_⟩
    have hc := Nat.choose_mul_factorial_mul_factorial (by omega : n ≤ 3 * n)
    rw [show 3 * n - n = 2 * n by omega] at hc
    linarith
  have h2 : n.factorial * n.factorial ∣ (2 * n).factorial := by
    refine ⟨Nat.choose (2 * n) n, ?_⟩
    have hc := Nat.choose_mul_factorial_mul_factorial (by omega : n ≤ 2 * n)
    rw [show 2 * n - n = n by omega] at hc
    linarith
  have h3 : n.factorial * (n.factorial * n.factorial) ∣ n.factorial * (2 * n).factorial :=
    mul_dvd_mul_left _ h2
  rw [show n.factorial ^ 3 = n.factorial * (n.factorial * n.factorial) by ring]
  exact dvd_trans h3 h1

private lemma diagFactor_step (m : ℕ) :
    (m + 1) ^ 2 * diagFactor (m + 1) = 3 * (3 * m + 2) * (3 * m + 1) * diagFactor m := by
  rw [diagFactor_eq, diagFactor_eq]
  have hd1 := fac_cube_dvd_three_mul (m + 1)
  have hd0 := fac_cube_dvd_three_mul m
  have hpos : 0 < (m + 1).factorial ^ 3 := pow_pos (Nat.factorial_pos _) 3
  apply Nat.eq_of_mul_eq_mul_right hpos
  have hl : (m + 1) ^ 2 * ((3 * (m + 1)).factorial / (m + 1).factorial ^ 3) * (m + 1).factorial ^ 3 =
      (m + 1) ^ 2 * (3 * (m + 1)).factorial := by
    rw [mul_assoc, Nat.div_mul_cancel hd1]
  have hfac3 : (3 * (m + 1)).factorial = (3 * m + 3) * (3 * m + 2) * (3 * m + 1) * (3 * m).factorial := by
    rw [show 3 * (m + 1) = (3 * m + 2) + 1 by omega, Nat.factorial_succ,
        Nat.factorial_succ, Nat.factorial_succ]
    ring
  have hfacm : (m + 1).factorial ^ 3 = (m + 1) ^ 3 * m.factorial ^ 3 := by
    rw [Nat.factorial_succ, mul_pow]
  rw [hl, hfac3, hfacm]
  have hr : 3 * (3 * m + 2) * (3 * m + 1) * ((3 * m).factorial / m.factorial ^ 3) * ((m + 1) ^ 3 * m.factorial ^ 3) =
      3 * (3 * m + 2) * (3 * m + 1) * (m + 1) ^ 3 * (3 * m).factorial := by
    calc 3 * (3 * m + 2) * (3 * m + 1) * ((3 * m).factorial / m.factorial ^ 3) * ((m + 1) ^ 3 * m.factorial ^ 3)
        = 3 * (3 * m + 2) * (3 * m + 1) * (m + 1) ^ 3 * (((3 * m).factorial / m.factorial ^ 3) * m.factorial ^ 3) := by ring
      _ = 3 * (3 * m + 2) * (3 * m + 1) * (m + 1) ^ 3 * (3 * m).factorial := by rw [Nat.div_mul_cancel hd0]
  rw [hr]
  ring

private lemma prove_main :
    ∀ n : ℕ, 1 ≤ n → n ^ 4 * a268553 n = 9 * (3 * n - 1) ^ 2 * (3 * n - 2) ^ 2 * a268553 (n - 1) := by
  intro n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  rw [show m + 1 - 1 = m by omega, show 3 * (m + 1) - 1 = 3 * m + 2 by omega,
      show 3 * (m + 1) - 2 = 3 * m + 1 by omega]
  unfold a268553
  have h := diagFactor_step m
  calc (m + 1) ^ 4 * (diagFactor (m + 1) * diagFactor (m + 1))
      = ((m + 1) ^ 2 * diagFactor (m + 1)) * ((m + 1) ^ 2 * diagFactor (m + 1)) := by ring
    _ = (3 * (3 * m + 2) * (3 * m + 1) * diagFactor m) * (3 * (3 * m + 2) * (3 * m + 1) * diagFactor m) := by rw [h]
    _ = 9 * (3 * m + 2) ^ 2 * (3 * m + 1) ^ 2 * (diagFactor m * diagFactor m) := by ring

end OMA.P_oeis_a268553

theorem OMA.solution : type_of% @OMA.S_oeis_a268553.main :=
  OMA.P_oeis_a268553.prove_main
