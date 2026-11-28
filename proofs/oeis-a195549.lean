import OMAStatements.S_oeis_a195549

/-! Credit: @unserus

The convergents are consecutive Fibonacci numbers, so u^2 + v^2 = F(2n+1) and, as u and v are
coprime, the gcd of the triple is gcd(2, F(2n+1)). Hence a(n) = F(2n+1)/gcd(2, F(2n+1)), which is
the reduced denominator; the recurrence follows from F(m+12) + F(m) = 18 F(m+6) and
F(m+6) = F(m) mod 2, and the generating function coefficientwise. -/

namespace OMAA195549Helpers
open OMA.S_oeis_a195549 PowerSeries

theorem conv_eq (n : ℕ) : convergent n = (Nat.fib (n + 1), Nat.fib n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [convergent, ih, Nat.fib_add_two, Prod.mk.injEq, and_true]
    exact add_comm _ _

theorem gcd_eq (u v : ℕ) (h : Nat.Coprime u v) (hvu : v ≤ u) :
    Nat.gcd (Nat.gcd (2 * (u * v)) (u ^ 2 + v ^ 2)) (u ^ 2 - v ^ 2) = Nat.gcd 2 (u ^ 2 + v ^ 2) := by
  have hc : Nat.Coprime (u * v) (u ^ 2 + v ^ 2) := by
    apply Nat.Coprime.mul_left
    · rw [show u ^ 2 + v ^ 2 = v ^ 2 + u * u by ring]
      exact (Nat.coprime_add_mul_right_right u (v ^ 2) u).mpr (h.pow_right 2)
    · rw [show u ^ 2 + v ^ 2 = u ^ 2 + v * v by ring]
      exact (Nat.coprime_add_mul_right_right v (u ^ 2) v).mpr (h.symm.pow_right 2)
  rw [Nat.Coprime.gcd_mul_right_cancel 2 hc]
  apply Nat.gcd_eq_left
  have h1 : Nat.gcd 2 (u ^ 2 + v ^ 2) ∣ u ^ 2 + v ^ 2 := Nat.gcd_dvd_right _ _
  have h2 : Nat.gcd 2 (u ^ 2 + v ^ 2) ∣ 2 * v ^ 2 := Dvd.dvd.mul_right (Nat.gcd_dvd_left _ _) _
  have hle : v ^ 2 ≤ u ^ 2 := Nat.pow_le_pow_left hvu 2
  have : u ^ 2 - v ^ 2 = (u ^ 2 + v ^ 2) - 2 * v ^ 2 := by
    generalize u ^ 2 = A at *
    generalize v ^ 2 = B at *
    omega
  rw [this]
  exact Nat.dvd_sub h1 h2

theorem a_eq (n : ℕ) (hn : 1 ≤ n) :
    a n = Nat.fib (2 * n + 1) / Nat.gcd 2 (Nat.fib (2 * n + 1)) := by
  simp only [a, if_neg (show n ≠ 0 by omega), conv_eq, hyp]
  rw [gcd_eq _ _ (Nat.fib_coprime_fib_succ n).symm (Nat.fib_mono (Nat.le_succ n)),
    Nat.fib_two_mul_add_one]

theorem fib_ge (n : ℕ) (hn : 1 ≤ n) : 2 ≤ Nat.fib (2 * n + 1) := by
  have := Nat.fib_mono (show 3 ≤ 2 * n + 1 by omega)
  have h3 : Nat.fib 3 = 2 := by decide
  omega

theorem den_eq (n : ℕ) (hn : 1 ≤ n) :
    (mkRat ((Nat.fib (2 * n + 1) : ℤ) - 2) (Nat.fib (2 * n + 1))).den =
      Nat.fib (2 * n + 1) / Nat.gcd 2 (Nat.fib (2 * n + 1)) := by
  have hs := fib_ge n hn
  generalize Nat.fib (2 * n + 1) = s at *
  rw [Rat.den_mkRat, if_neg (by omega)]
  congr 1
  have h1 : ((s : ℤ) - 2).natAbs = s - 2 := by omega
  rw [h1]
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 2 := ⟨s - 2, by omega⟩
  rw [show t + 2 - 2 = t by omega, Nat.gcd_comm (t + 2) t, Nat.gcd_self_add_right,
    Nat.gcd_add_self_right, Nat.gcd_comm]

theorem fib6 (k : ℕ) : Nat.fib (k + 6) = 5 * Nat.fib k + 8 * Nat.fib (k + 1) := by
  simp only [Nat.fib_add_two]; ring

theorem fib12 (k : ℕ) : Nat.fib (k + 12) = 89 * Nat.fib k + 144 * Nat.fib (k + 1) := by
  simp only [Nat.fib_add_two]; ring

theorem g6 (k : ℕ) : Nat.gcd 2 (Nat.fib (k + 6)) = Nat.gcd 2 (Nat.fib k) := by
  rw [fib6, show 5 * Nat.fib k + 8 * Nat.fib (k + 1) =
    Nat.fib k + (2 * Nat.fib k + 4 * Nat.fib (k + 1)) * 2 by ring, Nat.gcd_add_mul_right_right]

theorem rec (n : ℕ) (hn : 1 ≤ n) : a (n + 6) + a n = 18 * a (n + 3) := by
  rw [a_eq _ (by omega), a_eq _ hn, a_eq _ (by omega),
    show 2 * (n + 6) + 1 = (2 * n + 1) + 12 by ring, show 2 * (n + 3) + 1 = (2 * n + 1) + 6 by ring]
  have hg12 : Nat.gcd 2 (Nat.fib (2 * n + 1 + 12)) = Nat.gcd 2 (Nat.fib (2 * n + 1)) := by
    rw [show 2 * n + 1 + 12 = (2 * n + 1 + 6) + 6 by ring, g6, g6]
  rw [hg12, g6]
  generalize hm : 2 * n + 1 = m
  have hd : ∀ x, Nat.gcd 2 x ∣ x := fun x => Nat.gcd_dvd_right _ _
  have hdm := hd (Nat.fib m)
  have hd6 : Nat.gcd 2 (Nat.fib m) ∣ Nat.fib (m + 6) := by rw [← g6]; exact hd _
  have hd12 : Nat.gcd 2 (Nat.fib m) ∣ Nat.fib (m + 12) := by
    rw [← g6, ← g6, show m + 6 + 6 = m + 12 by ring]; exact hd _
  rw [← Nat.add_div_of_dvd_right hd12, ← Nat.mul_div_assoc _ hd6]
  congr 1
  rw [fib12, fib6]; ring

theorem small : a 0 = 0 ∧ a 1 = 1 ∧ a 2 = 5 ∧ a 3 = 13 ∧ a 4 = 17 ∧ a 5 = 89 ∧ a 6 = 233 := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [a_eq _ (by norm_num)] <;> decide

end OMAA195549Helpers

open OMAA195549Helpers OMA.S_oeis_a195549 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a195549.main := by
  refine ⟨fun n hn => rec n hn, ?_, fun n hn => by rw [a_eq n hn, den_eq n hn]⟩
  unfold generatingFunction
  have hL : (((1 - 3 * X + X ^ 2) * (1 + 3 * X + 8 * X ^ 2 + 3 * X ^ 3 + X ^ 4) : ℤ⟦X⟧) *
      mk (fun n => (a n : ℤ))) =
      X ^ 6 * mk (fun n => (a n : ℤ)) - C (18 : ℤ) * (X ^ 3 * mk (fun n => (a n : ℤ)))
        + mk (fun n => (a n : ℤ)) := by
    simp only [map_ofNat]; ring
  have hR : (X * (1 + 5 * X + 13 * X ^ 2 - X ^ 3 - X ^ 4 - X ^ 5) : ℤ⟦X⟧) =
      X ^ 1 + C (5 : ℤ) * X ^ 2 + C (13 : ℤ) * X ^ 3 - X ^ 4 - X ^ 5 - X ^ 6 := by
    simp only [map_ofNat]; ring
  rw [hL, hR]
  ext k
  simp only [map_add, map_sub, coeff_C_mul, coeff_X_pow_mul', coeff_mk, coeff_X_pow]
  rcases Nat.lt_or_ge k 7 with hk | hk
  · obtain ⟨s0, s1, s2, s3, s4, s5, s6⟩ := small
    interval_cases k <;> simp [s0, s1, s2, s3, s4, s5, s6]
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 7 := ⟨k - 7, by omega⟩
    rw [if_pos (by omega : 6 ≤ j + 7), if_pos (by omega : 3 ≤ j + 7),
      if_neg (by omega : ¬ j + 7 = 1), if_neg (by omega : ¬ j + 7 = 2),
      if_neg (by omega : ¬ j + 7 = 3), if_neg (by omega : ¬ j + 7 = 4),
      if_neg (by omega : ¬ j + 7 = 5), if_neg (by omega : ¬ j + 7 = 6),
      show j + 7 - 6 = j + 1 by omega, show j + 7 - 3 = j + 1 + 3 by omega,
      show j + 7 = j + 1 + 6 by omega]
    have h := rec (j + 1) (by omega)
    have h' : ((a (j + 1 + 6) : ℕ) : ℤ) + (a (j + 1) : ℤ) = 18 * (a (j + 1 + 3) : ℤ) := by
      exact_mod_cast h
    generalize ((a (j + 1 + 6) : ℕ) : ℤ) = x6 at *
    generalize ((a (j + 1 + 3) : ℕ) : ℤ) = x3 at *
    generalize ((a (j + 1) : ℕ) : ℤ) = x0 at *
    linear_combination h'
