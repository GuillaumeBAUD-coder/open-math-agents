import OMAStatements.S_oeis_a067745
import Mathlib

/-!
# A067745: the numerator is the odd part of 3n − 2

Write 3n − 2 = 2^v·o with o odd. Since 2^v ≤ 3n − 2 ≤ 4^(n−1), we have v ≤ 2(n−1), so the fraction
equals o / (n^(2n−1)(2n−1)·2^(2(n−1)−v)). This is in lowest terms: gcd(o, n) divides
3n − (3n − 2) = 2 and o is odd; gcd(o, 2n − 1) divides 3(2n − 1) − 2(3n − 2) = 1; and o is coprime
to 2. (This is the argument recorded in the entry.)
-/

namespace PA067745

theorem le_four_pow (n : ℕ) (hn : 1 ≤ n) : 3 * n - 2 ≤ 4 ^ (n - 1) := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    rw [show n + 1 - 1 = (n - 1) + 1 by omega, pow_succ]
    have : 1 ≤ 4 ^ (n - 1) := Nat.one_le_pow _ _ (by norm_num)
    omega

end PA067745

theorem OMA.solution : type_of% @OMA.S_oeis_a067745.main := by
  intro n hn
  set N := 3 * n - 2 with hN
  have hN0 : N ≠ 0 := by omega
  set v := N.factorization 2 with hv
  set o := N / 2 ^ v with ho
  have hvo : 2 ^ v * o = N := Nat.ordProj_mul_ordCompl_eq_self N 2
  have hodd : ¬ 2 ∣ o := Nat.not_dvd_ordCompl Nat.prime_two hN0
  have hvle : v ≤ 2 * (n - 1) := by
    have h1 : 2 ^ v ≤ N := Nat.le_of_dvd (by omega) (Dvd.intro o hvo)
    have h2 : N ≤ 2 ^ (2 * (n - 1)) := by
      rw [pow_mul]; norm_num; exact PA067745.le_four_pow n hn
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp (h1.trans h2)
  set w := 2 * (n - 1) - v with hw
  set E := n ^ (2 * n - 1) * (2 * n - 1) * 2 ^ w with hE
  have hEpos : 0 < E := by
    have : 0 < 2 * n - 1 := by omega
    positivity
  have hfrac : (3 * (n : ℚ) - 2) / ((n : ℚ) ^ (2 * n - 1) * (2 * (n : ℚ) - 1) * 4 ^ (n - 1)) =
      ((o : ℤ) : ℚ) / ((E : ℤ) : ℚ) := by
    have e1 : (3 * (n : ℚ) - 2) = (2 : ℚ) ^ v * o := by
      have : ((N : ℕ) : ℚ) = (2 : ℚ) ^ v * o := by exact_mod_cast hvo.symm
      rw [← this, hN]; push_cast [Nat.cast_sub (show 2 ≤ 3 * n by omega)]; ring
    have e2 : (4 : ℚ) ^ (n - 1) = (2 : ℚ) ^ v * 2 ^ w := by
      rw [← pow_add, show v + w = 2 * (n - 1) by omega, pow_mul]; norm_num
    have e3 : (2 * (n : ℚ) - 1) = ((2 * n - 1 : ℕ) : ℚ) := by
      push_cast [Nat.cast_sub (show 1 ≤ 2 * n by omega)]; ring
    have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    have h2n : ((2 * n - 1 : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (show 2 * n - 1 ≠ 0 by omega)
    rw [e1, e2, e3, hE]
    push_cast
    field_simp
  have hcop : Nat.Coprime ((o : ℤ).natAbs) ((E : ℤ).natAbs) := by
    rw [Int.natAbs_natCast, Int.natAbs_natCast, hE]
    have hon : Nat.Coprime o n := by
      have hg : Nat.gcd o n ∣ 2 := by
        have h1 : Nat.gcd o n ∣ N := (Nat.gcd_dvd_left o n).trans (Dvd.intro_left _ hvo)
        have h2 : Nat.gcd o n ∣ 3 * n := Dvd.dvd.mul_left (Nat.gcd_dvd_right o n) 3
        have := Nat.dvd_sub h2 h1
        rwa [show 3 * n - N = 2 by omega] at this
      rcases (Nat.dvd_prime Nat.prime_two).mp hg with h | h
      · exact h
      · exfalso; exact hodd (h ▸ Nat.gcd_dvd_left o n)
    have ho2 : Nat.Coprime o (2 * n - 1) := by
      have hg : Nat.gcd o (2 * n - 1) ∣ 1 := by
        have h1 : Nat.gcd o (2 * n - 1) ∣ 2 * N := Dvd.dvd.mul_left
          ((Nat.gcd_dvd_left o _).trans (Dvd.intro_left _ hvo)) 2
        have h2 : Nat.gcd o (2 * n - 1) ∣ 3 * (2 * n - 1) :=
          Dvd.dvd.mul_left (Nat.gcd_dvd_right o _) 3
        have := Nat.dvd_sub h2 h1
        rwa [show 3 * (2 * n - 1) - 2 * N = 1 by omega] at this
      exact Nat.eq_one_of_dvd_one hg
    have hotwo : Nat.Coprime o 2 := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd |>.symm
    exact Nat.Coprime.mul_right (Nat.Coprime.mul_right (hon.pow_right _) ho2) (hotwo.pow_right _)
  unfold OMA.S_oeis_a067745.a OMA.S_oeis_a067745.oddPart
  rw [hfrac, Rat.num_div_eq_of_coprime (by exact_mod_cast hEpos) hcop]
