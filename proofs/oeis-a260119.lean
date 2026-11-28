import OMAStatements.S_oeis_a260119
import Mathlib

/-!
# A260119: a(n) is odd for every n >= 1

For n >= 1 the set of positive k with gcd(2^n - 1, k^n - 1) = 1 is nonempty, since k = 2^n - 1
works: any common divisor of m = 2^n - 1 and m^n - 1 also divides m^n, hence divides 1. So a(n)
is the least element of this set. If a(n) were even, a(n) = 2j with j > 0, then
(2j)^n - 1 = (j^n - 1) + j^n (2^n - 1), so gcd(2^n - 1, j^n - 1) = gcd(2^n - 1, (2j)^n - 1) = 1.
Then j is a smaller member of the set, which contradicts minimality.
-/

namespace OMA.P260119

open OMA.S_oeis_a260119

theorem mem_set (n : ℕ) (hn : 1 ≤ n) :
    (2 ^ n - 1) ∈ {k : ℕ | 0 < k ∧ Nat.Coprime (2 ^ n - 1) (k ^ n - 1)} := by
  have h2 : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  refine ⟨by omega, ?_⟩
  set m := 2 ^ n - 1 with hm
  have hm1 : 1 ≤ m := by omega
  have hmn : 1 ≤ m ^ n := Nat.one_le_pow _ _ hm1
  have hdvd : m ∣ m ^ n := dvd_pow_self m (by omega)
  obtain ⟨c, hc⟩ := hdvd
  have : m ^ n - 1 + 1 = m ^ n := by omega
  rw [Nat.Coprime, Nat.gcd_comm]
  apply Nat.dvd_one.mp
  have g1 : Nat.gcd (m ^ n - 1) m ∣ m ^ n - 1 := Nat.gcd_dvd_left _ _
  have g2 : Nat.gcd (m ^ n - 1) m ∣ m ^ n := (Nat.gcd_dvd_right _ _).trans ⟨c, hc⟩
  have := (Nat.dvd_sub g2 g1)
  have e : m ^ n - (m ^ n - 1) = 1 := by omega
  rwa [e] at this

theorem halve (n j : ℕ) (hj : 0 < j)
    (h : Nat.Coprime (2 ^ n - 1) ((2 * j) ^ n - 1)) :
    Nat.Coprime (2 ^ n - 1) (j ^ n - 1) := by
  have h1 : 1 ≤ j ^ n := Nat.one_le_pow _ _ hj
  have h2 : 1 ≤ 2 ^ n := Nat.one_le_pow _ _ (by norm_num)
  have e : (2 * j) ^ n - 1 = (j ^ n - 1) + j ^ n * (2 ^ n - 1) := by
    rw [mul_pow, Nat.mul_sub, mul_one]
    have : j ^ n ≤ j ^ n * 2 ^ n := Nat.le_mul_of_pos_right _ (by omega)
    rw [mul_comm (2 ^ n)]
    omega
  rw [e] at h
  exact (Nat.coprime_add_mul_right_right _ _ _).mp h

end OMA.P260119

open OMA.P260119 in
theorem OMA.solution : type_of% @OMA.S_oeis_a260119.main := by
  intro n hn
  set S := {k : ℕ | 0 < k ∧ Nat.Coprime (2 ^ n - 1) (k ^ n - 1)} with hS
  have hne : S.Nonempty := ⟨_, mem_set n hn⟩
  have hmem : OMA.S_oeis_a260119.a n ∈ S := Nat.sInf_mem hne
  rcases Nat.even_or_odd (OMA.S_oeis_a260119.a n) with ⟨j, hj⟩ | ho
  · exfalso
    have hpos := hmem.1
    have hj0 : 0 < j := by omega
    have hjS : j ∈ S := by
      refine ⟨hj0, halve n j hj0 ?_⟩
      have := hmem.2
      rwa [hj, ← two_mul] at this
    have := Nat.sInf_le hjS
    change OMA.S_oeis_a260119.a n ≤ j at this
    omega
  · exact ho
