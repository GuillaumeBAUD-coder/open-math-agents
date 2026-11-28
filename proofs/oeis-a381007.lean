import OMAStatements.S_oeis_a381007
import Mathlib

open OMA.S_oeis_a381007

theorem OMA.solution : type_of% @OMA.S_oeis_a381007.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨y, hy⟩ : ∃ y, y = 2 ^ (2 * m) := ⟨_, rfl⟩
  obtain ⟨z, hz⟩ : ∃ z, z = 2 ^ (4 * m) := ⟨_, rfl⟩
  have e1 : 2 ^ (4 * (m + 1)) = 16 * z := by rw [hz]; ring
  have e2 : 2 ^ (4 * (m + 1) - 2) = 4 * z := by
    rw [show 4 * (m + 1) - 2 = 4 * m + 2 by omega, hz]; ring
  have e3 : 2 ^ (2 * (m + 1)) = 4 * y := by rw [hy]; ring
  have ypos : 1 ≤ y := by rw [hy]; exact Nat.one_le_two_pow
  have hyz : y ≤ z := by
    rw [hy, hz]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hB : legB (m + 1) = 16 * z - 4 * z - 4 * y - 1 := by
    unfold legB; rw [e1, e2, e3]
  have hC : hyp (m + 1) = 16 * z + 4 * z + 4 * y + 1 := by
    unfold hyp; rw [e1, e2, e3]
  have hsum : legB (m + 1) + hyp (m + 1) = 32 * z := by
    rw [hB, hC]; omega
  have hdB : Nat.gcd (Nat.gcd (legA (m + 1)) (legB (m + 1))) (hyp (m + 1)) ∣ legB (m + 1) :=
    Nat.dvd_trans (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right _ _)
  have hdC : Nat.gcd (Nat.gcd (legA (m + 1)) (legB (m + 1))) (hyp (m + 1)) ∣ hyp (m + 1) :=
    Nat.gcd_dvd_right _ _
  have hd : Nat.gcd (Nat.gcd (legA (m + 1)) (legB (m + 1))) (hyp (m + 1)) ∣ 2 ^ (4 * m + 5) := by
    have h := Nat.dvd_add hdB hdC
    rw [hsum] at h
    rwa [show 2 ^ (4 * m + 5) = 32 * z by rw [hz]; ring]
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · simpa using hk
  · exfalso
    have h2 : 2 ∣ Nat.gcd (Nat.gcd (legA (m + 1)) (legB (m + 1))) (hyp (m + 1)) := by
      rw [hk]; exact dvd_pow_self 2 (by omega)
    have h3 := Nat.dvd_trans h2 hdC
    rw [hC] at h3
    omega
