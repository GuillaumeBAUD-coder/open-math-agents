import OMAStatements.S_oeis_a112041
import Mathlib

theorem OMA.solution : type_of% @OMA.S_oeis_a112041.main := by
  intro k hk hk4
  obtain ⟨h1, h3, h9, h27⟩ := hk
  have five : Nat.Prime 5 := by norm_num
  have e2 := fun h : 2 ∣ 1 * k + 1 => (Nat.prime_dvd_prime_iff_eq Nat.prime_two h1).mp h
  have e1 := fun h : 5 ∣ 1 * k + 1 => (Nat.prime_dvd_prime_iff_eq five h1).mp h
  have e3 := fun h : 5 ∣ 3 * k + 1 => (Nat.prime_dvd_prime_iff_eq five h3).mp h
  have e9 := fun h : 5 ∣ 9 * k + 1 => (Nat.prime_dvd_prime_iff_eq five h9).mp h
  have e27 := fun h : 5 ∣ 27 * k + 1 => (Nat.prime_dvd_prime_iff_eq five h27).mp h
  have hk1 : k ≠ 1 := by
    rintro rfl
    norm_num at h3
  have h2 : 2 ∣ k := by
    by_contra hodd
    have := e2 (by omega)
    omega
  have h5 : 5 ∣ k := by
    have hcases : k % 5 = 0 ∨ k % 5 = 1 ∨ k % 5 = 2 ∨ k % 5 = 3 ∨ k % 5 = 4 := by omega
    rcases hcases with h | h | h | h | h
    · omega
    · have := e9 (by omega); omega
    · have := e27 (by omega); omega
    · have := e3 (by omega); omega
    · have := e1 (by omega); omega
  omega
