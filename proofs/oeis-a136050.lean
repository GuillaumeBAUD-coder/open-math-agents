import OMAStatements.S_oeis_a136050
import Mathlib

theorem OMA.solution : type_of% @OMA.S_oeis_a136050.main := by
  intro p hp hp2 hp3
  have h5 : p % 6 = 5 := by
    have h2 : p ≠ 2 := by
      rintro rfl
      norm_num at hp2
    have hodd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left h2
    have h3 : p % 3 ≠ 0 := by
      intro h
      have h3p : 3 ∣ p := Nat.dvd_of_mod_eq_zero h
      have := (Nat.prime_dvd_prime_iff_eq (by norm_num) hp).mp h3p
      omega
    have h3' : (p + 2) % 3 ≠ 0 := by
      intro h
      have h3p : 3 ∣ p + 2 := Nat.dvd_of_mod_eq_zero h
      have := (Nat.prime_dvd_prime_iff_eq (by norm_num) hp2).mp h3p
      have := hp.two_le
      omega
    have h32 : p % 3 = 2 := by omega
    omega
  obtain ⟨k, rfl⟩ : ∃ k, p = 6 * k + 5 := ⟨p / 6, by omega⟩
  unfold OMA.S_oeis_a136050.term
  have hmod := Nat.modEq_nine_digits_sum ((6 * k + 5) * (6 * k + 5 + 2))
  have h8 : ((6 * k + 5) * (6 * k + 5 + 2)) % 9 = 8 := by
    have e : (6 * k + 5) * (6 * k + 5 + 2) = 9 * (4 * k * k + 8 * k + 3) + 8 := by ring
    omega
  unfold Nat.ModEq at hmod
  omega
