import OMAStatements.S_oeis_a098807
import Mathlib

namespace OMA.P_oeis_a098807

theorem prime_even_eq_two {q : ℕ} (hq : q.Prime) (h : q % 2 = 0) : q = 2 :=
  ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hq).1 (Nat.dvd_of_mod_eq_zero h)).symm

theorem prime_three_dvd {q : ℕ} (hq : q.Prime) (h : q % 3 = 0) : q = 3 :=
  ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hq).1 (Nat.dvd_of_mod_eq_zero h)).symm

theorem all_even (k : ℕ) (hk : k ∈ OMA.S_oeis_a098807.S) : Even k := by
  obtain ⟨hk1, p, hp, hm, hpl⟩ := hk
  have h2 := hm.two_le
  by_contra hodd
  rw [Nat.even_iff] at hodd
  by_cases hpe : p % 2 = 0
  · have := prime_even_eq_two hp hpe
    omega
  · have h3 := prime_even_eq_two hm (by omega)
    have h4 := prime_even_eq_two hpl (by omega)
    omega

theorem char_iff (k : ℕ) (hev : Even k) (h3 : ¬ 3 ∣ k) :
    k ∈ OMA.S_oeis_a098807.S ↔ (k + 3).Prime ∧ (2 * k + 3).Prime := by
  rw [Nat.even_iff] at hev
  rw [Nat.dvd_iff_mod_eq_zero] at h3
  constructor
  · rintro ⟨hk1, p, hp, hm, hpl⟩
    have h2 := hm.two_le
    have hp2 := hp.two_le
    have hcases : (p - k) % 3 = 0 ∨ p % 3 = 0 ∨ (p + k) % 3 = 0 := by
      obtain ⟨d, rfl⟩ : ∃ d, p = k + d := ⟨p - k, by omega⟩
      have e1 : k + d - k = d := by omega
      rw [e1]
      have hk3 : k % 3 = 1 ∨ k % 3 = 2 := by omega
      have hd3 : d % 3 = 0 ∨ d % 3 = 1 ∨ d % 3 = 2 := by omega
      rcases hk3 with a | a <;> rcases hd3 with b | b | b <;> omega
    rcases hcases with h | h | h
    · have e := prime_three_dvd hm h
      have e1 : p = k + 3 := by omega
      have e2 : p + k = 2 * k + 3 := by omega
      rw [← e1, ← e2]
      exact ⟨hp, hpl⟩
    · have e := prime_three_dvd hp h
      omega
    · have e := prime_three_dvd hpl h
      omega
  · rintro ⟨ha, hb⟩
    refine ⟨by omega, k + 3, ha, ?_, ?_⟩
    · have : k + 3 - k = 3 := by omega
      rw [this]
      exact Nat.prime_three
    · have : k + 3 + k = 2 * k + 3 := by omega
      rw [this]
      exact hb

end OMA.P_oeis_a098807

theorem OMA.solution : type_of% @OMA.S_oeis_a098807.main :=
  ⟨OMA.P_oeis_a098807.all_even, OMA.P_oeis_a098807.char_iff⟩
