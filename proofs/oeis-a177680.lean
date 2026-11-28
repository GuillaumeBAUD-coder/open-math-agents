import OMAStatements.S_oeis_a177680
import Mathlib

theorem OMA.solution : type_of% @OMA.S_oeis_a177680.main := by
  rintro n ⟨⟨p, hp, hp2, hpe⟩, ⟨q, hq, hq2, hqe⟩⟩ hn1
  by_contra h5
  have hmod : n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by omega
  rcases hmod with h | h | h | h
  · have h5p : 5 ∣ p := by omega
    have := (Nat.prime_dvd_prime_iff_eq (by norm_num) hp).mp h5p
    omega
  · have h5p : 5 ∣ q + 2 := by omega
    have := (Nat.prime_dvd_prime_iff_eq (by norm_num) hq2).mp h5p
    omega
  · have h5p : 5 ∣ q := by omega
    have := (Nat.prime_dvd_prime_iff_eq (by norm_num) hq).mp h5p
    omega
  · have h5p : 5 ∣ p + 2 := by omega
    have := (Nat.prime_dvd_prime_iff_eq (by norm_num) hp2).mp h5p
    omega
