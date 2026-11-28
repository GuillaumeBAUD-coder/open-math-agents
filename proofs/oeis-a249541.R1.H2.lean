import OMAReductions.R_oeis_a249541_R1
import Mathlib

theorem OMA.solution : OMA.R_oeis_a249541_R1.H2 := by
  intro k _ _ _ _ hsq h
  rw [Nat.squarefree_iff_prime_squarefree] at hsq
  push_neg at hsq
  obtain ⟨p, hp, m, hm⟩ := hsq
  have h1 : k.totient = p * (p * m).totient := by
    rw [hm, mul_assoc, Nat.totient_mul_of_prime_of_dvd hp (dvd_mul_right p m)]
  have h2 : p ∣ k + 1 := ⟨3 * (p * m).totient, by rw [← h, h1]; ring⟩
  have h3 : p ∣ k := ⟨p * m, by rw [hm, mul_assoc]⟩
  have h4 : p ∣ 1 := (Nat.dvd_add_right h3).1 h2
  exact hp.one_lt.ne' (Nat.dvd_one.1 h4)
