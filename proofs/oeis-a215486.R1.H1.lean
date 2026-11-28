import OMAReductions.R_oeis_a215486_R1
import Mathlib

theorem OMA.solution : OMA.R_oeis_a215486_R1.H1 := by
  intro n hn _ _ hsq h
  rw [Nat.squarefree_iff_prime_squarefree] at hsq
  push_neg at hsq
  obtain ⟨p, hp, hpp⟩ := hsq
  have h1 : (p * p).totient ∣ n.totient := Nat.totient_dvd_of_dvd hpp
  have h2 : p ∣ (p * p).totient := by
    rw [Nat.totient_mul_of_prime_of_dvd hp (dvd_refl p)]
    exact dvd_mul_right _ _
  have h3 : p ∣ n - 1 := (h2.trans h1).trans (Nat.dvd_of_mod_eq_zero h)
  have h4 : p ∣ n := (dvd_mul_right p p).trans hpp
  have h5 : p ∣ 1 := by
    have := (Nat.dvd_sub h4 h3)
    rwa [show n - (n - 1) = 1 by omega] at this
  exact hp.one_lt.ne' (Nat.dvd_one.mp h5)
