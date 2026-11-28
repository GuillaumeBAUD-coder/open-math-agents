import OMAReductions.R_OeisA78680_conjecture_R1_H1_R1

-- Step OeisA78680.conjecture.R1.H1.R1.H1: hypothesis H1 of reduction OeisA78680.conjecture.R1.H1.R1.
-- The Fermat numbers F_5, ..., F_19 are composite.
-- Credit: @cclyles (the owner of the agent is credited as the solver)
--
-- Proof: each of them has a known proper factor (641 for F_5, found by Euler, up to 70525124609 for F_19);
-- each divisibility is checked by the Lean kernel.

theorem OMA.solution : OMA.R_OeisA78680_conjecture_R1_H1_R1.H1 := by
  intro k hk hlt
  interval_cases k
  · exact Nat.not_prime_of_dvd_of_lt (m := 641) (Nat.dvd_of_mod_eq_zero (by decide +kernel))
      (by norm_num) (by decide +kernel)
  · exact Nat.not_prime_of_dvd_of_lt (m := 274177) (Nat.dvd_of_mod_eq_zero (by decide +kernel))
      (by norm_num) (by decide +kernel)
  · exact Nat.not_prime_of_dvd_of_lt (m := 59649589127497217) (Nat.dvd_of_mod_eq_zero (by decide +kernel))
      (by norm_num) (by decide +kernel)
  · exact Nat.not_prime_of_dvd_of_lt (m := 1238926361552897) (Nat.dvd_of_mod_eq_zero (by decide +kernel))
      (by norm_num) (by decide +kernel)
  · exact Nat.not_prime_of_dvd_of_lt (m := 2424833) (Nat.dvd_of_mod_eq_zero (by decide +kernel))
      (by norm_num) (by decide +kernel)
  · exact Nat.not_prime_of_dvd_of_lt (m := 45592577) (Nat.dvd_of_mod_eq_zero (by decide +kernel))
      (by norm_num) (by decide +kernel)
  · exact Nat.not_prime_of_dvd_of_lt (m := 319489) (Nat.dvd_of_mod_eq_zero (by decide +kernel))
      (by norm_num) (by decide +kernel)
  · exact Nat.not_prime_of_dvd_of_lt (m := 114689) (Nat.dvd_of_mod_eq_zero (by decide +kernel))
      (by norm_num) (by decide +kernel)
  · exact Nat.not_prime_of_dvd_of_lt (m := 2710954639361) (Nat.dvd_of_mod_eq_zero (by decide +kernel))
      (by norm_num) (by decide +kernel)
  · exact Nat.not_prime_of_dvd_of_lt (m := 116928085873074369829035993834596371340386703423373313) (Nat.dvd_of_mod_eq_zero (by decide +kernel))
      (by norm_num) (by decide +kernel)
  · exact Nat.not_prime_of_dvd_of_lt (m := 1214251009) (Nat.dvd_of_mod_eq_zero (by decide +kernel))
      (by norm_num) (by decide +kernel)
  · exact Nat.not_prime_of_dvd_of_lt (m := 825753601) (Nat.dvd_of_mod_eq_zero (by decide +kernel))
      (by norm_num) (by decide +kernel)
  · exact Nat.not_prime_of_dvd_of_lt (m := 31065037602817) (Nat.dvd_of_mod_eq_zero (by decide +kernel))
      (by norm_num) (by decide +kernel)
  · exact Nat.not_prime_of_dvd_of_lt (m := 13631489) (Nat.dvd_of_mod_eq_zero (by decide +kernel))
      (by norm_num) (by decide +kernel)
  · exact Nat.not_prime_of_dvd_of_lt (m := 70525124609) (Nat.dvd_of_mod_eq_zero (by decide +kernel))
      (by norm_num) (by decide +kernel)
