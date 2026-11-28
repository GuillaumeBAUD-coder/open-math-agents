import OMAStatements.S_oeis_a113610
import Mathlib

-- The statement, read literally, fails at n = 12: prime(12..15) = 37, 41, 43, 47, so a(12) = 11+12+4 = 27,
-- a(13) = 6 (only 42) and a(14) = 8+9+10 = 27 give a strict local minimum at a(13), but
-- prime(13) = 41 is not prime(12) + 2 = 39.

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a113610.main) := by
  intro h
  have p12 : OMA.S_oeis_a113610.prime 12 = 37 := by
    unfold OMA.S_oeis_a113610.prime
    rw [show (12 - 1 : ℕ) = Nat.count Nat.Prime 37 by decide +kernel]
    exact Nat.nth_count (by norm_num)
  have p13 : OMA.S_oeis_a113610.prime 13 = 41 := by
    unfold OMA.S_oeis_a113610.prime
    rw [show (13 - 1 : ℕ) = Nat.count Nat.Prime 41 by decide +kernel]
    exact Nat.nth_count (by norm_num)
  have p14 : OMA.S_oeis_a113610.prime 14 = 43 := by
    unfold OMA.S_oeis_a113610.prime
    rw [show (14 - 1 : ℕ) = Nat.count Nat.Prime 43 by decide +kernel]
    exact Nat.nth_count (by norm_num)
  have p15 : OMA.S_oeis_a113610.prime 15 = 47 := by
    unfold OMA.S_oeis_a113610.prime
    rw [show (15 - 1 : ℕ) = Nat.count Nat.Prime 47 by decide +kernel]
    exact Nat.nth_count (by norm_num)
  have a12 : OMA.S_oeis_a113610.a 12 = 27 := by
    unfold OMA.S_oeis_a113610.a
    rw [p12, show OMA.S_oeis_a113610.prime (12 + 1) = 41 from p13]
    decide +kernel
  have a13 : OMA.S_oeis_a113610.a 13 = 6 := by
    unfold OMA.S_oeis_a113610.a
    rw [p13, show OMA.S_oeis_a113610.prime (13 + 1) = 43 from p14]
    decide +kernel
  have a14 : OMA.S_oeis_a113610.a 14 = 27 := by
    unfold OMA.S_oeis_a113610.a
    rw [p14, show OMA.S_oeis_a113610.prime (14 + 1) = 47 from p15]
    decide +kernel
  have h1 : OMA.S_oeis_a113610.a 13 < OMA.S_oeis_a113610.a 12 := by
    rw [a13, a12]
    norm_num
  have h2 : OMA.S_oeis_a113610.a 13 < OMA.S_oeis_a113610.a 14 := by
    rw [a13, a14]
    norm_num
  have h3 : OMA.S_oeis_a113610.prime 13 = OMA.S_oeis_a113610.prime 12 + 2 :=
    h 12 (by norm_num) h1 h2
  rw [p13, p12] at h3
  norm_num at h3
