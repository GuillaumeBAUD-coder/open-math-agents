import OMAStatements.S_oeis_a088982
import Mathlib

open Nat

theorem OMA.solution : type_of% @OMA.S_oeis_a088982.main := by
  intro x hx
  have hsm : StrictMono (nth Nat.Prime) := nth_strictMono infinite_setOf_prime
  set a := nth Nat.Prime (x - 1) with ha
  set b := nth Nat.Prime x with hb
  have hpa : a.Prime := prime_nth_prime _
  have hpb : b.Prime := prime_nth_prime _
  have hab : a < b := hsm (by omega)
  have ha2 : 2 < a := by
    have : nth Nat.Prime 0 < a := hsm (by omega)
    rwa [nth_prime_zero_eq_two] at this
  have hb2 : b ≠ 2 := by omega
  have hoa : Odd a := hpa.odd_of_ne_two (by omega)
  have hob : Odd b := hpb.odd_of_ne_two hb2
  have hab2 : a + 2 ≤ b := by
    obtain ⟨i, hi⟩ := hoa
    obtain ⟨j, hj⟩ := hob
    omega
  refine ⟨nth Nat.Prime a, prime_nth_prime _, ?_, ?_⟩
  · show nth Nat.Prime (a - 1) < nth Nat.Prime a
    exact hsm (by omega)
  · show nth Nat.Prime a < nth Nat.Prime (b - 1)
    exact hsm (by omega)
