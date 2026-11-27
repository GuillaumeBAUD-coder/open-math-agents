import OMAStatements.S_oeis_a088982
import Mathlib

/-!
# Proof of OEIS-A088982 conjecture


-/

open OMA.S_oeis_a088982

private theorem prime_isPrime (k : ℕ) : Nat.Prime (prime k) :=
  Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime (k - 1)

private theorem prime_lt {a b : ℕ} (ha : 0 < a) (hab : a < b) : prime a < prime b := by
  unfold prime
  exact Nat.nth_strictMono Nat.infinite_setOfPred_prime (show a - 1 < b - 1 by omega)

theorem OMA.solution : type_of% @OMA.S_oeis_a088982.main := by
  intro x hx
  have hxPrime : 2 < prime x := by
    simpa [prime] using (prime_lt (a := 1) (by decide) hx)
  have hnext : prime x < prime (x + 1) := prime_lt (by omega) (by omega)
  have hxOdd := (prime_isPrime x).eq_two_or_odd.resolve_left (by omega)
  have hnextOdd := (prime_isPrime (x + 1)).eq_two_or_odd.resolve_left (by omega)
  have hgap : prime x + 1 < prime (x + 1) := by omega
  refine ⟨prime (prime x + 1), prime_isPrime _, ?_, ?_⟩
  · exact prime_lt (by omega) (Nat.lt_succ_self _)
  · exact prime_lt (by omega) hgap
