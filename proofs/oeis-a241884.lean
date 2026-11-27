import OMAStatements.S_oeis_a241884
import Mathlib

/-!
# OEIS A241884: Librandi's conjecture is false at `n = 56`

`n` is a term when `n - t ^ 2` is not prime for every divisor `t` of `n`. The conjecture says
that `n` is a term exactly when `n - 1` is not prime.

Counterexample: `n = 56`. Here `n - 1 = 55 = 5 * 11` is not prime, so the conjecture predicts
that `56` is a term. But `t = 7` divides `56` and `56 - 7 ^ 2 = 7` is prime.

(More generally `n = t (t + 1)` with `t` prime gives `n - t ^ 2 = t`, so the conjecture fails
whenever `t` is prime and `t ^ 2 + t - 1` is not; `t = 7` is the smallest such case.)
-/

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a241884.main) := by
  intro h
  -- `55` is not prime, so the conjecture would make `56` a term
  have hterm : OMA.S_oeis_a241884.IsTerm 56 := (h 56 (by norm_num)).2 (by norm_num)
  -- but the divisor `t = 7` gives the prime `56 - 49 = 7`
  exact hterm 7 (Nat.mem_divisors.2 ⟨by norm_num, by norm_num⟩) ⟨7, by norm_num, by norm_num⟩
