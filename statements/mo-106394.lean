import Mathlib

/-!
# How many ways can a number be Fortunate?

Source: https://mathoverflow.net/questions/106394 (CC BY-SA 4.0).

An integer `m` is Fortunate if `m = q - P` where `P` is a primorial and `q` is the smallest prime
greater than `P + 1`. For a given `m` there are only finitely many primorials `P` admitting such a
decomposition (because `m` must exceed the largest prime dividing `P`). The question: is the number
of such representations of an integer `m` uniformly bounded above?

We state the positive answer: there is a bound `B` with at most `B` primorials `P` for every `m`.

Formalization notes:
* Primorials are the values `primorial k = ∏_{p ≤ k prime} p` (Mathlib); different `k` with the same
  value give the same `P`, so we count the set of values `P`, as the question does.
* The smallest prime above `P + 1` is `sInf {q | q.Prime ∧ P + 1 < q}`; `m = q - P` is written
  `m + P = q` (here `q > P`, so nothing is truncated).
* The count is `Set.encard`, so an infinite set could not satisfy the bound.
-/

namespace OMA.S_mo_106394

/-- The number of primorials `P` with `m = q(P) - P` is bounded independently of `m`. -/
theorem main : ∃ B : ℕ, ∀ m : ℕ,
    {P : ℕ | (∃ k, P = primorial k) ∧ m + P = sInf {q : ℕ | q.Prime ∧ P + 1 < q}}.encard ≤ B := by
  sorry

end OMA.S_mo_106394
