import Mathlib

/-!
# Giuga's Conjecture on Primality

Source: https://www.openproblemgarden.org/op/giugas_conjecture_on_primality

Conjecture (Giuga): p is a prime iff  sum_{i=1}^{p-1} i^(p-1) ≡ -1 (mod p).

Conventions:
* p ranges over natural numbers with p ≥ 2, the range in which Giuga posed the
  conjecture (Borwein, Borwein, Borwein, Girgensohn, Amer. Math. Monthly 103 (1996),
  cited on the page). For p = 1 the sum is empty, 0 ≡ -1 (mod 1) holds and 1 is not
  prime, so the bare biconditional would be false for a trivial reason; p = 0 is
  likewise excluded.
* The sum is over i ∈ Finset.Icc 1 (p - 1), computed in ℤ, and the congruence is
  Int.ModEq modulo p.
* The direction prime → congruence follows from Fermat's little theorem; the open
  content is the converse.
-/

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

namespace OMA.S_opg_giugas_conjecture_on_primality

theorem main :
    ∀ p : ℕ, 2 ≤ p →
      (p.Prime ↔ (∑ i ∈ Finset.Icc 1 (p - 1), (i : ℤ) ^ (p - 1)) ≡ -1 [ZMOD (p : ℤ)]) := by
  sorry

end OMA.S_opg_giugas_conjecture_on_primality
