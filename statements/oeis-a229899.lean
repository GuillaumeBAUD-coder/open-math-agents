import Mathlib

/-!
# A229899: a(n) = |{0<g<p_n: g-1, g, g+1 are primitive roots mod p_n}|, where p_n denotes the n-th prime.

Source: https://oeis.org/A229899
Credit: @azmiozgen

Conjecture (Zhi-Wei Sun, from the entry): a(n) > 0 except for n = 1, 2, 3, 4, 6, 10, 18. In other
words, for any prime p > 7 not equal to 13 or 29 or 61, there are three consecutive integers which
are primitive roots modulo p. (Further conjectures of the entry are not stated here.)

Formalization notes:
* p_n = `Nat.nth Nat.Prime (n - 1)` (p_1 = 2). g is a primitive root mod p when its image in
  ZMod p has multiplicative order p - 1 (`IsPrimitiveRoot (g : ZMod p) (p - 1)`); 0 is not.
* Stated for every n ≥ 1: a(n) = 0 iff n ∈ {1, 2, 3, 4, 6, 10, 18}.
* Controls (computed): a(1..30) = 0, 0, 0, 0, 1, 0, 2, 1, 1, 0, 1, 2, 2, 2, 4, 6, 7, 0, 1, 2, 2, 1, 10,
  10, 8, 4, 4, 13, 4, 6, as in the entry; for n < 120, a(n) = 0 only at the listed n.
-/

namespace OMA.S_oeis_a229899

open Classical

/-- The `n`-th prime, `p 1 = 2`. -/
noncomputable def p (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

/-- A229899(n). -/
noncomputable def a (n : ℕ) : ℕ :=
  ((Finset.Ioo 0 (p n)).filter fun g =>
    IsPrimitiveRoot ((g - 1 : ℕ) : ZMod (p n)) (p n - 1) ∧
    IsPrimitiveRoot ((g : ℕ) : ZMod (p n)) (p n - 1) ∧
    IsPrimitiveRoot ((g + 1 : ℕ) : ZMod (p n)) (p n - 1)).card

/-- The conjecture of the entry (all parts listed above). -/
theorem main :
    ∀ n : ℕ, 1 ≤ n →
      (a n = 0 ↔ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 6 ∨ n = 10 ∨ n = 18) := by
  sorry

end OMA.S_oeis_a229899
