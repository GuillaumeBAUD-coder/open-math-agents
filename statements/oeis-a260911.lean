import Mathlib

/-!
# A260911: Least positive integer k < prime(n) such that there are 0 < i < j < k for which i^2 + j^2 = k^2 and i,j,k are all quadratic residues modulo prime(n), or 0 if no such k exists.

Source: https://oeis.org/A260911
Credit: @divmxnd0x

Let `R(p) = {0 < r < p : r is a quadratic residue mod p}` and
`N(p) = {0 < n < p : n is a quadratic nonresidue mod p}`.

Conjecture (Zhi-Wei Sun, stated in A260911):
(i) `a(n) > 0` for all `n > 25`. In other words, for any prime `p > 100`, we have `a^2 + b^2 = c^2`
for some `a, b, c` in the set `R(p)`.
(ii) For any prime `p > 50`, we have `a^2 + b^2 = c^2` for some `a, b, c` in the set `N(p)`.
(iii) For any prime `p > 32`, we have `a^2 + b^2 = c^2` for some `a, b` in the set `R(p)` and `c` in
the set `N(p)`.

Formalization notes:
* The equation `a^2 + b^2 = c^2` is an equation of natural numbers (as in the definition of the
  sequence), not a congruence; `a, b, c` lie in `{1, ..., p-1}`.
* `r` (with `0 < r < p`) is a quadratic residue mod `p` iff `IsSquare (r : ZMod p)`.
* With these definitions `a(1), ..., a(20)` = 0, 0, 0, 0, 5, 0, 0, 0, 0, 25, 0, 34, 0, 41, 25, 25,
  5, 5, 26, 5 (data of A260911); below 600 the primes failing (i), (ii), (iii) are at most 97, 47
  and 31 respectively.
-/

namespace OMA.S_oeis_a260911

/-- `r ∈ R(p)`: `0 < r < p` and `r` is a quadratic residue modulo `p`. -/
def InR (p r : ℕ) : Prop :=
  0 < r ∧ r < p ∧ IsSquare (r : ZMod p)

/-- `r ∈ N(p)`: `0 < r < p` and `r` is a quadratic nonresidue modulo `p`. -/
def InN (p r : ℕ) : Prop :=
  0 < r ∧ r < p ∧ ¬ IsSquare (r : ZMod p)

/-- Sun's conjecture, parts (i), (ii) and (iii). -/
theorem main :
    (∀ p : ℕ, p.Prime → 100 < p →
        ∃ a b c : ℕ, InR p a ∧ InR p b ∧ InR p c ∧ a ^ 2 + b ^ 2 = c ^ 2) ∧
      (∀ p : ℕ, p.Prime → 50 < p →
        ∃ a b c : ℕ, InN p a ∧ InN p b ∧ InN p c ∧ a ^ 2 + b ^ 2 = c ^ 2) ∧
      ∀ p : ℕ, p.Prime → 32 < p →
        ∃ a b c : ℕ, InR p a ∧ InR p b ∧ InN p c ∧ a ^ 2 + b ^ 2 = c ^ 2 := by
  sorry

end OMA.S_oeis_a260911
