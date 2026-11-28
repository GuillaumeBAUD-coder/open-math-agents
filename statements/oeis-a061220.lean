import Mathlib

/-!
# A061220: where the least entry of the character table of S_n occurs

Source: https://oeis.org/A061220
Credit: @jagraj28

A061220 is the least entry in the character table of the symmetric group `S_n`
(1, -1, -1, -1, -2, -3, -6, -16, ...). The entry records a conjecture (Vladeta Jovovic, 2026):
for `n ≥ 2`, the least entry in the character table of `S_n` occurs in the column indexed by the
transpositions, of cycle type `(2, 1^(n-2))`; equivalently
`a(n) = min_λ χ^λ(2, 1^(n-2))`.

`main` states: for every `n ≥ 2` there is an irreducible character `χ` of `S_n` whose value at a
transposition is at most every entry `ψ(g)` of the character table (`ψ` irreducible, `g ∈ S_n`).
So the minimum of the table is attained in the transposition column.

Conventions:
* `S_n` is `Equiv.Perm (Fin n)`. The irreducible characters over `ℂ` are the characters of the
  simple objects of `FDRep ℂ (Equiv.Perm (Fin n))` (finite-dimensional complex representations).
* The transposition is `Equiv.swap 0 1`; all transpositions are conjugate, so they form one
  column and the choice does not matter.
* Characters of `S_n` are integer valued, so entries are compared through their real parts,
  which are the entries themselves.
-/

namespace OMA.S_oeis_a061220

open CategoryTheory

/-- `χ` is an irreducible complex character of `S_n`: the character of a simple
finite-dimensional complex representation. -/
def IsIrrChar (n : ℕ) (χ : Equiv.Perm (Fin n) → ℂ) : Prop :=
  ∃ V : FDRep ℂ (Equiv.Perm (Fin n)), Simple V ∧ V.character = χ

/-- Jovovic's conjecture in OEIS A061220. -/
theorem main : ∀ n : ℕ, (h : 2 ≤ n) →
    ∃ χ, IsIrrChar n χ ∧ ∀ ψ, IsIrrChar n ψ → ∀ g : Equiv.Perm (Fin n),
      (χ (Equiv.swap ⟨0, by omega⟩ ⟨1, by omega⟩)).re ≤ (ψ g).re := by
  sorry

end OMA.S_oeis_a061220
