import Mathlib

/-!
# Odd incongruent covering systems

Source: https://www.openproblemgarden.org/op/odd_incongruent_covering_systems

Conjecture (Erdős, Selfridge). There is no covering system whose moduli are odd,
distinct, and greater than 1.

Here a(n) denotes the residue class {a + n t : t ∈ ℤ}, and a covering system is a finite
collection {a_1(n_1), ..., a_k(n_k)} of residue classes whose union covers all integers.

Conventions:
* A finite collection of residue classes is a `Finset (ℤ × ℕ)`; the pair (a, n) stands
  for the class a(n) = {x ∈ ℤ : x ≡ a (mod n)}.
* moduli odd and greater than 1: every pair (a, n) in the collection has `Odd n` and
  `1 < n`.
* moduli distinct: no two different classes of the collection share a modulus,
  `Set.InjOn Prod.snd`, i.e. the map (a, n) ↦ n is injective on the collection.
* covers all integers: every x : ℤ satisfies x ≡ a [ZMOD n] for some (a, n) in the
  collection.
* The conjecture asserts that no such finite collection exists.
-/

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

namespace OMA.S_opg_odd_incongruent_covering_systems

theorem main :
    ¬ ∃ S : Finset (ℤ × ℕ),
      (∀ c ∈ S, Odd c.2 ∧ 1 < c.2) ∧
      Set.InjOn Prod.snd (S : Set (ℤ × ℕ)) ∧
      ∀ x : ℤ, ∃ c ∈ S, x ≡ c.1 [ZMOD (c.2 : ℤ)] := by
  sorry

end OMA.S_opg_odd_incongruent_covering_systems
