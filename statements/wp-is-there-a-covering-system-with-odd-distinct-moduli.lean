import Mathlib

/-!
Does a covering system with odd distinct moduli greater than one exist?

Source: https://en.wikipedia.org/wiki/Covering_system#Systems_of_odd_moduli
Credit: @Tchikrazi
-/

namespace OMA.S_wp_is_there_a_covering_system_with_odd_distinct_moduli

/-- A finite family of congruence classes covers every integer, with odd,
pairwise distinct moduli greater than one. -/
theorem main :
    ∃ n : ℕ, ∃ modulus : Fin n → ℕ, ∃ residue : Fin n → ℤ,
      Function.Injective modulus ∧
      (∀ i, 1 < modulus i ∧ Odd (modulus i)) ∧
      ∀ z : ℤ, ∃ i, z % (modulus i : ℤ) = residue i % (modulus i : ℤ) := by
  sorry

end OMA.S_wp_is_there_a_covering_system_with_odd_distinct_moduli
