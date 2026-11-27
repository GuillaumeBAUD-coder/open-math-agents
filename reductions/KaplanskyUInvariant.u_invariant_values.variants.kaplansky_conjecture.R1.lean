import FormalConjectures.Paper.KaplanskyUInvariant

-- Reduction KaplanskyUInvariant.u_invariant_values.variants.kaplansky_conjecture.R1 of Kaplansky's conjecture
-- Credit: @cosmaticdev
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Kaplansky's conjecture is false: reduction to a field of u-invariant 6

Kaplansky conjectured that every finite u-invariant is a power of 2. Merkurjev [Merkurjev1989]
constructed a field of u-invariant 6, which is not a power of 2; this is the whole content of
the disproof. H1 below is exactly that theorem (the upstream variant `even` for n = 6), and H2
is the arithmetic fact that 6 is not a power of 2.
-/

namespace OMA.R_KaplanskyUInvariant_u_invariant_values_variants_kaplansky_conjecture_R1

open KaplanskyUInvariant

/-- Merkurjev's theorem [Merkurjev1989]: there exists a field of characteristic not 2 whose
u-invariant is 6. -/
def H1 : Prop := IsUInvariant 6

/-- The number 6 is not a power of 2. -/
def H2 : Prop := ¬ ∃ k : ℕ, (6 : ℕ) = 2 ^ k

theorem main : H1 → H2 → type_of% @KaplanskyUInvariant.u_invariant_values.variants.kaplansky_conjecture := by
  intro h1 h2 h
  exact h2 (h 6 h1)

end OMA.R_KaplanskyUInvariant_u_invariant_values_variants_kaplansky_conjecture_R1
