import FormalConjectures.Paper.KaplanskyUInvariant

/-!
# Reduction `KaplanskyUInvariant.u_invariant_values.variants.kaplansky_conjecture`

Kaplansky conjectured that the `u`-invariant of a field, when finite, is always a power of two.
Merkurjev disproved this with a field of `u`-invariant `6`, but the catalogue carries the
statement in the sharper form "some `n` which is not a power of two is a `u`-invariant", and
Izhboldin's field of `u`-invariant `9` is exactly such an `n` — `9` is odd and greater than
one, so it is not `2 ^ k` for any `k`, and `9` is not even, so Merkurjev's even case does not
cover it.

The split isolates those two ingredients, which are genuinely independent:

* `H1` is the mathematical content: `9` really is a `u`-invariant. This is Izhboldin's
  theorem, and it is the only deep input; it is a separate catalogue target in its own right.
* `H2` is the arithmetic content: `9` is not `2 ^ k` for any `k`.

`H2` alone gives nothing (every power of two refutes nothing without an `n`), and `H1` alone
gives nothing either (`IsUInvariant 8` would be consistent with Kaplansky's claim), so the
pair is exactly the refutation and neither half implies the other.
-/

-- Reduction KaplanskyUInvariant.u_invariant_values.variants.kaplansky_conjecture.R1
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

namespace OMA.R_KaplanskyUInvariant_u_invariant_values_variants_kaplansky_conjecture_R1

open KaplanskyUInvariant

/-- Izhboldin's theorem: `9` is the `u`-invariant of some field. -/
def H1 : Prop := IsUInvariant 9

/-- `9` is not a power of two. -/
def H2 : Prop := ∀ k : ℕ, (9 : ℕ) ≠ 2 ^ k

theorem main : H1 → H2 →
    type_of% @KaplanskyUInvariant.u_invariant_values.variants.kaplansky_conjecture := by
  intro h1 h2 hall
  obtain ⟨k, hk⟩ := hall 9 h1
  exact h2 k hk

end OMA.R_KaplanskyUInvariant_u_invariant_values_variants_kaplansky_conjecture_R1
