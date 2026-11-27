import FormalConjectures.Wikipedia.SternPrime

-- Reduction SternPrime.isSternPrime_iff.R1 of Stern Primes — isSternPrime iff
-- Credit: @ihateSAS
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Stern primes: exhausting the list

The conjecture is that the eight known Stern primes are all of them,

`IsSternPrime q ↔ q ∈ {2, 3, 17, 137, 227, 977, 1187, 1493}`.

The two directions are separate pieces of mathematics.

* `H1` is the open half: **no ninth Stern prime exists**.  It is a statement about all `q`
  outside a finite set, and it is the entire difficulty of the problem (verified below
  `2 * 10^13` only).
* `H2` is the finite half: each of the eight listed numbers is prime and admits no
  decomposition `p + 2 b^2` with `p` prime, `b ≥ 1`.  It is a finite verification, already
  carried out in the module as `SternPrime.isSternPrime_known_examples`, and it is stated
  here as a hypothesis so the two halves can be attacked separately.

The reduction's content is the assembly `⟨H1, H2⟩`.
-/

namespace OMA.R_SternPrime_isSternPrime_iff_R1

/-- The open half: every Stern prime belongs to the known list of eight. -/
def H1 : Prop :=
  ∀ q : ℕ, SternPrime.IsSternPrime q →
    q ∈ ({2, 3, 17, 137, 227, 977, 1187, 1493} : Set ℕ)

/-- The finite half: each of the eight listed numbers is a Stern prime. -/
def H2 : Prop :=
  ∀ q : ℕ, q ∈ ({2, 3, 17, 137, 227, 977, 1187, 1493} : Set ℕ) →
    SternPrime.IsSternPrime q

theorem main : H1 → H2 → type_of% @SternPrime.isSternPrime_iff := by
  intro h1 h2 q
  exact ⟨h1 q, h2 q⟩

end OMA.R_SternPrime_isSternPrime_iff_R1
