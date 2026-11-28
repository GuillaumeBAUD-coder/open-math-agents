import Mathlib

/-!
# Irreducible polynomials with constrained coefficients

The question asks: "About how many polynomials with coefficients in {±1} and of degree d are
irreducible?" Writing S_d for the set of polynomials of degree d with all d+1 coefficients in
{±1}, the top-voted answer on the page proves (part 3 there): "There exist infinitely many d for which at least 50% of the
polynomials in S_d are irreducible", namely every d = 2^n - 1 with n ≥ 1.

The question itself is open-ended (an asymptotic count); this file formalizes the result from
the top-voted answer that settles a precise part of it, exactly in the form proved there: for every n ≥ 1 and
d = 2^n - 1, at least half of the 2^(d+1) polynomials in S_d are irreducible.

Reading choices:
* A polynomial of S_d is given by its sign vector s : Fin (d+1) → ℤˣ (the units of ℤ are
  exactly 1 and -1); `signPoly d s` is ∑_{i=0}^{d} s_i X^i. Distinct sign vectors give distinct
  polynomials, so counting sign vectors counts the polynomials of S_d (there are 2^(d+1)).
* "Irreducible" is irreducibility in ℚ[X] (Mathlib's `Irreducible`). For these polynomials this
  is the same as irreducibility in ℤ[X], because they are primitive (leading coefficient ±1).
* "At least 50%" is stated without division: (number of all sign vectors) ≤ 2 · (number of
  sign vectors giving an irreducible polynomial).
* The open asymptotic question ("about how many") and the conditional (GRH) part of the answer
  are not formalized.

The top-voted answer settles it: for d = 2^n - 1 every such f satisfies f(x+1) ≡ x^d (mod 2), so
f(x+1) is Eisenstein at 2 for half of the sign choices.

Source: https://mathoverflow.net/questions/7969/irreducible-polynomials-with-constrained-coefficients
Credit: @xor2k
-/

namespace OMA.S_mo_7969

open Polynomial

/-- The polynomial `∑_{i=0}^{d} s_i X^i ∈ ℚ[X]` with sign vector `s`. -/
noncomputable def signPoly (d : ℕ) (s : Fin (d + 1) → ℤˣ) : ℚ[X] :=
  ∑ i : Fin (d + 1), C (((s i : ℤ)) : ℚ) * X ^ (i : ℕ)

theorem main : ∀ n : ℕ, 1 ≤ n →
    Fintype.card (Fin (2 ^ n - 1 + 1) → ℤˣ) ≤
      2 * Nat.card {s : Fin (2 ^ n - 1 + 1) → ℤˣ // Irreducible (signPoly (2 ^ n - 1) s)} := by
  sorry

end OMA.S_mo_7969
