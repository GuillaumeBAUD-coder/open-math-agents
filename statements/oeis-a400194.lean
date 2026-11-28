import Mathlib

/-!
# A400194: Maximum number of terms in a 2-dense sublist of divisors of n.

Source: https://oeis.org/A400194
Credit: @xor2k

Comment line of A400194 (the entry is by Omar E. Pol, Sep 20 2026):
  Conjecture: a(n) is the product of the ruler function of n and the maximum number of odd terms
  in a 2-dense sublist of divisors of n.
This is the only conjecture of the entry. The ruler function is A001511 and the maximum number of
odd terms in a 2-dense sublist of divisors of n is A400195(n), so the conjecture is the formula
line of the entry, a(n) = A001511(n) * A400195(n); `main` states it for every n ≥ 1 (A400194 has
offset 1), in ℕ.

This is mathematically the same equation as the merged statement oeis-a400195
(A400195(n) = A400194(n) / A001511(n), stated there in ℚ), read from the side of A400194. The
definitions `terms`, `IsDense`, `denseLists`, the two maxima and `a001511` are copied verbatim from
that statement (only the names of the two sequences are exchanged: here `a` is A400194 and
`a400195` is A400195), so that both statements share their conventions.

The 2-dense sublists of divisors of n are the pieces of the increasing list of divisors of n
when it is cut between consecutive divisors d < d' with d' > 2*d (as the entries' Mathematica
programs do with Split; see also the comments of A384222, whose n-th row lists the lengths of
these pieces). Such a piece is determined by its first term a and last term b,
and its terms are the divisors d of n with a ≤ d ≤ b (`terms n a b`). `IsDense n a b` says that
a and b are divisors of n with a ≤ b, that the divisor following each divisor d with a ≤ d < b
is at most 2*d (some divisor e has d < e ≤ 2*d), that the divisor before a, if any, is less
than a/2, and that the divisor after b, if any, is greater than 2*b. `denseLists n` is the set
of pairs (a, b) of the 2-dense sublists of divisors of n.

The referenced sequences, by their own entries' definitions:
* A400195(n) (offset 1) is the maximum number of odd terms in a 2-dense sublist of divisors of n.
* A001511(n) (offset 1), the ruler function, is the exponent of the highest power of 2 dividing
  2n, equivalently the 2-adic valuation of 2n: `padicValNat 2 (2 * n)`.

Numerical check: a Python copy of these definitions gives for n = 1..20
  a(n)       = 1, 2, 1, 3, 1, 4, 1, 4, 1, 2, 1, 6, 1, 2, 2, 5, 1, 6, 1, 6
  A400195(n) = 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 2
  A001511(n) = 1, 2, 1, 3, 1, 2, 1, 4, 1, 2, 1, 3, 1, 2, 1, 5, 1, 2, 1, 3
compared with DATA: identical for the first 100 terms of A400194, A400195 and A001511, and the
equation holds for all n ≤ 100.
-/

namespace OMA.S_oeis_a400194

/-- The terms of the sublist of divisors of n from a to b: the divisors d of n with a ≤ d ≤ b. -/
def terms (n a b : ℕ) : Finset ℕ := (Nat.divisors n).filter (fun d => a ≤ d ∧ d ≤ b)

/-- The divisors of n from a to b form a 2-dense sublist of divisors of n. -/
abbrev IsDense (n a b : ℕ) : Prop :=
  a ∈ Nat.divisors n ∧ b ∈ Nat.divisors n ∧ a ≤ b ∧
    (∀ d ∈ Nat.divisors n, a ≤ d → d < b → ∃ e ∈ Nat.divisors n, d < e ∧ e ≤ 2 * d) ∧
    (∀ p ∈ Nat.divisors n, p < a → 2 * p < a) ∧
    (∀ q ∈ Nat.divisors n, b < q → 2 * b < q)

/-- The 2-dense sublists of divisors of n, as pairs (first term, last term). -/
def denseLists (n : ℕ) : Finset (ℕ × ℕ) :=
  (Nat.divisors n ×ˢ Nat.divisors n).filter (fun p => IsDense n p.1 p.2)

/-- A400194(n): the maximum number of terms in a 2-dense sublist of divisors of n. -/
def a (n : ℕ) : ℕ := (denseLists n).sup (fun p => (terms n p.1 p.2).card)

/-- A400195(n): the maximum number of odd terms in a 2-dense sublist of divisors of n. -/
def a400195 (n : ℕ) : ℕ := (denseLists n).sup (fun p => ((terms n p.1 p.2).filter Odd).card)

/-- A001511(n), the ruler function: the 2-adic valuation of 2n. -/
def a001511 (n : ℕ) : ℕ := padicValNat 2 (2 * n)

/-- The conjecture: a(n) = A001511(n) * A400195(n) for n ≥ 1. -/
theorem main : ∀ n : ℕ, 1 ≤ n → a n = a001511 n * a400195 n := by
  sorry

end OMA.S_oeis_a400194
