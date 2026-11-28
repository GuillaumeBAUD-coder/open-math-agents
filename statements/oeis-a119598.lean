import Mathlib

/-!
# A119598: Numbers that are repunits in four or more bases

Source: https://oeis.org/A119598
Credit: @sobrien032

The terms are 1, 31, 8191 (offset 1). The entry's comment (Bernard Schott, Jun 25 2013):
"Following the Goormaghtigh conjecture (Links), 31 and 8191 which are both Mersenne numbers, are
the only primes which are Brazilian in two different bases."

Brazilian numbers are defined in A125134: `n` is Brazilian if there is a natural number `b` with
`1 < b < n - 1` such that the representation of `n` in base `b` has all equal digits. So `n` is
Brazilian in base `b` when `1 < b < n - 1` and all the digits of `n` in base `b` are equal.
`Nat.digits b n` is the list of the digits of `n` in base `b` (least significant first, no leading
zeros); the order of the digits does not matter for whether they are all equal. For natural
numbers, `b < n - 1` holds exactly when `b + 1 < n`, as over the integers. A prime `p` is Brazilian
in two different bases when it is Brazilian in base `b` and in base `c` for some `b ≠ c`; for
example 31 = 11111 in base 2 = 111 in base 5, and 8191 = 1111111111111 in base 2 = 111 in base 90.

The Goormaghtigh conjecture, in the form on the Wikipedia page that the entry links: the
equation `(x^m - 1)/(x - 1) = (y^n - 1)/(y - 1)` in integers `x, y > 1`, `x ≠ y`, with exponents
`m, n > 2`, written with the convention `x > y > 1` (then `n > m > 2` follows), has only the
solutions `(x, y, m, n) = (5, 2, 3, 5)` and `(90, 2, 3, 13)`, that is
`31 = (5^3 - 1)/(5 - 1) = (2^5 - 1)/(2 - 1)` and `8191 = (90^3 - 1)/(90 - 1) = (2^13 - 1)/(2 - 1)`.
For `x > 1` the quotient `(x^m - 1)/(x - 1)` is exactly `1 + x + ... + x^(m-1)`, so both sides
are written below as such sums, without division.

A Mersenne number is a number `2^q - 1` (some authors also ask that `q` be prime);
`31 = 2^5 - 1` and `8191 = 2^13 - 1`, with `5` and `13` prime.

The statement: if the Goormaghtigh conjecture holds, then 31 and 8191 are Mersenne numbers, and a
natural number `p` is a prime that is Brazilian in two different bases if and only if `p = 31` or
`p = 8191`.
-/

namespace OMA.S_oeis_a119598

/-- The Goormaghtigh conjecture: if `x > y > 1`, `m > 2`, `n > 2` and
`1 + x + ... + x^(m-1) = 1 + y + ... + y^(n-1)`, then `(x, y, m, n)` is `(5, 2, 3, 5)` or
`(90, 2, 3, 13)`. -/
def GoormaghtighConjecture : Prop :=
  ∀ x y m n : ℕ, 1 < y → y < x → 2 < m → 2 < n →
    ∑ i ∈ Finset.range m, x ^ i = ∑ i ∈ Finset.range n, y ^ i →
      (x = 5 ∧ y = 2 ∧ m = 3 ∧ n = 5) ∨ (x = 90 ∧ y = 2 ∧ m = 3 ∧ n = 13)

/-- `n` is Brazilian in base `b` (A125134): `1 < b < n - 1` and the representation of `n` in
base `b` has all equal digits. -/
def IsBrazilianInBase (n b : ℕ) : Prop :=
  1 < b ∧ b < n - 1 ∧ ∀ i ∈ Nat.digits b n, ∀ j ∈ Nat.digits b n, i = j

/-- Under the Goormaghtigh conjecture: 31 and 8191 are Mersenne numbers, and they are the only
primes that are Brazilian in two different bases. -/
theorem main : GoormaghtighConjecture →
    (31 = 2 ^ 5 - 1 ∧ 8191 = 2 ^ 13 - 1) ∧
      ∀ p : ℕ, ((p.Prime ∧ ∃ b c : ℕ, b ≠ c ∧ IsBrazilianInBase p b ∧ IsBrazilianInBase p c) ↔
        (p = 31 ∨ p = 8191)) := by
  sorry

end OMA.S_oeis_a119598
