import Mathlib

/-!
# A007059: Number of balanced ordered trees with n nodes.

Source: https://oeis.org/A007059
Credit: @thatoneguy006

The conjecture stated here, from the entry:

  Conjecture: for n > 0, a(n+1) is the number of numbral divisors of (4^n-1)/3 = A002450(n)
  (see A048888 for the definition of numbral arithmetic). This has been verified computationally
  up to n=15. - John W. Layman, Dec 18 2001

The entry adds that the conjecture follows from Proposition 2.3 of Frosini and Rinaldi
(N. J. A. Sloane, Apr 29 2011); it is stated here as recorded.

Definitions.
* a(n), offset 0, a(0) = 0. The entry gives, for n >= 1, a(n) as the number of compositions of n
  in which all parts are smaller than the first part (Joerg Arndt); this is the definition used
  (with Mathlib's `Composition n`). It reproduces the data 0, 1, 1, 2, 3, 5, 8, 14, 24, ...
* Numbral arithmetic (Marc LeBrun, in A048888): addition is bitwise inclusive OR and
  multiplication is shift-and-OR, [d] * [e] = OR of the shifts d * 2^j over the 1-bits j of e.
  [d] divides [n] if [d] * [e] = [n] for some [e]. With this definition the numbral divisors
  of 14 are 1, 2, 3, 6, 7, 14, as in A048888.
-/

namespace OMA.S_oeis_a007059

/-- A007059(n): for `n ≥ 1`, the compositions of `n` whose later parts are all smaller than the
first part; `a 0 = 0`. -/
def a (n : ℕ) : ℕ :=
  if n = 0 then 0 else
    ((Finset.univ : Finset (Composition n)).filter
      (fun c => ∀ p ∈ c.blocks.tail, p < c.blocks.headI)).card

/-- Numbral multiplication: the bitwise OR of `d <<< j` over the 1-bits `j` of `e`. -/
def numbralMul (d e : ℕ) : ℕ :=
  ((List.range e.size).filter (fun j => e.testBit j)).foldl (fun acc j => acc ||| (d <<< j)) 0

/-- The number of numbral divisors of `N`. -/
noncomputable def numbralDivisorCount (N : ℕ) : ℕ :=
  Nat.card {d : ℕ | ∃ e : ℕ, numbralMul d e = N}

/-- Layman's conjecture: `a(n+1)` is the number of numbral divisors of `(4^n - 1)/3`. -/
theorem main : ∀ n : ℕ, 0 < n → a (n + 1) = numbralDivisorCount ((4 ^ n - 1) / 3) := by
  sorry

end OMA.S_oeis_a007059
