import Mathlib

/-!
# A272515: Number of set partitions of [n] into three blocks with distinct sizes.

Source: https://oeis.org/A272515
Credit: @xor2k

Vaclav Kotesovec, in the formula section of A272515:
  Conjecture: a(n) ~ 3^n / 6.

This is the only conjecture of the row and it is stated in full.

Conventions:
* [n] is the n-element set `Fin n`. A set partition of [n] is a `Finpartition` of
  `(Finset.univ : Finset (Fin n))`: a finite set `parts` of nonempty, pairwise disjoint finite
  sets (the blocks) with union [n].
* `a n` is the number of set partitions of [n] with exactly three blocks such that any two
  different blocks have different cardinalities. It is defined for every n ≥ 0 (and is 0 for
  n < 6, the smallest possible sizes being 1 + 2 + 3), so the offset of the entry plays no role
  in the asymptotic claim.
* `a(n) ~ 3^n / 6` has its standard meaning: the quotient a(n) / (3^n / 6), computed in ℝ, tends
  to 1 as n tends to infinity.

Numerical check: a Python count of the same objects (sum of the multinomial coefficients
n! / (i! j! k!) over i + j + k = n with 0 < i < j < k) gives, for n = 0, 1, 2, ...:
0, 0, 0, 0, 0, 0, 60, 105, 448, 2016, 4980, 15675, 61644, 155155, 482573, 1733550, 4549808,
13890360, 48104628, 128949675, ...; the nonzero terms from n = 6 on are the DATA of the entry as
remembered (the entry was not available offline when this file was written), and
6 a(n) / 3^n = 0.793, 0.896, 0.954 for n = 50, 200, 1000.
-/

namespace OMA.S_oeis_a272515

/-- A272515: the number of set partitions of [n] into three blocks with pairwise distinct sizes. -/
def a (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Finpartition (Finset.univ : Finset (Fin n)))).filter fun P =>
    P.parts.card = 3 ∧ ∀ s ∈ P.parts, ∀ t ∈ P.parts, s ≠ t → s.card ≠ t.card).card

/-- Kotesovec's conjecture: a(n) ~ 3^n / 6. -/
theorem main :
    Filter.Tendsto (fun n : ℕ => (a n : ℝ) / ((3 : ℝ) ^ n / 6)) Filter.atTop (nhds 1) := by
  sorry

end OMA.S_oeis_a272515
