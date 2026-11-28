import Mathlib

/-!
# OEIS A244241: Chai Wah Wu's conjectured linear recurrence (for n > 40) and rational g.f. for the number of partitions of n into 5 parts whose i-th smallest part is different from i

Source: https://oeis.org/A244241 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with claude-code (model claude-fable-5-2), submitted by @VestigeClub.

Entry: A244241: Number of partitions of n into 5 parts such that every i-th smallest part (counted with multiplicity) is different from i.
The conjecture, as the entry gives it:
  Conjectures from Chai Wah Wu, Apr 18 2024: a(n) = a(n-1) + a(n-2) - a(n-5) - a(n-6) - a(n-7) + a(n-8) + a(n-9) + a(n-10) - a(n-13) - a(n-14) + a(n-15) for n > 40. G.f.: x^20*(-x^20 + 2*x^16 + 2*x^15 + 4*x^14 + x^13 - 3*x^12 - 7*x^11 - 9*x^10 - 5*x^9 + 2*x^8 + 8*x^7 + 9*x^6 + 8*x^5 + x^4 - 3*x^3 - 5*x^2 - 4*x - 1)/((x - 1)^5*(x + 1)^2*(x^2 + 1)*(x^2 + x + 1)*(x^4 + x^3 + x^2 + x + 1)).

Formalization notes:
* A partition of n into 5 parts is a `Nat.Partition n` whose multiset of parts has 5 elements.
  Its parts in increasing order, counted with multiplicity, are the list `p.parts.sort (· ≤ ·)`;
  the i-th smallest part (i = 1..5) is the entry of that list at index i - 1, and the condition
  is that this entry is different from i. With the 0-based index j = i - 1 this reads
  `(p.parts.sort (· ≤ ·))[j] ≠ j + 1` for every valid index j.
* `a n` is defined for every natural n as the number of such partitions. The entry has offset
  20; the definition gives a(n) = 0 for n < 20 (the smallest admissible partition is
  2 + 3 + 4 + 5 + 6), so the power series ∑_{n ≥ 0} a(n) x^n is the g.f. of the entry.
* The recurrence is stated in ℤ for every n ≥ 41 (the entry's "for n > 40"); all indices
  n - 1, ..., n - 15 are then at least 26, so natural-number subtraction is exact.
* The g.f. is stated as an identity of formal power series over ℚ, cleared of its denominator:
  (∑ a(n) x^n) * denominator = numerator, with numerator and denominator factors written
  exactly as in the entry. The denominator has constant term -1, so it is a unit and the
  identity is equivalent to the quotient form.
* Controls: the proof file derives from this definition a(n) = 0 for n < 20 and
  a(20), ..., a(40) = 1, 5, 11, 19, 29, 39, 53, 67, 84, 103, 126, 150, 179, 210, 246, 285, 329,
  376, 430, 487, 551, the first 21 terms of the entry's DATA.
-/

namespace OMA.S_oeis_a244241

/-- A244241: the number of partitions of n into 5 parts whose i-th smallest part (counted with
multiplicity) is different from i, for every i = 1..5. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {p : n.Partition // p.parts.card = 5 ∧
    ∀ (i : ℕ) (h : i < (p.parts.sort (· ≤ ·)).length), (p.parts.sort (· ≤ ·))[i] ≠ i + 1}

/-- Wu's conjectures: the recurrence for n > 40 and the rational g.f. -/
theorem main : (∀ n : ℕ, 41 ≤ n → (a n : ℤ) = a (n - 1) + a (n - 2) - a (n - 5) - a (n - 6) -
      a (n - 7) + a (n - 8) + a (n - 9) + a (n - 10) - a (n - 13) - a (n - 14) + a (n - 15)) ∧
    PowerSeries.mk (fun n => (a n : ℚ)) *
      ((PowerSeries.X - 1) ^ 5 * (PowerSeries.X + 1) ^ 2 * (PowerSeries.X ^ 2 + 1) *
        (PowerSeries.X ^ 2 + PowerSeries.X + 1) *
        (PowerSeries.X ^ 4 + PowerSeries.X ^ 3 + PowerSeries.X ^ 2 + PowerSeries.X + 1)) =
      PowerSeries.X ^ 20 * (-PowerSeries.X ^ 20 + 2 * PowerSeries.X ^ 16 + 2 * PowerSeries.X ^ 15 +
        4 * PowerSeries.X ^ 14 + PowerSeries.X ^ 13 - 3 * PowerSeries.X ^ 12 -
        7 * PowerSeries.X ^ 11 - 9 * PowerSeries.X ^ 10 - 5 * PowerSeries.X ^ 9 +
        2 * PowerSeries.X ^ 8 + 8 * PowerSeries.X ^ 7 + 9 * PowerSeries.X ^ 6 +
        8 * PowerSeries.X ^ 5 + PowerSeries.X ^ 4 - 3 * PowerSeries.X ^ 3 -
        5 * PowerSeries.X ^ 2 - 4 * PowerSeries.X - 1) := by
  sorry

end OMA.S_oeis_a244241
