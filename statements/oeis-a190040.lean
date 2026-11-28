import Mathlib

/-!
# OEIS A190040: Barker's conjectures for nondecreasing arrangements of n+2 numbers in 0..8 with the last equal to 8 and each after the second equal to the sum of one or two of the preceding three

Source: https://oeis.org/A190040 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jaredwilder.

Entry A190040 (R. H. Hardin, May 04 2011), offset 1: Number of nondecreasing arrangements of n+2 numbers in 0..8 with the last equal to 8 and each after the second equal to the sum of one or two of the preceding three.
Formula section:
Empirical: a(n) = (1/3)*n^3 + 2*n^2 + (50/3)*n - 83 for n>6.
Conjectures from Colin Barker, May 04 2018: (Start)
G.f.: x*(13 - 28*x + 22*x^2 - 3*x^3 + 2*x^4 - 2*x^5 - 6*x^7 + x^8 + 3*x^9) / (1 - x)^4.
a(n) = 4*a(n-1) - 6*a(n-2) + 4*a(n-3) - a(n-4) for n>6.
(End)

Formalization notes:
* An arrangement of n+2 numbers in 0..8 is a map x : Fin (n + 2) -> Fin 9; it is nondecreasing
  when x is monotone, and its last entry is x (n + 1) = 8.
* Each entry after the second, at position i >= 2 (counting from 0), must equal the entry at one
  of the positions i - 3, i - 2, i - 1 that exist, or the sum of the entries at two different such
  positions (okAt), the reading of the sibling entry A190039 (column 7 of the same table A190041).
* The entry starts at n = 1 and the g.f. is A(x) = Sum_(n >= 1) a(n) x^n, so a is set to 0 at
  n = 0 and the g.f. is stated for mk a over the integers as A * D = N (D has constant term 1).
* The statement is the conjunction of Barker's conjectures: the recurrence (for n > 6, in the
  integers) and the g.f.
* Controls: the definition gives 13, 24, 40, 65, 105, 164, 246 for n = 1..7 (direct enumeration),
  the entry's data.
-/

namespace OMA.S_oeis_a190040

open PowerSeries Finset

/-- Entry i of x is the entry at one of the (at most three) positions just before i, or the sum of
the entries at two different such positions. -/
def okAt {L N : ℕ} (x : Fin L → Fin N) (i : Fin L) : Prop :=
  ∃ j l : Fin L, j < i ∧ l < i ∧ (i : ℕ) ≤ j + 3 ∧ (i : ℕ) ≤ l + 3 ∧
    ((x i : ℕ) = x j ∨ (j ≠ l ∧ (x i : ℕ) = x j + x l))

/-- x is nondecreasing, its last entry is 7, and every entry after the second is the sum of one
or two of the preceding three entries. -/
def good {n : ℕ} (x : Fin (n + 2) → Fin 9) : Prop :=
  Monotone x ∧ (x (Fin.last (n + 1)) : ℕ) = 8 ∧ ∀ i : Fin (n + 2), 2 ≤ (i : ℕ) → okAt x i

instance {n : ℕ} : DecidablePred (@good n) := fun x => by unfold good okAt Monotone; infer_instance

/-- A190040: number of nondecreasing arrangements of n+2 numbers in 0..8 with the last equal to 8 and each after the second equal to the sum of one or two of the preceding three. -/
def a (n : ℕ) : ℕ := if n = 0 then 0 else ((univ : Finset (Fin (n + 2) → Fin 9)).filter good).card

/-- Barker's conjectures. -/
theorem main :
    (∀ n : ℕ, 6 < n → (a n : ℤ) = 4 * a (n - 1) - 6 * a (n - 2) + 4 * a (n - 3) - a (n - 4)) ∧
    mk (fun n => (a n : ℤ)) * ((1 - X) ^ 4) =
      (X * (13 - 28 * X + 22 * X ^ 2 - 3 * X ^ 3 + 2 * X ^ 4 - 2 * X ^ 5 - 6 * X ^ 7 + X ^ 8 + 3 * X ^ 9) : PowerSeries ℤ) := by
  sorry

end OMA.S_oeis_a190040
