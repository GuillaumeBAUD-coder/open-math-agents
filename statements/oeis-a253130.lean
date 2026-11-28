import Mathlib

/-!
# OEIS A253130
Source: https://oeis.org/A253130
R. H. Hardin counts four-entry words over 0 through n for which the medians
of the two adjacent triples admit signs summing to zero. Since both medians
are nonnegative this is exactly equality of those medians. The polynomial
is recorded as empirical and the generating function and recurrence were
proposed by Colin Barker in 2018.
-/

namespace OMA.S_oeis_a253130

def median {α : Type*} [LinearOrder α] (a b c : α) : α :=
  max (min a b) (min (max a b) c)

def accepted {α : Type*} [LinearOrder α] (w : Fin 4 → α) : Bool :=
  decide (median (w 0) (w 1) (w 2) = median (w 1) (w 2) (w 3))

def words (q : ℕ) : Finset (Fin 4 → Fin q) :=
  Finset.univ.filter (fun w => accepted w = true)

def count (n : ℕ) : ℚ := ((words (n+1)).card : ℕ)

def terms : ℕ → ℚ
  | 0 => 0
  | n+1 => count (n+1)

open PowerSeries

theorem main :
    (∀ n : ℕ, count n = ((n:ℚ)^4 + 8*n^3 + 14*n^2 + 10*n + 3)/3) ∧
    (∀ n : ℕ, terms (n+6) = 5*terms (n+5) - 10*terms (n+4) +
      10*terms (n+3) - 5*terms (n+2) + terms (n+1)) ∧
    (1-X)^5 * mk terms = (X*(3-X)*(4-X+2*X^2-X^3) : PowerSeries ℚ) := by
  sorry

end OMA.S_oeis_a253130
