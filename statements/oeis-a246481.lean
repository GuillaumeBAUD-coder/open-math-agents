import Mathlib

/-!
# A246481: length 5 0..n arrays with no pair in four consecutive terms totalling n

A246481(n) is the number of arrays `x 0, ..., x 4` (length 2+3 = 5) with entries in
0..n such that no two terms lying in a common window of four consecutive terms add up to
exactly n; that is, `x i + x j ≠ n` whenever `i < j < i + 4`. A brute-force count of this
reading gives 2, 14, 132, 484, 1734, 4386, 10376, 20840 for n = 1..8, matching the listed
terms.

The offset is 1; `a 0` is not a term of the sequence and is set to 0 in the generating
function, which has no constant term.

The problem: the conjectures of Colin Barker (Nov 06 2018):
  G.f.: 2*x*(1 + 4*x + 45*x^2 + 52*x^3 + 191*x^4 + 72*x^5 + 115*x^6) / ((1 - x)^6*(1 + x)^3),
  a(n) = 5*n - 11*n^2 + 10*n^3 - 4*n^4 + n^5 for n even,
  a(n) = 9 - 10*n - 4*n^2 + 10*n^3 - 4*n^4 + n^5 for n odd.
The g.f. is stated after multiplying both sides by the denominator; the closed forms are
stated for the terms of the sequence, n ≥ 1.

Source: https://oeis.org/A246481
Credit: @VashaTS
-/

namespace OMA.S_oeis_a246481

open PowerSeries

/-- No two terms within four consecutive positions total exactly `n`. -/
def NoPairTotal (n : ℕ) (x : Fin 5 → Fin (n + 1)) : Prop :=
  ∀ i j : Fin 5, i < j → j.val < i.val + 4 → (x i).val + (x j).val ≠ n

instance (n : ℕ) (x : Fin 5 → Fin (n + 1)) : Decidable (NoPairTotal n x) := by
  unfold NoPairTotal; infer_instance

/-- A246481(n). -/
def a (n : ℕ) : ℕ := (Finset.univ.filter fun x : Fin 5 → Fin (n + 1) => NoPairTotal n x).card

theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * ((1 - X) ^ 6 * (1 + X) ^ 3) =
      2 * X * (1 + 4 * X + 45 * X ^ 2 + 52 * X ^ 3 + 191 * X ^ 4 + 72 * X ^ 5 + 115 * X ^ 6) ∧
    (∀ n : ℕ, 1 ≤ n → Even n →
      (a n : ℤ) = 5 * n - 11 * n ^ 2 + 10 * n ^ 3 - 4 * n ^ 4 + n ^ 5) ∧
    ∀ n : ℕ, Odd n →
      (a n : ℤ) = 9 - 10 * n - 4 * n ^ 2 + 10 * n ^ 3 - 4 * n ^ 4 + n ^ 5 := by
  sorry

end OMA.S_oeis_a246481
