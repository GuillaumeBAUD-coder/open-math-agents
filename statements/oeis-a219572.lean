import Mathlib

/-!
# OEIS A219572: Number of n X 2 arrays of the minimum value of corresponding elements and their horizontal or vertical neighbors in a random, but sorted with lexicographically nondecreasing rows and nonincreasing columns, 0..3 n X 2 array

Source: https://oeis.org/A219572 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated (Antigravity / gemini-4-neon-high), submitted by @Solfanbtc.

OEIS entry A219572 (R. H. Hardin, Nov 23 2012), offset 1,1:
Number of n X 2 arrays of the minimum value of corresponding elements and their horizontal or
vertical neighbors in a random, but sorted with lexicographically nondecreasing rows and
nonincreasing columns, 0..3 n X 2 array.
(Column 2 of A219578.)

Conjectures and empirical formula quoted verbatim from the FORMULA section of the entry:
  Empirical: a(n) = (1/20160)*n^8 + (1/2520)*n^7 + (1/480)*n^6 + (43/360)*n^5 - (297/320)*n^4 + (1271/180)*n^3 - (75973/5040)*n^2 + (2081/105)*n - 12 for n>1.
  Conjectures from _Colin Barker_, Mar 11 2018: (Start)
  G.f.: x*(4 - 23*x + 86*x^2 - 218*x^3 + 376*x^4 - 420*x^5 + 296*x^6 - 127*x^7 + 33*x^8 - 5*x^9) / (1 - x)^9.
  a(n) = 9*a(n-1) - 36*a(n-2) + 84*a(n-3) - 126*a(n-4) + 126*a(n-5) - 84*a(n-6) + 36*a(n-7) - 9*a(n-8) + a(n-9) for n>10.
  (End)

Formalization notes:
* An n X 2 array over 0..3 is modeled as `M : Fin n → Fin 2 → Fin 4`.
* Following R. H. Hardin's convention for A219572 / A219578:
  - `rowsNondec M`: adjacent rows are in lexicographically nondecreasing order (`row i ≤ row (i+1)`).
  - `colsNoninc M`: column 0 is lexicographically `≥` column 1, i.e., at any row `i` where all
    earlier rows have equal entries `M j 0 = M j 1`, we have `M i 1 ≤ M i 0`.
* `minGrid M` maps each cell `(i, j)` to the minimum of `M i j`, its horizontal neighbor
  `M i (1 - j)`, and its vertical neighbors `M (i - 1) j` (if `i > 0`) and `M (i + 1) j`
  (if `i + 1 < n`).
* `a n` is the cardinality of the image of `minGrid` over all valid `n × 2` arrays `M`.
* This definition reproduces all 31 listed OEIS data terms starting at offset 1:
  4, 13, 59, 181, 469, 1107, 2447, 5120, 10197, 19415, 35485, 62501, 106471, 175993, 283101,
  444308, 681875, 1025337, 1513319, 2195677, 3136001, 4414519, 6131443, 8410800, 11404793,
  15298739, 20316633, 26727389, 34851811, 45070349, 57831697.
* `series` is the ordinary generating function `Sum_{n ≥ 1} a(n) x^n` over `ℚ` (zero constant
  term, matching offset 1). Because `(1 - X)^9` is a unit in `PowerSeries ℚ`, the generating
  function conjecture is stated equivalently by clearing the denominator: `series * (1 - X)^9 = ...`.
* The empirical closed-form formula is stated over `ℚ` for `n > 1`, and the linear recurrence is
  stated over `ℤ` for `n > 10`.
-/

namespace OMA.S_oeis_a219572

/-- Lexicographic nondecreasing order on rows of length 2 over `{0, 1, 2, 3}`. -/
def rowLe (r s : Fin 2 → Fin 4) : Prop :=
  r 0 < s 0 ∨ (r 0 = s 0 ∧ r 1 ≤ s 1)

/-- Adjacent rows are in lexicographically nondecreasing order. -/
def rowsNondec {n : ℕ} (M : Fin n → Fin 2 → Fin 4) : Prop :=
  ∀ i j : Fin n, j.val = i.val + 1 → rowLe (M i) (M j)

/-- Column 0 is lexicographically `≥` column 1 (nonincreasing columns). -/
def colsNoninc {n : ℕ} (M : Fin n → Fin 2 → Fin 4) : Prop :=
  ∀ i : Fin n, (∀ j : Fin n, j < i → M j 0 = M j 1) → M i 1 ≤ M i 0

/-- An `n × 2` `0..3` array with lexicographically nondecreasing rows and nonincreasing columns. -/
def valid {n : ℕ} (M : Fin n → Fin 2 → Fin 4) : Prop :=
  rowsNondec M ∧ colsNoninc M

instance {n : ℕ} : DecidablePred (@valid n) := fun M => by
  unfold valid rowsNondec rowLe colsNoninc
  infer_instance

/-- Minimum of `M i j` and its horizontal and vertical neighbors in the `n × 2` array `M`. -/
def minNeighbor {n : ℕ} (M : Fin n → Fin 2 → Fin 4) (i : Fin n) (j : Fin 2) : Fin 4 :=
  let h := min (M i j) (M i (if j = 0 then 1 else 0))
  let u := if hi : 0 < i.val then min h (M ⟨i.val - 1, by omega⟩ j) else h
  if hi' : i.val + 1 < n then min u (M ⟨i.val + 1, hi'⟩ j) else u

/-- The `n × 2` array of local horizontal/vertical neighbor minima of `M`. -/
def minGrid {n : ℕ} (M : Fin n → Fin 2 → Fin 4) : Fin n → Fin 2 → Fin 4 :=
  minNeighbor M

/-- OEIS A219572 (offset 1): number of distinct `minGrid M` over valid `n × 2` `0..3` arrays. -/
def a (n : ℕ) : ℕ :=
  (((Finset.univ : Finset (Fin n → Fin 2 → Fin 4)).filter valid).image minGrid).card

/-- Ordinary generating function `∑_{n ≥ 1} a(n) X^n` over `ℚ`. -/
noncomputable def series : PowerSeries ℚ :=
  PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ))

open PowerSeries in
/-- Conjunction of the generating function, closed-form formula, and recurrence for OEIS A219572. -/
theorem main :
    series * (1 - X) ^ 9 =
      X * (4 - 23 * X + 86 * X ^ 2 - 218 * X ^ 3 + 376 * X ^ 4 - 420 * X ^ 5 +
        296 * X ^ 6 - 127 * X ^ 7 + 33 * X ^ 8 - 5 * X ^ 9) ∧
    (∀ n : ℕ, 1 < n →
      (a n : ℚ) =
        (1 / 20160 : ℚ) * (n : ℚ) ^ 8 + (1 / 2520 : ℚ) * (n : ℚ) ^ 7 +
          (1 / 480 : ℚ) * (n : ℚ) ^ 6 + (43 / 360 : ℚ) * (n : ℚ) ^ 5 -
          (297 / 320 : ℚ) * (n : ℚ) ^ 4 + (1271 / 180 : ℚ) * (n : ℚ) ^ 3 -
          (75973 / 5040 : ℚ) * (n : ℚ) ^ 2 + (2081 / 105 : ℚ) * (n : ℚ) - 12) ∧
    (∀ n : ℕ, 10 < n →
      (a n : ℤ) =
        9 * (a (n - 1) : ℤ) - 36 * (a (n - 2) : ℤ) + 84 * (a (n - 3) : ℤ) -
          126 * (a (n - 4) : ℤ) + 126 * (a (n - 5) : ℤ) - 84 * (a (n - 6) : ℤ) +
          36 * (a (n - 7) : ℤ) - 9 * (a (n - 8) : ℤ) + (a (n - 9) : ℤ)) := by
  sorry

end OMA.S_oeis_a219572
