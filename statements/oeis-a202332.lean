import Mathlib

/-!
# OEIS A202332: Barker's generating function and recurrence

Source: https://oeis.org/A202332 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @marcusbuffett.

Entry A202332 (R. H. Hardin, Dec 17 2011), offset 1: Number of (n+1) X 6 binary arrays with consecutive windows of two bits considered as a binary number nondecreasing in every row and column.
Data: 64, 191, 478, 1052, 2102, 3896, 6800, 11299, ...
Formula section:
Empirical: a(n) = (1/360)*n^6 + (1/12)*n^5 + (17/18)*n^4 + (16/3)*n^3 + (5779/360)*n^2 + (295/12)*n + 17.
Conjectures from Colin Barker, May 28 2018: (Start)
G.f.: x*(64 - 257*x + 485*x^2 - 523*x^3 + 331*x^4 - 115*x^5 + 17*x^6) / (1 - x)^7.
a(n) = 7*a(n-1) - 21*a(n-2) + 35*a(n-3) - 35*a(n-4) + 21*a(n-5) - 7*a(n-6) + a(n-7) for n>7.
(End)

Formalization notes:
* An array is a function x : Fin (n + 1) → Fin 6 → Bool (false = 0, true = 1), x i j being the
  entry in row i and column j; row i is the bit string `List.ofFn (x i)`, read left to right, and
  column j is the bit string `List.ofFn fun i => x i j`, read top to bottom.
* `win b0 b1` is the window b0 b1 of 2 consecutive bits read as a binary number, the first
  bit being the high bit: 2 * b0 + b1. `windowsOK s` says that the windows of two
  consecutive bits of s, from first to last, are nondecreasing; it holds trivially for strings of
  at most 2 bits. `good x` asks this for every row and every column. This is the reading of the
  merged statements of the three-bit siblings A202455 - A202460, and the bit order and directions
  agree with the solutions shown in the entry.
* With this reading the definition reproduces every listed term of the entry: checked by a
  transfer-matrix evaluation of this exact definition for all listed terms, and by brute force
  for n = 1, 2.
* The g.f. is A(x) = Sum_{n >= 1} a(n) x^n (offset 1), stated as A(x) (1 - x)^7 = N(x) in Z[[x]],
  which is equivalent to the quotient form because 1 - x is a unit. The recurrence is stated in
  the integers for every n > 7, the range given in the entry.
* `main` is the conjunction of Barker's two conjectures; the empirical polynomial is not part of it.
-/

namespace OMA.S_oeis_a202332

open PowerSeries

/-- The window b0 b1 of 2 bits, read as a binary number with b0 the high bit. -/
def win (b0 b1 : Bool) : ℕ := 2 * b0.toNat + b1.toNat

/-- The consecutive windows of two bits of a bit string, read as binary numbers, are
nondecreasing. -/
def windowsOK : List Bool → Bool
  | b0 :: b1 :: b2 :: rest => decide (win b0 b1 ≤ win b1 b2) && windowsOK (b1 :: b2 :: rest)
  | _ => true

/-- An array with rows x i (each row a function Fin 6 → Bool): in every row and in every column the
consecutive windows of two bits, read as binary numbers, are nondecreasing. -/
def good {r : ℕ} (x : Fin r → Fin 6 → Bool) : Bool :=
  decide (∀ i, windowsOK (List.ofFn (x i)) = true) && decide (∀ j, windowsOK (List.ofFn fun i => x i j) = true)

/-- A202332(n): the number of good (n+1) X 6 binary arrays. -/
def a (n : ℕ) : ℕ := (Finset.univ.filter fun x : Fin (n + 1) → Fin 6 → Bool => good x = true).card

/-- Barker's conjectures: the g.f. and the recurrence. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 7 =
      X * (64 - 257 * X + 485 * X ^ 2 - 523 * X ^ 3 + 331 * X ^ 4 - 115 * X ^ 5 + 17 * X ^ 6) ∧
    ∀ n : ℕ, 7 < n → (a n : ℤ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) - 35 * a (n - 4) + 21 * a (n - 5) - 7 * a (n - 6) + a (n - 7) := by
  sorry

end OMA.S_oeis_a202332
