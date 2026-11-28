import Mathlib

/-!
# OEIS A183907: Barker's conjectures

Source: https://oeis.org/A183907 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A183907 (R. H. Hardin, Jan 07 2011), offset 1: Number of nondecreasing arrangements of n+2 numbers in 0..4 with each number being the sum mod 5 of two others.
Formula section:
Empirical: a(n) = (1/24)*n^4 + (3/4)*n^3 + (119/24)*n^2 - (95/4)*n + 23 for n>1.
Conjectures from Colin Barker, Apr 05 2018: (Start)
G.f.: x*(1 - 3*x + 20*x^2 - 24*x^3 + 3*x^4 + 4*x^5) / (1 - x)^5.
a(n) = 5*a(n-1) - 10*a(n-2) + 10*a(n-3) - 5*a(n-4) + a(n-5) for n>6.
(End)

Formalization notes:
* An arrangement of n + 2 numbers in 0..4 in nondecreasing order is a monotone function
  x : Fin (n + 2) → Fin 5. The addition of Fin 5 is addition mod 5.
* "Each number being the sum mod 5 of two others": every position i has a set T of
  2 other positions (i ∉ T) whose entries sum to x i mod 5.
* The statement is Barker's conjectures, the problem as stated on lefttosolve.com: the
  generating function and the recurrence.
* The definition gives a(0) = 0 (no number has enough others), so the generating function is
  A(x) = Sum_{n >= 0} a(n) x^n, and the identity is stated as A(x) (1 - x)^5 = N(x) in the
  formal power series ring over the integers.
* Controls proved in the proof file: the definition gives 1, 2, 20, 66, 148, 275, 457, 705, 1031, 1448, 1970, 2612 for n = 1..12,
  the entry's first terms.
-/

namespace OMA.S_oeis_a183907

open Finset

/-- An arrangement of N numbers in 0..4 (Fin 5, whose addition is mod 5) in
nondecreasing order where each entry is the sum of the entries at 2 other positions. -/
def Good {N : ℕ} (x : Fin N → Fin 5) : Prop :=
  Monotone x ∧ ∀ i, ∃ T : Finset (Fin N), i ∉ T ∧ T.card = 2 ∧ ∑ j ∈ T, x j = x i

instance {N : ℕ} : DecidablePred (Good (N := N)) := fun x => by unfold Good; infer_instance

/-- A183907(n): the good arrangements of n + 2 numbers. -/
def a (n : ℕ) : ℕ := (univ.filter (fun x : Fin (n + 2) → Fin 5 => Good x)).card

/-- The problem as the site states it. -/
theorem main :
    PowerSeries.mk (fun n => (a n : ℤ)) * (1 - PowerSeries.X) ^ 5 = PowerSeries.X * (1 - 3 * PowerSeries.X + 20 * PowerSeries.X ^ 2 - 24 * PowerSeries.X ^ 3 + 3 * PowerSeries.X ^ 4 + 4 * PowerSeries.X ^ 5) ∧
    (∀ n : ℕ, 6 < n → (a n : ℤ) = 5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) - 5 * a (n - 4) + a (n - 5)) := by
  sorry

end OMA.S_oeis_a183907
