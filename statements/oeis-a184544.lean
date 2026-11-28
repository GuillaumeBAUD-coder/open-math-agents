import Mathlib

/-!
# OEIS A184544: the number of (n+2) X 7 binary arrays in which every 3 X 3 subblock has its rows and its columns in lexicographically nondecreasing order satisfies the conjectured g.f., linear recurrence and empirical polynomial formula of the entry

Source: https://oeis.org/A184544 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with claude-code (model claude-fable-5-2), submitted by @VestigeClub.

Entry: A184544: Number of (n+2) X 7 binary arrays with each 3 X 3 subblock having rows and columns in lexicographically nondecreasing order.
Offset 1; data 309, 792, 1627, 3024, 5313, 8989, 14767, 23648, ...
The conjecture, as the entry gives it:
  Conjectures from Colin Barker, Apr 13 2018: G.f.: x*(309 - 1680*x + 3943*x^2 - 5120*x^3 + 3955*x^4 - 1819*x^5 + 465*x^6 - 52*x^7) / (1 - x)^8. a(n) = 8*a(n-1) - 28*a(n-2) + 56*a(n-3) - 70*a(n-4) + 56*a(n-5) - 28*a(n-6) + 8*a(n-7) - a(n-8) for n>8.
The entry's other formula (R. H. Hardin), also stated here:
  Empirical: a(n) = (1/5040)*n^7 + (1/120)*n^6 + (53/360)*n^5 + (17/12)*n^4 + (5767/720)*n^3 + (3063/40)*n^2 + (11959/70)*n + 52.

Formalization notes:
* An array is a map x : Fin (n+2) → Fin 7 → Fin 2 (row i, column j, entries 0 and 1). `a n` counts the
  arrays with n+2 rows and 7 columns that satisfy the condition, so `a n` is the entry's a(n) for n ≥ 1
  (offset 1). `a 0` (two rows, no 3 X 3 subblock) is not a term of the entry and none of the three
  claims below uses it.
* A 3 X 3 subblock is made of three consecutive rows i, i+1, i+2 and three consecutive columns j, j+1, j+2.
  Its rows, read left to right, must be lexicographically nondecreasing from top to bottom, and its
  columns, read top to bottom, lexicographically nondecreasing from left to right (`Lex3` is the
  lexicographic order ≤ on triples of bits, with 0 < 1). Nondecreasing: equal neighbours are allowed.
* The recurrence is stated for every n > 8 (written 9 ≤ n), over ℤ because of the subtractions.
* The g.f. is stated as an identity of formal power series over ℚ for Sum_{n ≥ 1} a(n) x^n: the
  coefficient of x^0 is 0 (offset 1), and division by (1 - x)^8 is multiplication by its inverse.
* The empirical formula is stated for every n ≥ 1, over ℚ.
* The proof file proves the first eight listed terms a(1..8) = 309, 792, 1627, 3024, 5313, 8989, 14767,
  23648 from this definition as controls.
-/

namespace OMA.S_oeis_a184544

/-- Lexicographic order on triples of bits: (a, b, c) ≤ (a', b', c'). -/
def Lex3 (a b c a' b' c' : Fin 2) : Prop :=
  a < a' ∨ (a = a' ∧ (b < b' ∨ (b = b' ∧ c ≤ c')))

/-- Three consecutive rows u, v, w (top to bottom): in each 3 X 3 subblock (columns j, j+1, j+2) the three
rows are lexicographically nondecreasing from top to bottom and the three columns from left to right. -/
def TriOK (u v w : Fin 7 → Fin 2) : Prop :=
  ∀ j j' j'' : Fin 7, (j' : ℕ) = j + 1 → (j'' : ℕ) = j' + 1 →
    Lex3 (u j) (u j') (u j'') (v j) (v j') (v j'') ∧ Lex3 (v j) (v j') (v j'') (w j) (w j') (w j'') ∧
    Lex3 (u j) (v j) (w j) (u j') (v j') (w j') ∧ Lex3 (u j') (v j') (w j') (u j'') (v j'') (w j'')

/-- The condition on an array with L rows: every 3 X 3 subblock (rows i, i+1, i+2) has lexicographically
nondecreasing rows and columns. -/
def Good {L : ℕ} (x : Fin L → Fin 7 → Fin 2) : Prop :=
  ∀ i i' i'' : Fin L, (i' : ℕ) = i + 1 → (i'' : ℕ) = i' + 1 → TriOK (x i) (x i') (x i'')

/-- a(n): the number of such (n+2) X 7 arrays. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {x : Fin (n + 2) → Fin 7 → Fin 2 // Good x}

/-- The conjectured g.f.
x*(309 - 1680*x + 3943*x^2 - 5120*x^3 + 3955*x^4 - 1819*x^5 + 465*x^6 - 52*x^7) / (1 - x)^8. -/
noncomputable def G : PowerSeries ℚ :=
  (PowerSeries.X * (309 - 1680 * PowerSeries.X + 3943 * PowerSeries.X ^ 2 - 5120 * PowerSeries.X ^ 3 + 3955 * PowerSeries.X ^ 4 - 1819 * PowerSeries.X ^ 5 + 465 * PowerSeries.X ^ 6 - 52 * PowerSeries.X ^ 7)) * ((1 - PowerSeries.X) ^ 8)⁻¹

/-- The recurrence (n > 8), the g.f. and the empirical polynomial formula (n ≥ 1). -/
theorem main :
    (∀ n : ℕ, 9 ≤ n → (a n : ℤ) = 8 * (a (n - 1) : ℤ) - 28 * (a (n - 2) : ℤ) + 56 * (a (n - 3) : ℤ) - 70 * (a (n - 4) : ℤ) + 56 * (a (n - 5) : ℤ) - 28 * (a (n - 6) : ℤ) + 8 * (a (n - 7) : ℤ) - (a (n - 8) : ℤ)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = G ∧
    (∀ n : ℕ, 1 ≤ n → (a n : ℚ) = (1 / 5040) * (n : ℚ) ^ 7 + (1 / 120) * (n : ℚ) ^ 6 + (53 / 360) * (n : ℚ) ^ 5 + (17 / 12) * (n : ℚ) ^ 4 + (5767 / 720) * (n : ℚ) ^ 3 + (3063 / 40) * (n : ℚ) ^ 2 + (11959 / 70) * (n : ℚ) + 52) := by
  sorry

end OMA.S_oeis_a184544
