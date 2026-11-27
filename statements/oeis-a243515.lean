import Mathlib.Data.Fin.Basic

/-!
# Counting seven-symbol words avoiding two consecutive patterns

Source: https://oeis.org/A243515
Credit: @jatin6

R. H. Hardin defined the words. Colin Barker proposed both formulas in 2018.
-/

namespace OMA.S_oeis_a243515

/-- First appearances must be in order. After two distinct letters, the
next letter must differ from both. -/
def letters (hi prev last : Fin 7) : List (Fin 7) :=
  (List.finRange 7).filter fun x =>
    decide (x.val ≤ hi.val + 1 ∧ (prev = last ∨ (x ≠ prev ∧ x ≠ last)))

/-- Update the greatest symbol introduced so far. -/
def advance (hi x : Fin 7) : Fin 7 := if hi < x then x else hi

/-- List every possible remaining string of the requested length, retaining
the largest letter seen and the last two letters of the prefix. -/
def continuations : ℕ → Fin 7 → Fin 7 → Fin 7 → List (List (Fin 7))
  | 0, _, _, _ => [[]]
  | r + 1, hi, prev, last => (letters hi prev last).flatMap fun x =>
      (continuations r (advance hi x) last x).map (x :: ·)

/-- The first letter is necessarily zero. Before the second letter, using
two equal previous letters imposes no pattern restriction. -/
def count (n : ℕ) : ℕ := (continuations (n + 1) 0 0 0).length

/-- Coefficients of the ordinary generating function, starting at degree one. -/
def series : ℕ → ℤ
  | 0 => 0
  | n + 1 => count (n + 1)

/-- Coefficients after multiplying a series by the polynomial 1 - c X. -/
def mulLinear (c : ℤ) (a : ℕ → ℤ) : ℕ → ℤ
  | 0 => a 0
  | n + 1 => a (n + 1) - c * a n

/-- Coefficients of X (3 - 31 X + 106 X² - 141 X³ + 60 X⁴). -/
def numerator : ℕ → ℤ
  | 1 => 3
  | 2 => -31
  | 3 => 106
  | 4 => -141
  | 5 => 60
  | _ => 0

/-- Barker's closed form and his generating function after multiplication
by its denominator (1-X)² (1-2X) (1-3X) (1-5X). -/
theorem main :
    (∀ n : ℕ, 1 ≤ n → 96 * count n = 147 + 2 ^ (5 + n) + 4 * 3 ^ (1 + n) + 5 ^ n + 36 * n) ∧
    (∀ n : ℕ, mulLinear 1 (mulLinear 1 (mulLinear 2 (mulLinear 3 (mulLinear 5 series)))) n =
      numerator n) := by
  sorry

end OMA.S_oeis_a243515
