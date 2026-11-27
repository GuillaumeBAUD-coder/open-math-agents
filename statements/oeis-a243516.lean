import Mathlib.Data.Fin.Basic

/-!
# Counting eight-symbol words avoiding two consecutive patterns

Source: https://oeis.org/A243516
Credit: @jatin6

R. H. Hardin defined the words. Colin Barker proposed both formulas in 2018.
-/

namespace OMA.S_oeis_a243516

/-- First appearances must be in order. After two distinct letters, the
next letter must differ from both. -/
def letters (hi prev last : Fin 8) : List (Fin 8) :=
  (List.finRange 8).filter fun x =>
    decide (x.val ≤ hi.val + 1 ∧ (prev = last ∨ (x ≠ prev ∧ x ≠ last)))

/-- Update the greatest symbol introduced so far. -/
def advance (hi x : Fin 8) : Fin 8 := if hi < x then x else hi

/-- List every possible remaining string of the requested length, retaining
the largest letter seen and the last two letters of the prefix. -/
def continuations : ℕ → Fin 8 → Fin 8 → Fin 8 → List (List (Fin 8))
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

/-- Coefficients of X (3 - 46 X + 258 X² - 655 X³ + 739 X⁴ - 288 X⁵). -/
def numerator : ℕ → ℤ
  | 1 => 3
  | 2 => -46
  | 3 => 258
  | 4 => -655
  | 5 => 739
  | 6 => -288
  | _ => 0

/-- Barker's closed form and his generating function after multiplication
by its denominator (1-X)² (1-2X) (1-3X) (1-4X) (1-6X). -/
theorem main :
    (∀ n : ℕ, 1 ≤ n → 1800 * count n = 2722 + 675 * 2 ^ n + 25 * 2 ^ (1 + 2*n) +
      50 * 3 ^ (1+n) + 2^n * 3^(1+n) + 660*n) ∧
    (∀ n : ℕ, mulLinear 1 (mulLinear 1 (mulLinear 2 (mulLinear 3 (mulLinear 4 (mulLinear 6 series))))) n =
      numerator n) := by
  sorry

end OMA.S_oeis_a243516
