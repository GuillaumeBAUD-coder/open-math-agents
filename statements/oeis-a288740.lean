import Mathlib.Data.Real.Basic

/-!
# Positions of digit 1 in phase 2 of the two-pattern replacement

Source: Clark Kimberling, OEIS A288740 and A288736 (CC BY-SA 4.0).
Scan from left to right, replacing disjoint 00 and 10 pairs as specified
in the source. Each fourth iterate extends the preceding one of that phase.
The one-based occurrence relation gives the selected digit’s rank and its position.
The first conjunct expresses the proposed limit in epsilon form.
Credit: @jatin6
-/

namespace OMA.S_oeis_a288740

def scan : List Bool → List Bool
  | [] => []
  | [b] => [b]
  | false :: false :: t => true :: false :: false :: false :: scan t
  | true :: false :: t => false :: true :: scan t
  | b :: true :: t => b :: scan (true :: t)

def word : ℕ → List Bool
  | 0 => [false,false]
  | k+1 => scan (word k)

def occurrence (n p : ℕ) : Prop :=
  ∃ (k : ℕ) (u v : List Bool), word (4*k + 2) = u ++ true :: v ∧
    n = u.count true + 1 ∧ p = u.length + 1

theorem main :
    (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n p : ℕ, N ≤ n → occurrence n p →
      |(p:ℝ)/n - 2| < ε) ∧
    (∀ n p : ℕ, occurrence n p → -(2/3) < 2 - (p:ℝ)/n ∧ 2 - (p:ℝ)/n < 1/2) := by
  sorry

end OMA.S_oeis_a288740
