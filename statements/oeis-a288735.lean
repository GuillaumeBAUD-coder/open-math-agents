import Mathlib

/-!
# OEIS A288735, positions of ones in A288733

Sources: https://oeis.org/A288735 and https://oeis.org/A288733.
OEIS data are licensed under CC BY-SA 4.0.

Starting at 00, a pass scans from the left and replaces each nonoverlapping
00 by 1000 and each 10 by 01. Other letters are copied. A288733 is the
limit along the iterates numbered 1 modulo 4. In that limiting word the
positions of the ones are indexed from 1 and counted from 1. The nth
position in the limit is the eventual nth position on this subsequence.
The conjecture asserts a real limit and strict bounds for every positive
index. The proof file checks the first eight listed positions.
-/

namespace OMA.S_oeis_a288735

open Filter Topology

def step : List Bool → List Bool
  | false :: false :: xs => true :: false :: false :: false :: step xs
  | true :: false :: xs => false :: true :: step xs
  | b :: xs => b :: step xs
  | [] => []

def word : ℕ → List Bool
  | 0 => [false, false]
  | t + 1 => step (word t)

def places (b : Bool) : ℕ → List Bool → List ℕ
  | _, [] => []
  | p, c :: cs =>
    if c = b then p :: places b (p + 1) cs else places b (p + 1) cs

def isPosition (n p : ℕ) : Prop :=
  ∀ᶠ t : ℕ in atTop, (places true 1 (word (4 * t + 1)))[n - 1]? = some p

theorem main : ∃ a : ℕ → ℕ,
    (∀ n, 1 ≤ n → isPosition n (a n)) ∧
    Tendsto (fun n : ℕ => (a n : ℝ) / n) atTop (𝓝 2) ∧
    (∀ n : ℕ, 1 ≤ n → 0 < 2 - (a n : ℝ) / n ∧
      2 - (a n : ℝ) / n < 1) := by
  sorry

end OMA.S_oeis_a288735
