import Mathlib

/-!
# OEIS A283794, positions of ones in A288375

Sources: https://oeis.org/A283794 and https://oeis.org/A288375.
OEIS data are licensed under CC BY-SA 4.0.

Starting at 00, a pass scans from the left and replaces each nonoverlapping
00 by 1000 and each 10 by 1001. Other letters are copied. The positions
of the ones in the limiting word are indexed from 1 and counted from 1.
The nth position in the limit is the eventual nth position in these finite
words. The conjecture asserts both a real limit and strict bounds for every
positive index. The proof file checks the first eight positions.
-/

namespace OMA.S_oeis_a283794

open Filter Topology

def step : List Bool → List Bool
  | false :: false :: xs => true :: false :: false :: false :: step xs
  | true :: false :: xs => true :: false :: false :: true :: step xs
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
  ∀ᶠ t : ℕ in atTop, (places true 1 (word t))[n - 1]? = some p

theorem main : ∃ a : ℕ → ℕ,
    (∀ n, 1 ≤ n → isPosition n (a n)) ∧
    Tendsto (fun n : ℕ => (a n : ℝ) / n) atTop (𝓝 2) ∧
    (∀ n : ℕ, 1 ≤ n → -(1 / 4 : ℝ) < 2 - (a n : ℝ) / n ∧
      2 - (a n : ℝ) / n < 1) := by
  sorry

end OMA.S_oeis_a283794
