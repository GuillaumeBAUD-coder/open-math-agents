import Mathlib

/-!
# OEIS A288307, positions of zeros in A288306

Sources: https://oeis.org/A288307 and https://oeis.org/A288306.
OEIS data are licensed under CC BY-SA 4.0.

Starting at 00, a pass scans from the left and replaces each nonoverlapping
00 by 0010 and each 1 by 110. Other letters are copied. The positions
of the zeros in the limiting word are indexed from 1 and counted from 1.
The nth position in the limit is the eventual nth position in these finite
words. The conjecture gives two strict bounds on a real quotient for every
positive index. The proof file checks the first eight positions.
-/

namespace OMA.S_oeis_a288307

open Filter Topology

def step : List Bool → List Bool
  | false :: false :: xs => false :: false :: true :: false :: step xs
  | true :: xs => true :: true :: false :: step xs
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
  ∀ᶠ t : ℕ in atTop, (places false 1 (word t))[n - 1]? = some p

theorem main : ∃ a : ℕ → ℕ,
    (∀ n, 1 ≤ n → isPosition n (a n)) ∧
    (∀ n : ℕ, 1 ≤ n → -1 < 2 - (a n : ℝ) / n ∧
      2 - (a n : ℝ) / n < 1) := by
  sorry

end OMA.S_oeis_a288307
