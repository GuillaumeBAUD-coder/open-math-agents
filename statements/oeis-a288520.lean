import Mathlib

/-!
The map 00→0101, 10→010 sends the blocks 010, 0010 and 10 to B, ACC
and A respectively, where A=010, B=0010, C=10. The final 1 is fixed.
Sources: https://oeis.org/A288520 and https://oeis.org/A288523
-/

namespace OMA.S_oeis_a288520

def scan : List Bool → List Bool
  | [] => []
  | [x] => [x]
  | false :: false :: w => [false, true, false, true] ++ scan w
  | true :: false :: w => [false, true, false] ++ scan w
  | x :: true :: w => x :: scan (true :: w)

def word : ℕ → List Bool
  | 0 => [false, false]
  | n + 1 => scan (word n)

def a288523 : ℕ → ℕ
  | 0 => 2
  | 1 => 4
  | 2 => 5
  | 3 => 8
  | 4 => 11
  | n + 5 => a288523 (n + 4) + a288523 (n + 3) + a288523 (n + 2) - 2 * a288523 (n + 1)

theorem main : ∀ n : ℕ, (word n).length = a288523 n := by
  sorry

end OMA.S_oeis_a288520
