import Mathlib

/-!
OEIS A288473 and A288476, on lengths of iterates of a binary substitution.
Sources: https://oeis.org/A288473 and https://oeis.org/A288476
-/

namespace OMA.S_oeis_a288473

def scan : List Bool → List Bool
  | [] => []
  | [false] => [false]
  | false :: false :: w => [false, true, false, true] ++ scan w
  | false :: true :: w => [false, false, true, true] ++ scan w
  | true :: w => [false, true, true] ++ scan w

def word : ℕ → List Bool
  | 0 => [false, false]
  | n + 1 => scan (word n)

def a288476 : ℕ → ℕ
  | 0 => 2
  | 1 => 4
  | 2 => 8
  | n + 3 => a288476 (n + 2) + 4 * a288476 (n + 1) - 2 * a288476 n

theorem main : ∀ n : ℕ, (word n).length = a288476 n := by
  sorry

end OMA.S_oeis_a288473
