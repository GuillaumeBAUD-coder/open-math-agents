import Mathlib

/-!
# The iterate lengths in OEIS A288665

Source: https://oeis.org/A288665 and https://oeis.org/A288668
The words and the conjecture are due to Clark Kimberling.
A288668's initial values 2, 4, 5 at indices 0, 1, 2 are given by its
term table, generating function and LinearRecurrence program.
-/

namespace OMA.S_oeis_a288665

/-- A single left-to-right replacement pass. Unmatched characters are copied. -/
def scan : List Bool → List Bool
  | [] => []
  | [x] => [x]
  | false :: false :: w => [false, true, true, false] ++ scan w
  | true :: false :: w => [false, false, false] ++ scan w
  | x :: true :: w => x :: scan (true :: w)

def word : ℕ → List Bool
  | 0 => [false, false]
  | n + 1 => scan (word n)

def a288668 : ℕ → ℕ
  | 0 => 2
  | 1 => 4
  | 2 => 5
  | n + 3 => a288668 (n + 1) + 2 * a288668 n

theorem main : ∀ n : ℕ, (word n).length = a288668 n := by
  sorry

end OMA.S_oeis_a288665
