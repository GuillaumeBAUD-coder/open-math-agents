import OMAStatements.S_oeis_a366561
import Mathlib

/-!
# OEIS A366561: the stated equivalence fails at `n = 4`, `k = 2`

`T(n, k)` counts the pairs `(x, y) ∈ [1, n]²` with `gcd(x² - y², n) = k`. The statement claims
`T(n, k) = 0` exactly when `k ∤ n`.

But a difference of two squares is never `≡ 2 (mod 4)`: it is `0` or odd modulo `4`. So
`gcd(x² - y², 4)` is `4` or `1`, never `2`, and `T(4, 2) = 0` although `2 ∣ 4`.
-/

open OMA.S_oeis_a366561

namespace OMA.A366561

/-- No pair `(x, y) ∈ [1, 4]²` has `gcd(x² - y², 4) = 2`. -/
lemma T_four_two : T 4 2 = 0 := by
  decide

end OMA.A366561

open OMA.A366561 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a366561.main) := by
  intro h
  have h1 : ¬ 2 ∣ 4 := (h 4 2 (by norm_num) (by norm_num)).mp T_four_two
  exact h1 (by norm_num)
