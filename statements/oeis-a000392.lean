import Mathlib

/-!
# OEIS A000392

Source: https://oeis.org/A000392 (John W. Layman, 2007; index corrected in 2014).
Credit: @stevenczp
-/

namespace OMA.S_oeis_a000392

/-- 从单元素集合开始扩张。有限集的并集自动消除重复元素。 -/
def rounds : ℕ → Finset ℕ
  | 0 => {1}
  | n + 1 =>
    let s := rounds n
    s ∪ s.image (2 * ·) ∪ s.image (3 * ·)

/-- OEIS 从第一轮开始编号。零处取空集，只为给出自然数上的全函数。 -/
def S : ℕ → Finset ℕ
  | 0 => ∅
  | n + 1 => rounds n

theorem main : ∀ n : ℕ, 1 ≤ n →
    (∑ x ∈ S n, x) = Nat.stirlingSecond (n + 2) 3 := by
  sorry

end OMA.S_oeis_a000392
