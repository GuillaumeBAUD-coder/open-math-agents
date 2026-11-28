import OMAStatements.S_oeis_a215095
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.NormNum

/-!
Ratushnyak defined the greedy sequence and Scambler proposed its generating
function. The proof locates each threshold between consecutive Jacobsthal
numbers and shows that the greedy construction skips none of them.
-/

open OMA.S_oeis_a215095

namespace OMA.A215095

private theorem jacStep (n : ℕ) : jac (n+2) = jac (n+1) + 2*jac n := rfl

private theorem jacMono : Monotone jac := by
  apply monotone_nat_of_le_succ
  intro n
  cases n with
  | zero => decide
  | succ n => rw [show n.succ + 1 = n+2 by omega, jacStep]; omega

/-- The two bounds identify the first permissible Jacobsthal number.
The explicit candidate also proves that the minimizing set is nonempty. -/
private theorem nextInGap (j x y : ℕ) (lo : jac j ≤ x + y) (hi : x + y < jac (j+1)) :
    y < nextTerm x y ∧ nextTerm x y + x = jac (j+1) := by
  let S := {k : ℕ | y < k ∧ ∃ i : ℕ, k + x = jac i}
  have hmem : jac (j+1) - x ∈ S := ⟨by omega, j+1, by omega⟩
  have upper : sInf S ≤ jac (j+1) - x := Nat.sInf_le hmem
  obtain ⟨hy, i, he⟩ := Nat.sInf_mem (show S.Nonempty from ⟨_, hmem⟩)
  have hj : j < i := by
    by_contra! hir
    have := jacMono hir
    omega
  have lower := jacMono (show j + 1 ≤ i by omega)
  change y < sInf S ∧ sInf S + x = jac (j+1)
  exact ⟨hy, by omega⟩

/-- Two adjacent greedy terms straddle the threshold for the next choice. -/
private theorem bounds (n : ℕ) :
    a n ≤ a (n+1) ∧ a (n+1) ≤ jac (n+2) ∧
    jac (n+2) ≤ a n + a (n+1) ∧ a n + a (n+1) < jac (n+3) := by
  induction n with
  | zero => change 0 ≤ 1 ∧ 1 ≤ 1 ∧ 1 ≤ 0+1 ∧ 0+1 < 3; decide
  | succ n ih =>
    obtain ⟨hxy, hy, lo, hi⟩ := ih
    have step := nextInGap (n+2) (a n) (a (n+1)) lo hi
    change a (n+1) < a (n+2) ∧ a (n+2) + a n = jac (n+3) at step
    have pos : 1 ≤ jac (n+2) := jacMono (show 1 ≤ n+2 by omega)
    have jump : jac (n+4) = jac (n+3) + 2*jac (n+2) := jacStep (n+2)
    change a (n+1) ≤ a (n+2) ∧ a (n+2) ≤ jac (n+3) ∧
      jac (n+3) ≤ a (n+1) + a (n+2) ∧ a (n+1) + a (n+2) < jac (n+4)
    omega

theorem twoApart (n : ℕ) : a (n+2) + a n = jac (n+3) := by
  obtain ⟨_, _, lo, hi⟩ := bounds n
  exact (nextInGap (n+2) (a n) (a (n+1)) lo hi).2

theorem recurrence (n : ℕ) :
    a (n+4) = a (n+3) + a (n+2) + a (n+1) + 2 * a n := by
  have h0 := twoApart n
  have h1 : a (n+3) + a (n+1) = jac (n+4) := twoApart (n+1)
  have h2 : a (n+4) + a (n+2) = jac (n+5) := twoApart (n+2)
  have hj : jac (n+5) = jac (n+4) + 2*jac (n+3) := jacStep (n+3)
  omega

end OMA.A215095

theorem OMA.solution : type_of% @OMA.S_oeis_a215095.main := by
  intro n
  have h0 : a 0 = 0 := rfl
  have h1 : a 1 = 1 := rfl
  have h2 := OMA.A215095.twoApart 0
  have h3 := OMA.A215095.twoApart 1
  change a 2 + a 0 = 3 at h2
  change a 3 + a 1 = 5 at h3
  have firstTwo : a 2 = 3 := by omega
  have firstThree : a 3 = 4 := by omega
  rcases n with _ | _ | _ | _ | n
  · norm_num [denominatorProduct, h0]
  · norm_num [denominatorProduct, h0, h1]
  · norm_num [denominatorProduct, h0, h1, firstTwo]
  · norm_num [denominatorProduct, h0, h1, firstTwo, firstThree]
  · have h := OMA.A215095.recurrence n
    change (a (n+4):ℤ) - a (n+3) - a (n+2) - a (n+1) - 2*a n =
      (if n+4 = 1 then 1 else if n+4 = 2 then 2 else 0)
    rw [if_neg (by omega : n+4 ≠ 1), if_neg (by omega : n+4 ≠ 2)]
    omega
