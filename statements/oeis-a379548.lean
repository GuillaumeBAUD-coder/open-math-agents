import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.Nat.Squarefree
import Mathlib.Order.Bounds.Basic

/-!
# OEIS A379548: the squarefree least-missing-prime permutation

Source: https://oeis.org/A379548 (David James Sycamore, December 25, 2024).

The sequence starts at 1. Each subsequent term is the least unused positive
squarefree multiple of the smallest prime not dividing the previous term.
The entry conjectures that this is a permutation of the squarefree positive
integers. The indexing below starts at zero, so `a 0 = 1` corresponds to
the entry's `a(1) = 1`. The whole previous history is excluded at each step.
Existence and the permutation property are both included in the target.
-/

namespace OMA.S_oeis_a379548

def Greedy (a : ℕ → ℕ) : Prop :=
  a 0 = 1 ∧ ∀ n, ∃ p : ℕ,
    IsLeast {q : ℕ | q.Prime ∧ ¬ q ∣ a n} p ∧
    IsLeast {m : ℕ | 0 < m ∧ Squarefree m ∧ p ∣ m ∧ ∀ i ≤ n, a i ≠ m}
      (a (n+1))

theorem main :
    (∃ a, Greedy a) ∧ ∀ a, Greedy a →
      Function.Injective a ∧ Set.range a = {m : ℕ | 0 < m ∧ Squarefree m} := by
  sorry

end OMA.S_oeis_a379548
