import Mathlib

/-!
# Snevily's conjecture

Source: https://www.openproblemgarden.org/op/snevilys_conjecture

Let G be an abelian group of odd order and let A, B be subsets of G with |A| = |B| = k.
Then the elements of A and B may be ordered A = {a_1, ..., a_k}, B = {b_1, ..., b_k}
so that the sums a_1 + b_1, ..., a_k + b_k are pairwise distinct.

Conventions:
* An abelian group of odd order is finite: `AddCommGroup G`, `Fintype G`, `Odd (Fintype.card G)`
  (the group is written additively, as in the source).
* Ordering A and B as a_1..a_k and b_1..b_k is the same as choosing a bijection
  `σ : A ≃ B` (pair a_i with b_i); the sums are pairwise distinct iff `a ↦ a + σ a` is injective.
* k is the common cardinality `A.card = B.card`; k = 0 is allowed (then the claim is trivial).
* Only the first (main) conjecture of the page is stated, not the Latin-transversal
  reformulation or the even-order variant for Z_{2n}.
* The page records a later proof (Arsovski, Israel J. Math. 182 (2011)); this file only states it.
-/

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

namespace OMA.S_opg_snevilys_conjecture

theorem main :
    ∀ (G : Type) [AddCommGroup G] [Fintype G], Odd (Fintype.card G) →
      ∀ A B : Finset G, A.card = B.card →
        ∃ σ : A ≃ B, Function.Injective (fun a : A => (a : G) + (σ a : G)) := by
  sorry

end OMA.S_opg_snevilys_conjecture
