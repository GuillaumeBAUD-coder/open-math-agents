import Mathlib

/-!
# Snevily's conjecture

Source: https://www.openproblemgarden.org/op/snevilys_conjecture
Credit: @majdi19

Conjecture (Snevily). Let `G` be an abelian group of odd order and let `A, B ⊆ G` satisfy
`|A| = |B| = k`. Then the elements of `A` and `B` may be ordered `a₁, …, a_k` and `b₁, …, b_k`
so that the sums `a₁ + b₁, …, a_k + b_k` are pairwise distinct.

Conventions.
* The group is written additively; being of odd order, it is finite (`Fintype G`).
* Ordering `A` as `a₁, …, a_k` and `B` as `b₁, …, b_k` amounts to pairing each `aᵢ` with `bᵢ`,
  that is, to a bijection `σ : A ≃ B` (with `σ aᵢ = bᵢ`). Conversely every bijection gives such
  orderings. The sums are pairwise distinct exactly when `a ↦ a + σ a` is injective on `A`.
* Equivalent form on the source page: every `k × k` submatrix of the addition table of an
  abelian group of odd order has a latin transversal.

Status. The source lists this as open, with known cases for groups of prime order (Alon) and
cyclic groups of odd order (Dasgupta, Károlyi, Serra, Szegedy). It has since been proved in
general by B. Arsovski, A proof of Snevily's conjecture, Israel J. Math. 182 (2011), 505–508,
doi:10.1007/s11856-011-0040-6. So this is a known theorem, not an open problem.
The odd order hypothesis is needed: the full addition table of `ZMod 2` has no latin transversal.
-/

namespace OMA.S_opg_snevilys_conjecture

theorem main :
    ∀ (G : Type) [AddCommGroup G] [Fintype G], Odd (Fintype.card G) →
      ∀ A B : Finset G, A.card = B.card →
        ∃ σ : A ≃ B, Function.Injective (fun a : A => (a : G) + (σ a : G)) := by
  sorry

end OMA.S_opg_snevilys_conjecture
