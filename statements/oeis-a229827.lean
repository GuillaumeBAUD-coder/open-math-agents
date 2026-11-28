import Mathlib

namespace OMA.S_oeis_a229827

/-- OEIS A229827 Conjecture (ii) (Zhi-Wei Sun):
For every field `F` with `|F| > 7`, every finite subset `A ⊆ F` with `|A| = n > 2`, and every
polynomial `P(x) ∈ F[x]` (of degree `< p - 1` if `char(F) = p > 0`) not of the form `c - x`,
there exists a circular permutation `a_1, ..., a_n` of `A` such that
`P(a_1) + a_2, P(a_2) + a_3, ..., P(a_n) + a_1` are pairwise distinct. -/
theorem main :
    ∀ (F : Type) [Field F],
      (Infinite F ∨ ∃ (_ : Fintype F), 7 < Fintype.card F) →
      ∀ (n : ℕ) (hn : 2 < n),
      ∀ (A : Finset F), A.card = n →
      ∀ (P : Polynomial F),
        (∀ p : ℕ, p.Prime → CharP F p → P.natDegree < p - 1) →
        (∀ c : F, P ≠ Polynomial.C c - Polynomial.X) →
        ∃ f : Fin n ≃ A,
          Function.Injective (fun i : Fin n =>
            P.eval (f i).val + (f ⟨(i.val + 1) % n, Nat.mod_lt _ (by omega)⟩).val) := by
  sorry

end OMA.S_oeis_a229827
