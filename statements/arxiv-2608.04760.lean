import Mathlib

namespace OMA.S_arxiv_2608_04760

/-- The distinct-element two-fold sumset, with duplicate sums counted once. -/
def restrictedSumset (A : Finset ℕ) : Finset ℕ :=
  ((A.product A).filter (fun p => p.1 ≠ p.2)).image (fun p => p.1 + p.2)

/-- The Freiman–Lev bound on the restricted sumset of normalized integers. -/
theorem main :
    ∀ (A : Finset ℕ) (l : ℕ),
      7 < A.card → 0 ∈ A → l ∈ A →
      (∀ a ∈ A, a ≤ l) →
      A.gcd id = 1 →
      (if l ≤ 2 * A.card - 5 then l + A.card - 2 else 3 * A.card - 7) ≤
        (restrictedSumset A).card := by
  sorry

end OMA.S_arxiv_2608_04760
