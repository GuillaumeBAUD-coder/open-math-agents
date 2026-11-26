import FormalConjectures.Wikipedia.AlspachConjecture

namespace OMA.R_AlspachConjecture_alspach_conjecture_R1

open SimpleGraph AlspachConjecture

-- Bryant, Horsley and Pettersson, arXiv:1204.3709, Lemma 2 (Balister),
-- specialised to odd orders. This is a finite verification.
def H1 : Prop :=
  ∀ (n : ℕ), Odd n → n ≤ 14 → ∀ m : Multiset ℕ,
    (∀ x ∈ m, 3 ≤ x ∧ x ≤ n) → m.sum = n.choose 2 →
    ∃ C : Multiset (Cycle (completeGraph (Fin n))),
      IsCycleDecomposition (completeGraph (Fin n)) C ∧ lengths C = m

-- Theorem 3 of the same paper, specialised to large odd orders.
-- In its premise, the last conjunction gives the six ancestor-list conditions.
-- The first counts multiplicities, including repeated intermediate lengths.
def H2 : Prop :=
  ∀ (n : ℕ), Odd n → 15 ≤ n →
    (∀ a : Multiset ℕ, (∀ x ∈ a, 3 ≤ x ∧ x ≤ n) → a.sum = n.choose 2 →
      ((a.filter (fun x => 6 ≤ x ∧ x < n)).card ≤ 1 ∧
       (3 ≤ a.count 5 → 2 * a.count 4 + 6 ≤ n) ∧
       (2 ≤ a.count 5 → 3 * a.count 3 + 10 ≤ n) ∧
       (1 ≤ a.count 4 → 1 ≤ a.count 5 → 3 * a.count 3 + 9 ≤ n) ∧
       (1 ≤ a.count 4 → ∀ x : ℕ, n ≤ x + 2 → x < n → a.count x = 0) ∧
       (1 ≤ a.count 5 → ∀ x : ℕ, n ≤ x + 4 → x < n → a.count x = 0)) →
      ∃ C : Multiset (Cycle (completeGraph (Fin n))),
        IsCycleDecomposition (completeGraph (Fin n)) C ∧ lengths C = a) →
    ∀ m : Multiset ℕ, (∀ x ∈ m, 3 ≤ x ∧ x ≤ n) → m.sum = n.choose 2 →
      ∃ C : Multiset (Cycle (completeGraph (Fin n))),
        IsCycleDecomposition (completeGraph (Fin n)) C ∧ lengths C = m

-- The restricted construction that occupies Sections 3 through 5.
-- Their proof treats at least two Hamilton cycles and at most one separately.
def H3 : Prop :=
  ∀ (n : ℕ), Odd n → 15 ≤ n → ∀ a : Multiset ℕ,
    (∀ x ∈ a, 3 ≤ x ∧ x ≤ n) → a.sum = n.choose 2 →
    ((a.filter (fun x => 6 ≤ x ∧ x < n)).card ≤ 1 ∧
     (3 ≤ a.count 5 → 2 * a.count 4 + 6 ≤ n) ∧
     (2 ≤ a.count 5 → 3 * a.count 3 + 10 ≤ n) ∧
     (1 ≤ a.count 4 → 1 ≤ a.count 5 → 3 * a.count 3 + 9 ≤ n) ∧
     (1 ≤ a.count 4 → ∀ x : ℕ, n ≤ x + 2 → x < n → a.count x = 0) ∧
     (1 ≤ a.count 5 → ∀ x : ℕ, n ≤ x + 4 → x < n → a.count x = 0)) →
    ∃ C : Multiset (Cycle (completeGraph (Fin n))),
      IsCycleDecomposition (completeGraph (Fin n)) C ∧ lengths C = a

theorem main : H1 → H2 → H3 → type_of% @AlspachConjecture.alspach_conjecture := by
  intro small transfer ancestors n hn m hm hsum
  by_cases hs : n ≤ 14
  · exact small n hn hs m hm hsum
  · have hl : 15 ≤ n := by omega
    exact transfer n hn hl (ancestors n hn hl) m hm hsum

end OMA.R_AlspachConjecture_alspach_conjecture_R1
