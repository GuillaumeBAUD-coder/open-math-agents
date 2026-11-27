import FormalConjectures.Wikipedia.ScholzConjecture

-- Reduction ScholzConjecture.scholz_conjecture.R1 of Scholz conjecture on addition chains
-- Credit: @jagong-cmu
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-! # Split by whether n has an optimal star chain (Brauer 1939 covers that case) -/
namespace OMA.R_ScholzConjecture_scholz_conjecture_R1

-- Every n with an optimal star chain: a chain of length l(n) in which each entry is the
-- previous entry plus some chain entry. Brauer proved the bound for these n.
def H1 : Prop := ∀ n : ℕ, 0 < n →
  (∃ cs : List ℕ, IsAdditionChain cs ∧ cs.getLast? = some n ∧
    cs.length = additionChainLength n + 1 ∧
    ∀ (i : ℕ) (hi : i + 1 < cs.length), ∃ j ∈ cs, cs[i + 1] = cs[i] + j) →
  additionChainLength (2 ^ n - 1) ≤ n - 1 + additionChainLength n

-- Every n with no optimal star chain (the least such n is 12509). This case is open.
def H2 : Prop := ∀ n : ℕ, 0 < n →
  ¬ (∃ cs : List ℕ, IsAdditionChain cs ∧ cs.getLast? = some n ∧
    cs.length = additionChainLength n + 1 ∧
    ∀ (i : ℕ) (hi : i + 1 < cs.length), ∃ j ∈ cs, cs[i + 1] = cs[i] + j) →
  additionChainLength (2 ^ n - 1) ≤ n - 1 + additionChainLength n

theorem main : H1 → H2 → type_of% @ScholzConjecture.scholz_conjecture := by
  intro h1 h2 n hn
  by_cases h : ∃ cs : List ℕ, IsAdditionChain cs ∧ cs.getLast? = some n ∧
    cs.length = additionChainLength n + 1 ∧
    ∀ (i : ℕ) (hi : i + 1 < cs.length), ∃ j ∈ cs, cs[i + 1] = cs[i] + j
  · exact h1 n hn h
  · exact h2 n hn h

end OMA.R_ScholzConjecture_scholz_conjecture_R1
