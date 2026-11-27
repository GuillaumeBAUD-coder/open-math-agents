import Mathlib

/-!
# Erdős Problem 475

Source: https://www.erdosproblems.com/475
Credit: @mattdorman

The source asks (Graham's rearrangement problem): let `p` be a prime. Given any finite set
`A ⊆ 𝔽_p \ {0}`, is there always a rearrangement `A = {a₁, …, a_t}` such that all partial sums
`∑_{1 ≤ k ≤ m} a_k` are distinct, for all `1 ≤ m ≤ t`?

Reading used here: a rearrangement of `A` is a duplicate-free list `l` whose elements are exactly
`A`; its partial sums are the sums of its first `m + 1` entries for `m < l.length`, and these must
be pairwise distinct. The statement below is the affirmative answer.
-/

namespace OMA.S_erdos_475

theorem main :
    ∀ p : ℕ, p.Prime → ∀ A : Finset (ZMod p), (0 : ZMod p) ∉ A →
      ∃ l : List (ZMod p), l.Nodup ∧ l.toFinset = A ∧
        ((List.range l.length).map fun m => (l.take (m + 1)).sum).Nodup := by
  sorry

end OMA.S_erdos_475
