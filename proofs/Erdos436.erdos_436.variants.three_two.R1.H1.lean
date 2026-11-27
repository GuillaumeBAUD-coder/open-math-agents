import OMAReductions.R_Erdos436_erdos_436_variants_three_two_R1
import Mathlib

-- Step Erdos436.erdos_436.variants.three_two.R1.H1: hypothesis H1 of reduction Erdos436.erdos_436.variants.three_two.R1
-- Credit: @luciusacarr

/-! Finite case split on the values `w p ∈ ZMod 3` of the primes `p` (in increasing order), stopping as soon
as some `n ≤ 77` has both weighted factor sums of `n` and `n + 1` equal to `0`: a search tree of 64 nodes.
Each leaf `L n` checks its witness `n` from the case hypotheses in scope (through the auto-param). -/

namespace OMA436tt

lemma K : ∀ x : ZMod 3, x = 0 ∨ x = 1 ∨ x = 2 := by decide

lemma L {w : ℕ → ZMod 3} (n : ℕ) (h1 : n ∈ Finset.Icc 1 77 := by decide)
    (h : (n.primeFactorsList.map w).sum = 0 ∧ ((n + 1).primeFactorsList.map w).sum = 0 := by
      simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, *] <;> decide) :
    ∃ n ∈ Finset.Icc 1 77, (n.primeFactorsList.map w).sum = 0 ∧ ((n + 1).primeFactorsList.map w).sum = 0 :=
  ⟨n, h1, h⟩

end OMA436tt

open OMA436tt in
theorem OMA.solution : OMA.R_Erdos436_erdos_436_variants_three_two_R1.H1 := by
  intro w
  obtain h | h | h := K (w 2)
  · exact L 1
  · obtain h | h | h := K (w 3)
    · exact L 8
    · obtain h | h | h := K (w 5)
      · obtain h | h | h := K (w 7)
        · exact L 7
        · exact L 27
        · obtain h | h | h := K (w 11)
          · exact L 11
          · obtain h | h | h := K (w 13)
            · exact L 12
            · exact L 77
            · exact L 25
          · exact L 21
      · obtain h | h | h := K (w 7)
        · exact L 7
        · exact L 27
        · exact L 20
      · obtain h | h | h := K (w 7)
        · exact L 7
        · exact L 27
        · exact L 14
    · obtain h | h | h := K (w 5)
      · exact L 5
      · obtain h | h | h := K (w 7)
        · exact L 6
        · exact L 20
        · exact L 14
      · obtain h | h | h := K (w 7)
        · exact L 6
        · exact L 27
        · exact L 63
  · obtain h | h | h := K (w 3)
    · exact L 8
    · obtain h | h | h := K (w 5)
      · exact L 5
      · obtain h | h | h := K (w 7)
        · exact L 6
        · exact L 63
        · exact L 27
      · obtain h | h | h := K (w 7)
        · exact L 6
        · exact L 14
        · exact L 20
    · obtain h | h | h := K (w 5)
      · obtain h | h | h := K (w 7)
        · exact L 7
        · obtain h | h | h := K (w 11)
          · exact L 11
          · exact L 21
          · obtain h | h | h := K (w 13)
            · exact L 12
            · exact L 25
            · exact L 77
        · exact L 27
      · obtain h | h | h := K (w 7)
        · exact L 7
        · exact L 14
        · exact L 27
      · obtain h | h | h := K (w 7)
        · exact L 7
        · exact L 20
        · exact L 27

