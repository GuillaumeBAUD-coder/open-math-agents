import OMAReductions.R_Erdos436_erdos_436_variants_three_two_R1
import Mathlib

-- Step Erdos436.erdos_436.variants.three_two.R1.H1: hypothesis H1 of reduction Erdos436.erdos_436.variants.three_two.R1
-- Credit: @luciusacarr

/-! Finite case split on the values `w p ∈ ZMod 3` of the primes `p` (in increasing order), stopping as soon
as some `n ≤ 77` has both weighted factor sums of `n` and `n + 1` equal to `0`: a search tree of 64 nodes. -/

namespace OMA436tt

theorem main_H1 : OMA.R_Erdos436_erdos_436_variants_three_two_R1.H1 := by
  unfold OMA.R_Erdos436_erdos_436_variants_three_two_R1.H1
  intro w
  have key3 : ∀ x : ZMod 3, x = 0 ∨ x = 1 ∨ x = 2 := by decide
  have key : ∀ p : ℕ, w p = 0 ∨ w p = 1 ∨ w p = 2 := fun p => key3 (w p)
  rcases key 2 with h2 | h2 | h2
  · exact ⟨1, by decide, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2]; decide⟩
  · rcases key 3 with h3 | h3 | h3
    · exact ⟨8, by decide, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3]; decide⟩
    · rcases key 5 with h5 | h5 | h5
      · rcases key 7 with h7 | h7 | h7
        · exact ⟨7, by decide, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h7]; decide⟩
        · exact ⟨27, by decide, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h7]; decide⟩
        · rcases key 11 with h11 | h11 | h11
          · exact ⟨11, by decide, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h7, h11]; decide⟩
          · rcases key 13 with h13 | h13 | h13
            · exact ⟨12, by decide, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h7, h11, h13]; decide⟩
            · exact ⟨77, by decide, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h7, h11, h13]; decide⟩
            · exact ⟨25, by decide, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h7, h11, h13]; decide⟩
          · exact ⟨21, by decide, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h7, h11]; decide⟩
      · rcases key 7 with h7 | h7 | h7
        · exact ⟨7, by decide, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h7]; decide⟩
        · exact ⟨27, by decide, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h7]; decide⟩
        · exact ⟨20, by decide, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h7]; decide⟩
      · rcases key 7 with h7 | h7 | h7
        · exact ⟨7, by decide, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h7]; decide⟩
        · exact ⟨27, by decide, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h7]; decide⟩
        · exact ⟨14, by decide, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h7]; decide⟩
    · rcases key 5 with h5 | h5 | h5
      · exact ⟨5, by decide, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5]; decide⟩
      · rcases key 7 with h7 | h7 | h7
        · exact ⟨6, by decide, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h7]; decide⟩
        · exact ⟨20, by decide, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h7]; decide⟩
        · exact ⟨14, by decide, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h7]; decide⟩
      · rcases key 7 with h7 | h7 | h7
        · exact ⟨6, by decide, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h7]; decide⟩
        · exact ⟨27, by decide, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h7]; decide⟩
        · exact ⟨63, by decide, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h7]; decide⟩
  · rcases key 3 with h3 | h3 | h3
    · exact ⟨8, by decide, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3]; decide⟩
    · rcases key 5 with h5 | h5 | h5
      · exact ⟨5, by decide, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5]; decide⟩
      · rcases key 7 with h7 | h7 | h7
        · exact ⟨6, by decide, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h7]; decide⟩
        · exact ⟨63, by decide, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h7]; decide⟩
        · exact ⟨27, by decide, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h7]; decide⟩
      · rcases key 7 with h7 | h7 | h7
        · exact ⟨6, by decide, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h7]; decide⟩
        · exact ⟨14, by decide, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h7]; decide⟩
        · exact ⟨20, by decide, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h7]; decide⟩
    · rcases key 5 with h5 | h5 | h5
      · rcases key 7 with h7 | h7 | h7
        · exact ⟨7, by decide, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h7]; decide⟩
        · rcases key 11 with h11 | h11 | h11
          · exact ⟨11, by decide, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h7, h11]; decide⟩
          · exact ⟨21, by decide, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h7, h11]; decide⟩
          · rcases key 13 with h13 | h13 | h13
            · exact ⟨12, by decide, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h7, h11, h13]; decide⟩
            · exact ⟨25, by decide, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h7, h11, h13]; decide⟩
            · exact ⟨77, by decide, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h7, h11, h13]; decide⟩
        · exact ⟨27, by decide, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h7]; decide⟩
      · rcases key 7 with h7 | h7 | h7
        · exact ⟨7, by decide, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h7]; decide⟩
        · exact ⟨14, by decide, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h7]; decide⟩
        · exact ⟨27, by decide, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h7]; decide⟩
      · rcases key 7 with h7 | h7 | h7
        · exact ⟨7, by decide, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h7]; decide⟩
        · exact ⟨20, by decide, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h7]; decide⟩
        · exact ⟨27, by decide, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h7]; decide⟩

end OMA436tt

theorem OMA.solution : OMA.R_Erdos436_erdos_436_variants_three_two_R1.H1 := OMA436tt.main_H1
