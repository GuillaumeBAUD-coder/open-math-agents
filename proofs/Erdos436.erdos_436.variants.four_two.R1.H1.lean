import OMAReductions.R_Erdos436_erdos_436_variants_four_two_R1
import Mathlib

-- Step Erdos436.erdos_436.variants.four_two.R1.H1: hypothesis H1 of reduction Erdos436.erdos_436.variants.four_two.R1
-- Credit: @luciusacarr

/-! Finite case split on the values `w p ∈ ZMod 4` of the primes `p` (in increasing order), stopping as soon
as some `n ≤ 1224` has both weighted factor sums of `n` and `n + 1` equal to `0`: a search tree of 669 nodes. -/

namespace OMA436ft

theorem main_H1 : OMA.R_Erdos436_erdos_436_variants_four_two_R1.H1 := by
  unfold OMA.R_Erdos436_erdos_436_variants_four_two_R1.H1
  intro w
  have key4 : ∀ x : ZMod 4, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by decide
  have key : ∀ p : ℕ, w p = 0 ∨ w p = 1 ∨ w p = 2 ∨ w p = 3 := fun p => key4 (w p)
  rcases key 2 with h2 | h2 | h2 | h2
  · exact ⟨1, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2]; decide⟩
  · rcases key 3 with h3 | h3 | h3 | h3
    · rcases key 5 with h5 | h5 | h5 | h5
      · exact ⟨15, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5]; decide⟩
      · rcases key 7 with h7 | h7 | h7 | h7
        · exact ⟨48, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h7]; decide⟩
        · rcases key 11 with h11 | h11 | h11 | h11
          · exact ⟨99, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h11]; decide⟩
          · rcases key 13 with h13 | h13 | h13 | h13
            · exact ⟨39, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h13]; decide⟩
            · rcases key 17 with h17 | h17 | h17 | h17
              · exact ⟨16, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h17]; decide⟩
              · exact ⟨1224, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h7, h17]; decide⟩
              · exact ⟨935, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h11, h13, h17]; decide⟩
              · exact ⟨119, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h7, h17]; decide⟩
            · exact ⟨168, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h7, h13]; decide⟩
            · exact ⟨26, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h13]; decide⟩
          · exact ⟨120, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h11]; decide⟩
          · exact ⟨55, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h5, h7, h11]; decide⟩
        · exact ⟨27, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h7]; decide⟩
        · rcases key 11 with h11 | h11 | h11 | h11
          · exact ⟨99, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h11]; decide⟩
          · rcases key 13 with h13 | h13 | h13 | h13
            · exact ⟨13, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h7, h13]; decide⟩
            · exact ⟨104, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h7, h13]; decide⟩
            · exact ⟨728, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h7, h13]; decide⟩
            · exact ⟨26, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h13]; decide⟩
          · exact ⟨120, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h11]; decide⟩
          · rcases key 13 with h13 | h13 | h13 | h13
            · exact ⟨13, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h7, h13]; decide⟩
            · exact ⟨104, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h7, h13]; decide⟩
            · exact ⟨728, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h7, h13]; decide⟩
            · exact ⟨26, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h13]; decide⟩
      · rcases key 7 with h7 | h7 | h7 | h7
        · exact ⟨20, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h7]; decide⟩
        · rcases key 11 with h11 | h11 | h11 | h11
          · rcases key 13 with h13 | h13 | h13 | h13
            · exact ⟨143, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h11, h13]; decide⟩
            · exact ⟨363, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h7, h11, h13]; decide⟩
            · exact ⟨168, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h7, h13]; decide⟩
            · exact ⟨25, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h5, h13]; decide⟩
          · rcases key 13 with h13 | h13 | h13 | h13
            · exact ⟨168, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h7, h13]; decide⟩
            · exact ⟨675, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h13]; decide⟩
            · exact ⟨168, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h7, h13]; decide⟩
            · exact ⟨25, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h5, h13]; decide⟩
          · exact ⟨55, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h5, h7, h11]; decide⟩
          · rcases key 13 with h13 | h13 | h13 | h13
            · exact ⟨168, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h7, h13]; decide⟩
            · exact ⟨143, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h11, h13]; decide⟩
            · exact ⟨65, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h11, h13]; decide⟩
            · exact ⟨25, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h5, h13]; decide⟩
        · exact ⟨27, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h7]; decide⟩
        · exact ⟨224, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h7]; decide⟩
      · exact ⟨9, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5]; decide⟩
    · rcases key 5 with h5 | h5 | h5 | h5
      · exact ⟨24, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5]; decide⟩
      · rcases key 7 with h7 | h7 | h7 | h7
        · rcases key 11 with h11 | h11 | h11 | h11
          · rcases key 13 with h13 | h13 | h13 | h13
            · exact ⟨90, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h7, h13]; decide⟩
            · rcases key 17 with h17 | h17 | h17 | h17
              · exact ⟨16, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h17]; decide⟩
              · exact ⟨135, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h17]; decide⟩
              · exact ⟨255, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h17]; decide⟩
              · exact ⟨374, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h11, h17]; decide⟩
            · exact ⟨77, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h7, h11, h13]; decide⟩
            · exact ⟨39, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h13]; decide⟩
          · rcases key 13 with h13 | h13 | h13 | h13
            · exact ⟨90, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h7, h13]; decide⟩
            · rcases key 17 with h17 | h17 | h17 | h17
              · exact ⟨16, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h17]; decide⟩
              · exact ⟨135, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h17]; decide⟩
              · exact ⟨255, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h17]; decide⟩
              · exact ⟨220, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h5, h11, h13, h17]; decide⟩
            · exact ⟨168, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h7, h13]; decide⟩
            · exact ⟨39, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h13]; decide⟩
          · exact ⟨99, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h11]; decide⟩
          · exact ⟨54, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h11]; decide⟩
        · rcases key 11 with h11 | h11 | h11 | h11
          · exact ⟨440, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h7, h11]; decide⟩
          · rcases key 13 with h13 | h13 | h13 | h13
            · rcases key 17 with h17 | h17 | h17 | h17
              · exact ⟨16, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h17]; decide⟩
              · exact ⟨135, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h17]; decide⟩
              · exact ⟨169, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h5, h13, h17]; decide⟩
              · exact ⟨84, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h7, h17]; decide⟩
            · exact ⟨350, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h7, h13]; decide⟩
            · exact ⟨195, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h7, h13]; decide⟩
            · exact ⟨39, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h13]; decide⟩
          · exact ⟨99, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h11]; decide⟩
          · exact ⟨54, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h11]; decide⟩
        · rcases key 11 with h11 | h11 | h11 | h11
          · exact ⟨175, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h5, h7, h11]; decide⟩
          · exact ⟨384, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h7, h11]; decide⟩
          · exact ⟨99, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h11]; decide⟩
          · exact ⟨54, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h11]; decide⟩
        · exact ⟨35, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h7]; decide⟩
      · exact ⟨24, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5]; decide⟩
      · exact ⟨15, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5]; decide⟩
    · rcases key 5 with h5 | h5 | h5 | h5
      · exact ⟨80, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5]; decide⟩
      · rcases key 7 with h7 | h7 | h7 | h7
        · rcases key 11 with h11 | h11 | h11 | h11
          · exact ⟨11, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h11]; decide⟩
          · rcases key 13 with h13 | h13 | h13 | h13
            · exact ⟨12, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h13]; decide⟩
            · exact ⟨675, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h13]; decide⟩
            · exact ⟨39, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h13]; decide⟩
            · exact ⟨65, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h11, h13]; decide⟩
          · rcases key 13 with h13 | h13 | h13 | h13
            · exact ⟨12, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h13]; decide⟩
            · exact ⟨675, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h13]; decide⟩
            · exact ⟨39, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h13]; decide⟩
            · exact ⟨675, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h13]; decide⟩
          · rcases key 13 with h13 | h13 | h13 | h13
            · exact ⟨12, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h13]; decide⟩
            · exact ⟨143, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h11, h13]; decide⟩
            · exact ⟨39, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h13]; decide⟩
            · exact ⟨675, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h13]; decide⟩
        · rcases key 11 with h11 | h11 | h11 | h11
          · exact ⟨11, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h11]; decide⟩
          · rcases key 13 with h13 | h13 | h13 | h13
            · exact ⟨12, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h13]; decide⟩
            · exact ⟨104, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h7, h13]; decide⟩
            · exact ⟨39, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h13]; decide⟩
            · exact ⟨65, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h11, h13]; decide⟩
          · rcases key 13 with h13 | h13 | h13 | h13
            · exact ⟨12, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h13]; decide⟩
            · exact ⟨104, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h7, h13]; decide⟩
            · exact ⟨39, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h13]; decide⟩
            · exact ⟨675, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h13]; decide⟩
          · exact ⟨55, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h5, h7, h11]; decide⟩
        · rcases key 11 with h11 | h11 | h11 | h11
          · exact ⟨11, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h11]; decide⟩
          · rcases key 13 with h13 | h13 | h13 | h13
            · exact ⟨12, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h13]; decide⟩
            · exact ⟨675, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h13]; decide⟩
            · exact ⟨39, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h13]; decide⟩
            · exact ⟨65, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h11, h13]; decide⟩
          · rcases key 13 with h13 | h13 | h13 | h13
            · exact ⟨12, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h13]; decide⟩
            · exact ⟨77, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h7, h11, h13]; decide⟩
            · exact ⟨39, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h13]; decide⟩
            · exact ⟨675, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h13]; decide⟩
          · exact ⟨21, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h7, h11]; decide⟩
        · rcases key 11 with h11 | h11 | h11 | h11
          · exact ⟨11, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h11]; decide⟩
          · rcases key 13 with h13 | h13 | h13 | h13
            · exact ⟨12, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h13]; decide⟩
            · exact ⟨77, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h7, h11, h13]; decide⟩
            · exact ⟨39, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h13]; decide⟩
            · exact ⟨65, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h11, h13]; decide⟩
          · rcases key 13 with h13 | h13 | h13 | h13
            · exact ⟨12, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h13]; decide⟩
            · exact ⟨195, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h7, h13]; decide⟩
            · exact ⟨39, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h13]; decide⟩
            · exact ⟨675, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h13]; decide⟩
          · rcases key 13 with h13 | h13 | h13 | h13
            · exact ⟨12, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h13]; decide⟩
            · exact ⟨143, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h11, h13]; decide⟩
            · exact ⟨39, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h13]; decide⟩
            · exact ⟨363, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h7, h11, h13]; decide⟩
      · exact ⟨15, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5]; decide⟩
      · exact ⟨9, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5]; decide⟩
    · rcases key 5 with h5 | h5 | h5 | h5
      · exact ⟨5, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5]; decide⟩
      · exact ⟨15, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5]; decide⟩
      · rcases key 7 with h7 | h7 | h7 | h7
        · exact ⟨6, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h7]; decide⟩
        · exact ⟨20, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h7]; decide⟩
        · exact ⟨35, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h7]; decide⟩
        · rcases key 11 with h11 | h11 | h11 | h11
          · exact ⟨120, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h11]; decide⟩
          · rcases key 13 with h13 | h13 | h13 | h13
            · exact ⟨13, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h7, h13]; decide⟩
            · exact ⟨104, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h7, h13]; decide⟩
            · rcases key 17 with h17 | h17 | h17 | h17
              · exact ⟨16, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h17]; decide⟩
              · exact ⟨51, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h13, h17]; decide⟩
              · exact ⟨84, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h7, h17]; decide⟩
              · exact ⟨33, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h11, h17]; decide⟩
            · exact ⟨25, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h5, h13]; decide⟩
          · exact ⟨44, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h11]; decide⟩
          · exact ⟨440, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h7, h11]; decide⟩
      · rcases key 7 with h7 | h7 | h7 | h7
        · exact ⟨6, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h7]; decide⟩
        · exact ⟨35, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h7]; decide⟩
        · rcases key 11 with h11 | h11 | h11 | h11
          · exact ⟨10, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h5, h11]; decide⟩
          · rcases key 13 with h13 | h13 | h13 | h13
            · exact ⟨168, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h7, h13]; decide⟩
            · exact ⟨104, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h7, h13]; decide⟩
            · exact ⟨168, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h7, h13]; decide⟩
            · rcases key 17 with h17 | h17 | h17 | h17
              · exact ⟨16, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h17]; decide⟩
              · exact ⟨135, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h17]; decide⟩
              · exact ⟨153, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h7, h11, h17]; decide⟩
              · exact ⟨33, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h11, h17]; decide⟩
          · exact ⟨99, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h11]; decide⟩
          · rcases key 13 with h13 | h13 | h13 | h13
            · exact ⟨168, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h7, h13]; decide⟩
            · exact ⟨104, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h7, h13]; decide⟩
            · exact ⟨168, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h7, h13]; decide⟩
            · exact ⟨351, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h11, h13]; decide⟩
        · exact ⟨224, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h7]; decide⟩
  · rcases key 3 with h3 | h3 | h3 | h3
    · exact ⟨3, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3]; decide⟩
    · rcases key 5 with h5 | h5 | h5 | h5
      · exact ⟨4, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h5]; decide⟩
      · rcases key 7 with h7 | h7 | h7 | h7
        · exact ⟨49, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h5, h7]; decide⟩
        · rcases key 11 with h11 | h11 | h11 | h11
          · exact ⟨120, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h11]; decide⟩
          · exact ⟨440, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h7, h11]; decide⟩
          · exact ⟨98, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h7, h11]; decide⟩
          · rcases key 13 with h13 | h13 | h13 | h13
            · exact ⟨168, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h7, h13]; decide⟩
            · exact ⟨77, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h7, h11, h13]; decide⟩
            · exact ⟨168, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h7, h13]; decide⟩
            · exact ⟨64, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h5, h13]; decide⟩
        · exact ⟨49, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h5, h7]; decide⟩
        · rcases key 11 with h11 | h11 | h11 | h11
          · exact ⟨120, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h11]; decide⟩
          · exact ⟨440, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h7, h11]; decide⟩
          · exact ⟨21, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h7, h11]; decide⟩
          · rcases key 13 with h13 | h13 | h13 | h13
            · rcases key 17 with h17 | h17 | h17 | h17
              · exact ⟨16, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h17]; decide⟩
              · exact ⟨119, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h7, h17]; decide⟩
              · exact ⟨33, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h11, h17]; decide⟩
              · exact ⟨50, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h17]; decide⟩
            · rcases key 17 with h17 | h17 | h17 | h17
              · exact ⟨16, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h17]; decide⟩
              · exact ⟨119, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h7, h17]; decide⟩
              · exact ⟨33, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h11, h17]; decide⟩
              · exact ⟨50, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h17]; decide⟩
            · exact ⟨324, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h13]; decide⟩
            · exact ⟨64, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h5, h13]; decide⟩
      · rcases key 7 with h7 | h7 | h7 | h7
        · rcases key 11 with h11 | h11 | h11 | h11
          · exact ⟨10, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h5, h11]; decide⟩
          · rcases key 13 with h13 | h13 | h13 | h13
            · exact ⟨324, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h13]; decide⟩
            · exact ⟨195, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h7, h13]; decide⟩
            · exact ⟨25, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h5, h13]; decide⟩
            · exact ⟨39, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h13]; decide⟩
          · exact ⟨99, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h11]; decide⟩
          · rcases key 13 with h13 | h13 | h13 | h13
            · exact ⟨324, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h13]; decide⟩
            · exact ⟨195, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h7, h13]; decide⟩
            · exact ⟨25, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h5, h13]; decide⟩
            · exact ⟨39, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h13]; decide⟩
        · rcases key 11 with h11 | h11 | h11 | h11
          · exact ⟨10, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h5, h11]; decide⟩
          · rcases key 13 with h13 | h13 | h13 | h13
            · exact ⟨168, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h7, h13]; decide⟩
            · rcases key 17 with h17 | h17 | h17 | h17
              · exact ⟨16, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h17]; decide⟩
              · exact ⟨255, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h17]; decide⟩
              · exact ⟨153, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h7, h11, h17]; decide⟩
              · rcases key 19 with h19 | h19 | h19 | h19
                · exact ⟨18, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h19]; decide⟩
                · exact ⟨285, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h11, h13, h19]; decide⟩
                · exact ⟨399, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h7, h19]; decide⟩
                · rcases key 23 with h23 | h23 | h23 | h23
                  · rcases key 29 with h29 | h29 | h29 | h29
                    · rcases key 31 with h31 | h31 | h31 | h31
                      · rcases key 37 with h37 | h37 | h37 | h37
                        · exact ⟨666, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h23, h29, h37]; decide⟩
                        · exact ⟨221, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h13, h17, h37]; decide⟩
                        · exact ⟨296, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h11, h37]; decide⟩
                        · exact ⟨1035, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h7, h23, h37]; decide⟩
                      · exact ⟨186, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h11, h17, h31]; decide⟩
                      · exact ⟨154, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h5, h7, h11, h31]; decide⟩
                      · exact ⟨92, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h23, h31]; decide⟩
                    · rcases key 31 with h31 | h31 | h31 | h31
                      · rcases key 37 with h37 | h37 | h37 | h37
                        · rcases key 41 with h41 | h41 | h41 | h41
                          · exact ⟨40, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h5, h41]; decide⟩
                          · exact ⟨245, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h7, h41]; decide⟩
                          · exact ⟨81, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h41]; decide⟩
                          · exact ⟨123, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h31, h41]; decide⟩
                        · exact ⟨221, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h13, h17, h37]; decide⟩
                        · exact ⟨296, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h11, h37]; decide⟩
                        · exact ⟨406, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h7, h11, h29, h37]; decide⟩
                      · exact ⟨186, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h11, h17, h31]; decide⟩
                      · exact ⟨154, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h5, h7, h11, h31]; decide⟩
                      · exact ⟨92, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h23, h31]; decide⟩
                    · exact ⟨57, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h19, h29]; decide⟩
                    · exact ⟨203, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h7, h17, h29]; decide⟩
                  · exact ⟨391, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h7, h17, h23]; decide⟩
                  · exact ⟨45, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h23]; decide⟩
                  · exact ⟨160, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h5, h7, h23]; decide⟩
            · exact ⟨25, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h5, h13]; decide⟩
            · exact ⟨39, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h13]; decide⟩
          · exact ⟨98, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h7, h11]; decide⟩
          · rcases key 13 with h13 | h13 | h13 | h13
            · exact ⟨168, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h7, h13]; decide⟩
            · exact ⟨77, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h7, h11, h13]; decide⟩
            · exact ⟨25, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h5, h13]; decide⟩
            · exact ⟨39, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h13]; decide⟩
        · exact ⟨63, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h7]; decide⟩
        · rcases key 11 with h11 | h11 | h11 | h11
          · exact ⟨10, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h5, h11]; decide⟩
          · rcases key 13 with h13 | h13 | h13 | h13
            · exact ⟨324, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h13]; decide⟩
            · exact ⟨77, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h7, h11, h13]; decide⟩
            · exact ⟨25, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h5, h13]; decide⟩
            · exact ⟨39, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h13]; decide⟩
          · exact ⟨21, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h7, h11]; decide⟩
          · rcases key 13 with h13 | h13 | h13 | h13
            · exact ⟨324, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h13]; decide⟩
            · rcases key 17 with h17 | h17 | h17 | h17
              · exact ⟨16, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h17]; decide⟩
              · exact ⟨255, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h17]; decide⟩
              · exact ⟨33, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h11, h17]; decide⟩
              · exact ⟨594, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h7, h11, h17]; decide⟩
            · exact ⟨25, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h5, h13]; decide⟩
            · exact ⟨39, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h13]; decide⟩
      · exact ⟨15, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5]; decide⟩
    · rcases key 5 with h5 | h5 | h5 | h5
      · exact ⟨4, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h5]; decide⟩
      · rcases key 7 with h7 | h7 | h7 | h7
        · exact ⟨6, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h7]; decide⟩
        · rcases key 11 with h11 | h11 | h11 | h11
          · exact ⟨98, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h7, h11]; decide⟩
          · rcases key 13 with h13 | h13 | h13 | h13
            · exact ⟨675, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h13]; decide⟩
            · exact ⟨728, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h7, h13]; decide⟩
            · exact ⟨104, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h7, h13]; decide⟩
            · exact ⟨64, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h5, h13]; decide⟩
          · exact ⟨384, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h7, h11]; decide⟩
          · exact ⟨54, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h11]; decide⟩
        · exact ⟨49, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h5, h7]; decide⟩
        · exact ⟨35, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h7]; decide⟩
      · exact ⟨9, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5]; decide⟩
      · rcases key 7 with h7 | h7 | h7 | h7
        · exact ⟨6, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h7]; decide⟩
        · exact ⟨35, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h7]; decide⟩
        · exact ⟨49, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h5, h7]; decide⟩
        · rcases key 11 with h11 | h11 | h11 | h11
          · exact ⟨98, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h7, h11]; decide⟩
          · exact ⟨54, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h11]; decide⟩
          · exact ⟨384, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h7, h11]; decide⟩
          · rcases key 13 with h13 | h13 | h13 | h13
            · exact ⟨675, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h13]; decide⟩
            · exact ⟨64, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h5, h13]; decide⟩
            · exact ⟨104, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h7, h13]; decide⟩
            · exact ⟨728, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h7, h13]; decide⟩
    · rcases key 5 with h5 | h5 | h5 | h5
      · exact ⟨4, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h5]; decide⟩
      · exact ⟨15, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5]; decide⟩
      · rcases key 7 with h7 | h7 | h7 | h7
        · rcases key 11 with h11 | h11 | h11 | h11
          · exact ⟨10, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h5, h11]; decide⟩
          · rcases key 13 with h13 | h13 | h13 | h13
            · exact ⟨324, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h13]; decide⟩
            · exact ⟨39, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h13]; decide⟩
            · exact ⟨25, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h5, h13]; decide⟩
            · exact ⟨195, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h7, h13]; decide⟩
          · exact ⟨99, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h11]; decide⟩
          · rcases key 13 with h13 | h13 | h13 | h13
            · exact ⟨324, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h13]; decide⟩
            · exact ⟨39, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h13]; decide⟩
            · exact ⟨25, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h5, h13]; decide⟩
            · exact ⟨195, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h7, h13]; decide⟩
        · rcases key 11 with h11 | h11 | h11 | h11
          · exact ⟨10, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h5, h11]; decide⟩
          · rcases key 13 with h13 | h13 | h13 | h13
            · exact ⟨324, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h13]; decide⟩
            · exact ⟨39, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h13]; decide⟩
            · exact ⟨25, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h5, h13]; decide⟩
            · rcases key 17 with h17 | h17 | h17 | h17
              · exact ⟨16, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h17]; decide⟩
              · exact ⟨594, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h7, h11, h17]; decide⟩
              · exact ⟨33, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h11, h17]; decide⟩
              · exact ⟨255, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h17]; decide⟩
          · exact ⟨21, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h7, h11]; decide⟩
          · rcases key 13 with h13 | h13 | h13 | h13
            · exact ⟨324, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h13]; decide⟩
            · exact ⟨39, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h13]; decide⟩
            · exact ⟨25, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h5, h13]; decide⟩
            · exact ⟨77, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h7, h11, h13]; decide⟩
        · exact ⟨63, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h7]; decide⟩
        · rcases key 11 with h11 | h11 | h11 | h11
          · exact ⟨10, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h5, h11]; decide⟩
          · rcases key 13 with h13 | h13 | h13 | h13
            · exact ⟨168, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h7, h13]; decide⟩
            · exact ⟨39, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h13]; decide⟩
            · exact ⟨25, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h5, h13]; decide⟩
            · exact ⟨77, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h7, h11, h13]; decide⟩
          · exact ⟨98, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h7, h11]; decide⟩
          · rcases key 13 with h13 | h13 | h13 | h13
            · exact ⟨168, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h7, h13]; decide⟩
            · exact ⟨39, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h13]; decide⟩
            · exact ⟨25, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h5, h13]; decide⟩
            · rcases key 17 with h17 | h17 | h17 | h17
              · exact ⟨16, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h17]; decide⟩
              · rcases key 19 with h19 | h19 | h19 | h19
                · exact ⟨18, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h19]; decide⟩
                · rcases key 23 with h23 | h23 | h23 | h23
                  · rcases key 29 with h29 | h29 | h29 | h29
                    · rcases key 31 with h31 | h31 | h31 | h31
                      · rcases key 37 with h37 | h37 | h37 | h37
                        · exact ⟨666, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h23, h29, h37]; decide⟩
                        · exact ⟨1035, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h7, h23, h37]; decide⟩
                        · exact ⟨296, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h11, h37]; decide⟩
                        · exact ⟨221, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h13, h17, h37]; decide⟩
                      · exact ⟨92, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h23, h31]; decide⟩
                      · exact ⟨154, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h5, h7, h11, h31]; decide⟩
                      · exact ⟨186, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h11, h17, h31]; decide⟩
                    · exact ⟨203, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h7, h17, h29]; decide⟩
                    · exact ⟨57, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h19, h29]; decide⟩
                    · rcases key 31 with h31 | h31 | h31 | h31
                      · rcases key 37 with h37 | h37 | h37 | h37
                        · rcases key 41 with h41 | h41 | h41 | h41
                          · exact ⟨40, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h5, h41]; decide⟩
                          · exact ⟨123, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h31, h41]; decide⟩
                          · exact ⟨81, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h41]; decide⟩
                          · exact ⟨245, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h7, h41]; decide⟩
                        · exact ⟨406, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h7, h11, h29, h37]; decide⟩
                        · exact ⟨296, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h11, h37]; decide⟩
                        · exact ⟨221, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h13, h17, h37]; decide⟩
                      · exact ⟨92, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h23, h31]; decide⟩
                      · exact ⟨154, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h5, h7, h11, h31]; decide⟩
                      · exact ⟨186, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h11, h17, h31]; decide⟩
                  · exact ⟨160, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h5, h7, h23]; decide⟩
                  · exact ⟨45, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h23]; decide⟩
                  · exact ⟨391, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h7, h17, h23]; decide⟩
                · exact ⟨399, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h7, h19]; decide⟩
                · exact ⟨285, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h11, h13, h19]; decide⟩
              · exact ⟨153, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h7, h11, h17]; decide⟩
              · exact ⟨255, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h17]; decide⟩
      · rcases key 7 with h7 | h7 | h7 | h7
        · exact ⟨49, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h5, h7]; decide⟩
        · rcases key 11 with h11 | h11 | h11 | h11
          · exact ⟨120, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h11]; decide⟩
          · rcases key 13 with h13 | h13 | h13 | h13
            · rcases key 17 with h17 | h17 | h17 | h17
              · exact ⟨16, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h17]; decide⟩
              · exact ⟨50, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h17]; decide⟩
              · exact ⟨33, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h11, h17]; decide⟩
              · exact ⟨119, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h7, h17]; decide⟩
            · exact ⟨64, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h5, h13]; decide⟩
            · exact ⟨324, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h13]; decide⟩
            · rcases key 17 with h17 | h17 | h17 | h17
              · exact ⟨16, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h17]; decide⟩
              · exact ⟨50, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h17]; decide⟩
              · exact ⟨33, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h11, h17]; decide⟩
              · exact ⟨119, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h7, h17]; decide⟩
          · exact ⟨21, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h7, h11]; decide⟩
          · exact ⟨440, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h7, h11]; decide⟩
        · exact ⟨49, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h5, h7]; decide⟩
        · rcases key 11 with h11 | h11 | h11 | h11
          · exact ⟨120, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h11]; decide⟩
          · rcases key 13 with h13 | h13 | h13 | h13
            · exact ⟨168, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h7, h13]; decide⟩
            · exact ⟨64, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h5, h13]; decide⟩
            · exact ⟨168, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h7, h13]; decide⟩
            · exact ⟨77, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h7, h11, h13]; decide⟩
          · exact ⟨98, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h7, h11]; decide⟩
          · exact ⟨440, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h7, h11]; decide⟩
  · rcases key 3 with h3 | h3 | h3 | h3
    · rcases key 5 with h5 | h5 | h5 | h5
      · exact ⟨15, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5]; decide⟩
      · exact ⟨9, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5]; decide⟩
      · rcases key 7 with h7 | h7 | h7 | h7
        · exact ⟨20, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h7]; decide⟩
        · exact ⟨224, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h7]; decide⟩
        · exact ⟨27, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h7]; decide⟩
        · rcases key 11 with h11 | h11 | h11 | h11
          · rcases key 13 with h13 | h13 | h13 | h13
            · exact ⟨143, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h11, h13]; decide⟩
            · exact ⟨25, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h5, h13]; decide⟩
            · exact ⟨168, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h7, h13]; decide⟩
            · exact ⟨363, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h7, h11, h13]; decide⟩
          · rcases key 13 with h13 | h13 | h13 | h13
            · exact ⟨168, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h7, h13]; decide⟩
            · exact ⟨25, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h5, h13]; decide⟩
            · exact ⟨65, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h11, h13]; decide⟩
            · exact ⟨143, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h11, h13]; decide⟩
          · exact ⟨55, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h5, h7, h11]; decide⟩
          · rcases key 13 with h13 | h13 | h13 | h13
            · exact ⟨168, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h7, h13]; decide⟩
            · exact ⟨25, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h5, h13]; decide⟩
            · exact ⟨168, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h7, h13]; decide⟩
            · exact ⟨675, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h13]; decide⟩
      · rcases key 7 with h7 | h7 | h7 | h7
        · exact ⟨48, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h7]; decide⟩
        · rcases key 11 with h11 | h11 | h11 | h11
          · exact ⟨99, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h11]; decide⟩
          · rcases key 13 with h13 | h13 | h13 | h13
            · exact ⟨13, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h7, h13]; decide⟩
            · exact ⟨26, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h13]; decide⟩
            · exact ⟨728, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h7, h13]; decide⟩
            · exact ⟨104, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h7, h13]; decide⟩
          · exact ⟨120, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h11]; decide⟩
          · rcases key 13 with h13 | h13 | h13 | h13
            · exact ⟨13, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h7, h13]; decide⟩
            · exact ⟨26, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h13]; decide⟩
            · exact ⟨728, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h7, h13]; decide⟩
            · exact ⟨104, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h7, h13]; decide⟩
        · exact ⟨27, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h7]; decide⟩
        · rcases key 11 with h11 | h11 | h11 | h11
          · exact ⟨99, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h11]; decide⟩
          · exact ⟨55, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h5, h7, h11]; decide⟩
          · exact ⟨120, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h11]; decide⟩
          · rcases key 13 with h13 | h13 | h13 | h13
            · exact ⟨39, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h13]; decide⟩
            · exact ⟨26, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h13]; decide⟩
            · exact ⟨168, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h7, h13]; decide⟩
            · rcases key 17 with h17 | h17 | h17 | h17
              · exact ⟨16, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h17]; decide⟩
              · exact ⟨119, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h7, h17]; decide⟩
              · exact ⟨935, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h11, h13, h17]; decide⟩
              · exact ⟨1224, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h7, h17]; decide⟩
    · rcases key 5 with h5 | h5 | h5 | h5
      · exact ⟨5, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5]; decide⟩
      · rcases key 7 with h7 | h7 | h7 | h7
        · exact ⟨6, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h7]; decide⟩
        · exact ⟨224, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h7]; decide⟩
        · rcases key 11 with h11 | h11 | h11 | h11
          · exact ⟨10, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h5, h11]; decide⟩
          · rcases key 13 with h13 | h13 | h13 | h13
            · exact ⟨168, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h7, h13]; decide⟩
            · exact ⟨351, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h11, h13]; decide⟩
            · exact ⟨168, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h7, h13]; decide⟩
            · exact ⟨104, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h7, h13]; decide⟩
          · exact ⟨99, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h11]; decide⟩
          · rcases key 13 with h13 | h13 | h13 | h13
            · exact ⟨168, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h7, h13]; decide⟩
            · rcases key 17 with h17 | h17 | h17 | h17
              · exact ⟨16, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h17]; decide⟩
              · exact ⟨33, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h11, h17]; decide⟩
              · exact ⟨153, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h7, h11, h17]; decide⟩
              · exact ⟨135, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h17]; decide⟩
            · exact ⟨168, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h7, h13]; decide⟩
            · exact ⟨104, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h7, h13]; decide⟩
        · exact ⟨35, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h7]; decide⟩
      · rcases key 7 with h7 | h7 | h7 | h7
        · exact ⟨6, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h7]; decide⟩
        · rcases key 11 with h11 | h11 | h11 | h11
          · exact ⟨120, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h11]; decide⟩
          · exact ⟨440, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h7, h11]; decide⟩
          · exact ⟨44, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h11]; decide⟩
          · rcases key 13 with h13 | h13 | h13 | h13
            · exact ⟨13, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h7, h13]; decide⟩
            · exact ⟨25, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h5, h13]; decide⟩
            · rcases key 17 with h17 | h17 | h17 | h17
              · exact ⟨16, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h17]; decide⟩
              · exact ⟨33, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h11, h17]; decide⟩
              · exact ⟨84, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h7, h17]; decide⟩
              · exact ⟨51, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h13, h17]; decide⟩
            · exact ⟨104, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h7, h13]; decide⟩
        · exact ⟨35, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h7]; decide⟩
        · exact ⟨20, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h7]; decide⟩
      · exact ⟨15, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5]; decide⟩
    · rcases key 5 with h5 | h5 | h5 | h5
      · exact ⟨80, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5]; decide⟩
      · exact ⟨9, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5]; decide⟩
      · exact ⟨15, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5]; decide⟩
      · rcases key 7 with h7 | h7 | h7 | h7
        · rcases key 11 with h11 | h11 | h11 | h11
          · exact ⟨11, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h11]; decide⟩
          · rcases key 13 with h13 | h13 | h13 | h13
            · exact ⟨12, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h13]; decide⟩
            · exact ⟨675, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h13]; decide⟩
            · exact ⟨39, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h13]; decide⟩
            · exact ⟨143, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h11, h13]; decide⟩
          · rcases key 13 with h13 | h13 | h13 | h13
            · exact ⟨12, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h13]; decide⟩
            · exact ⟨675, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h13]; decide⟩
            · exact ⟨39, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h13]; decide⟩
            · exact ⟨675, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h13]; decide⟩
          · rcases key 13 with h13 | h13 | h13 | h13
            · exact ⟨12, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h13]; decide⟩
            · exact ⟨65, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h11, h13]; decide⟩
            · exact ⟨39, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h13]; decide⟩
            · exact ⟨675, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h13]; decide⟩
        · rcases key 11 with h11 | h11 | h11 | h11
          · exact ⟨11, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h11]; decide⟩
          · rcases key 13 with h13 | h13 | h13 | h13
            · exact ⟨12, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h13]; decide⟩
            · exact ⟨363, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h7, h11, h13]; decide⟩
            · exact ⟨39, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h13]; decide⟩
            · exact ⟨143, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h11, h13]; decide⟩
          · rcases key 13 with h13 | h13 | h13 | h13
            · exact ⟨12, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h13]; decide⟩
            · exact ⟨675, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h13]; decide⟩
            · exact ⟨39, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h13]; decide⟩
            · exact ⟨195, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h7, h13]; decide⟩
          · rcases key 13 with h13 | h13 | h13 | h13
            · exact ⟨12, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h13]; decide⟩
            · exact ⟨65, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h11, h13]; decide⟩
            · exact ⟨39, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h13]; decide⟩
            · exact ⟨77, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h7, h11, h13]; decide⟩
        · rcases key 11 with h11 | h11 | h11 | h11
          · exact ⟨11, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h11]; decide⟩
          · exact ⟨21, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h7, h11]; decide⟩
          · rcases key 13 with h13 | h13 | h13 | h13
            · exact ⟨12, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h13]; decide⟩
            · exact ⟨675, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h13]; decide⟩
            · exact ⟨39, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h13]; decide⟩
            · exact ⟨77, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h7, h11, h13]; decide⟩
          · rcases key 13 with h13 | h13 | h13 | h13
            · exact ⟨12, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h13]; decide⟩
            · exact ⟨65, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h11, h13]; decide⟩
            · exact ⟨39, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h13]; decide⟩
            · exact ⟨675, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h13]; decide⟩
        · rcases key 11 with h11 | h11 | h11 | h11
          · exact ⟨11, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h11]; decide⟩
          · exact ⟨55, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h5, h7, h11]; decide⟩
          · rcases key 13 with h13 | h13 | h13 | h13
            · exact ⟨12, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h13]; decide⟩
            · exact ⟨675, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h13]; decide⟩
            · exact ⟨39, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h13]; decide⟩
            · exact ⟨104, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h7, h13]; decide⟩
          · rcases key 13 with h13 | h13 | h13 | h13
            · exact ⟨12, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h13]; decide⟩
            · exact ⟨65, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h11, h13]; decide⟩
            · exact ⟨39, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h13]; decide⟩
            · exact ⟨104, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h7, h13]; decide⟩
    · rcases key 5 with h5 | h5 | h5 | h5
      · exact ⟨24, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5]; decide⟩
      · exact ⟨15, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5]; decide⟩
      · exact ⟨24, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5]; decide⟩
      · rcases key 7 with h7 | h7 | h7 | h7
        · rcases key 11 with h11 | h11 | h11 | h11
          · rcases key 13 with h13 | h13 | h13 | h13
            · exact ⟨90, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h7, h13]; decide⟩
            · exact ⟨39, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h13]; decide⟩
            · exact ⟨77, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h7, h11, h13]; decide⟩
            · rcases key 17 with h17 | h17 | h17 | h17
              · exact ⟨16, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h17]; decide⟩
              · exact ⟨374, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h11, h17]; decide⟩
              · exact ⟨255, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h17]; decide⟩
              · exact ⟨135, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h17]; decide⟩
          · exact ⟨54, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h11]; decide⟩
          · exact ⟨99, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h11]; decide⟩
          · rcases key 13 with h13 | h13 | h13 | h13
            · exact ⟨90, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h7, h13]; decide⟩
            · exact ⟨39, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h13]; decide⟩
            · exact ⟨168, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h7, h13]; decide⟩
            · rcases key 17 with h17 | h17 | h17 | h17
              · exact ⟨16, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h17]; decide⟩
              · exact ⟨220, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h5, h11, h13, h17]; decide⟩
              · exact ⟨255, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h17]; decide⟩
              · exact ⟨135, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h17]; decide⟩
        · exact ⟨35, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h7]; decide⟩
        · rcases key 11 with h11 | h11 | h11 | h11
          · exact ⟨175, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h5, h7, h11]; decide⟩
          · exact ⟨54, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h11]; decide⟩
          · exact ⟨99, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h11]; decide⟩
          · exact ⟨384, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h7, h11]; decide⟩
        · rcases key 11 with h11 | h11 | h11 | h11
          · exact ⟨440, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h7, h11]; decide⟩
          · exact ⟨54, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h11]; decide⟩
          · exact ⟨99, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h11]; decide⟩
          · rcases key 13 with h13 | h13 | h13 | h13
            · rcases key 17 with h17 | h17 | h17 | h17
              · exact ⟨16, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h17]; decide⟩
              · exact ⟨84, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h7, h17]; decide⟩
              · exact ⟨169, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h5, h13, h17]; decide⟩
              · exact ⟨135, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h17]; decide⟩
            · exact ⟨39, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h13]; decide⟩
            · exact ⟨195, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h7, h13]; decide⟩
            · exact ⟨350, Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, by simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h2, h3, h5, h7, h13]; decide⟩

end OMA436ft

theorem OMA.solution : OMA.R_Erdos436_erdos_436_variants_four_two_R1.H1 := OMA436ft.main_H1
