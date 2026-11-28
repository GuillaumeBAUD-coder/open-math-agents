import OMAReductions.R_Erdos436_erdos_436_variants_four_two_R1
import Mathlib

-- Step Erdos436.erdos_436.variants.four_two.R1.H1: hypothesis H1 of reduction Erdos436.erdos_436.variants.four_two.R1
-- Credit: @luciusacarr

/-! Finite case split on the values `w p ∈ ZMod 4` of the primes `p` (in increasing order), stopping as soon
as some `n ≤ 1224` has both weighted factor sums of `n` and `n + 1` equal to `0`: a search tree of 669 nodes.
Each leaf `L n` checks its witness `n` from the case hypotheses in scope (through the auto-param). -/

namespace OMA436ft

lemma K : ∀ x : ZMod 4, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by decide

lemma L {w : ℕ → ZMod 4} (n : ℕ) (h1 : 1 ≤ n ∧ n ≤ 1224 := by decide)
    (h : (n.primeFactorsList.map w).sum = 0 ∧ ((n + 1).primeFactorsList.map w).sum = 0 := by
      simp only [Nat.reduceAdd, Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, *] <;> decide) :
    ∃ n ∈ Finset.Icc 1 1224, (n.primeFactorsList.map w).sum = 0 ∧ ((n + 1).primeFactorsList.map w).sum = 0 :=
  ⟨n, Finset.mem_Icc.2 h1, h⟩

end OMA436ft

open OMA436ft in
theorem OMA.solution : OMA.R_Erdos436_erdos_436_variants_four_two_R1.H1 := by
  intro w
  obtain h | h | h | h := K (w 2)
  · exact L 1
  · obtain h | h | h | h := K (w 3)
    · obtain h | h | h | h := K (w 5)
      · exact L 15
      · obtain h | h | h | h := K (w 7)
        · exact L 48
        · obtain h | h | h | h := K (w 11)
          · exact L 99
          · obtain h | h | h | h := K (w 13)
            · exact L 39
            · obtain h | h | h | h := K (w 17)
              · exact L 16
              · exact L 1224
              · exact L 935
              · exact L 119
            · exact L 168
            · exact L 26
          · exact L 120
          · exact L 55
        · exact L 27
        · obtain h | h | h | h := K (w 11)
          · exact L 99
          · obtain h | h | h | h := K (w 13)
            · exact L 13
            · exact L 104
            · exact L 728
            · exact L 26
          · exact L 120
          · obtain h | h | h | h := K (w 13)
            · exact L 13
            · exact L 104
            · exact L 728
            · exact L 26
      · obtain h | h | h | h := K (w 7)
        · exact L 20
        · obtain h | h | h | h := K (w 11)
          · obtain h | h | h | h := K (w 13)
            · exact L 143
            · exact L 363
            · exact L 168
            · exact L 25
          · obtain h | h | h | h := K (w 13)
            · exact L 168
            · exact L 675
            · exact L 168
            · exact L 25
          · exact L 55
          · obtain h | h | h | h := K (w 13)
            · exact L 168
            · exact L 143
            · exact L 65
            · exact L 25
        · exact L 27
        · exact L 224
      · exact L 9
    · obtain h | h | h | h := K (w 5)
      · exact L 24
      · obtain h | h | h | h := K (w 7)
        · obtain h | h | h | h := K (w 11)
          · obtain h | h | h | h := K (w 13)
            · exact L 90
            · obtain h | h | h | h := K (w 17)
              · exact L 16
              · exact L 135
              · exact L 255
              · exact L 374
            · exact L 77
            · exact L 39
          · obtain h | h | h | h := K (w 13)
            · exact L 90
            · obtain h | h | h | h := K (w 17)
              · exact L 16
              · exact L 135
              · exact L 255
              · exact L 220
            · exact L 168
            · exact L 39
          · exact L 99
          · exact L 54
        · obtain h | h | h | h := K (w 11)
          · exact L 440
          · obtain h | h | h | h := K (w 13)
            · obtain h | h | h | h := K (w 17)
              · exact L 16
              · exact L 135
              · exact L 169
              · exact L 84
            · exact L 350
            · exact L 195
            · exact L 39
          · exact L 99
          · exact L 54
        · obtain h | h | h | h := K (w 11)
          · exact L 175
          · exact L 384
          · exact L 99
          · exact L 54
        · exact L 35
      · exact L 24
      · exact L 15
    · obtain h | h | h | h := K (w 5)
      · exact L 80
      · obtain h | h | h | h := K (w 7)
        · obtain h | h | h | h := K (w 11)
          · exact L 11
          · obtain h | h | h | h := K (w 13)
            · exact L 12
            · exact L 675
            · exact L 39
            · exact L 65
          · obtain h | h | h | h := K (w 13)
            · exact L 12
            · exact L 675
            · exact L 39
            · exact L 675
          · obtain h | h | h | h := K (w 13)
            · exact L 12
            · exact L 143
            · exact L 39
            · exact L 675
        · obtain h | h | h | h := K (w 11)
          · exact L 11
          · obtain h | h | h | h := K (w 13)
            · exact L 12
            · exact L 104
            · exact L 39
            · exact L 65
          · obtain h | h | h | h := K (w 13)
            · exact L 12
            · exact L 104
            · exact L 39
            · exact L 675
          · exact L 55
        · obtain h | h | h | h := K (w 11)
          · exact L 11
          · obtain h | h | h | h := K (w 13)
            · exact L 12
            · exact L 675
            · exact L 39
            · exact L 65
          · obtain h | h | h | h := K (w 13)
            · exact L 12
            · exact L 77
            · exact L 39
            · exact L 675
          · exact L 21
        · obtain h | h | h | h := K (w 11)
          · exact L 11
          · obtain h | h | h | h := K (w 13)
            · exact L 12
            · exact L 77
            · exact L 39
            · exact L 65
          · obtain h | h | h | h := K (w 13)
            · exact L 12
            · exact L 195
            · exact L 39
            · exact L 675
          · obtain h | h | h | h := K (w 13)
            · exact L 12
            · exact L 143
            · exact L 39
            · exact L 363
      · exact L 15
      · exact L 9
    · obtain h | h | h | h := K (w 5)
      · exact L 5
      · exact L 15
      · obtain h | h | h | h := K (w 7)
        · exact L 6
        · exact L 20
        · exact L 35
        · obtain h | h | h | h := K (w 11)
          · exact L 120
          · obtain h | h | h | h := K (w 13)
            · exact L 13
            · exact L 104
            · obtain h | h | h | h := K (w 17)
              · exact L 16
              · exact L 51
              · exact L 84
              · exact L 33
            · exact L 25
          · exact L 44
          · exact L 440
      · obtain h | h | h | h := K (w 7)
        · exact L 6
        · exact L 35
        · obtain h | h | h | h := K (w 11)
          · exact L 10
          · obtain h | h | h | h := K (w 13)
            · exact L 168
            · exact L 104
            · exact L 168
            · obtain h | h | h | h := K (w 17)
              · exact L 16
              · exact L 135
              · exact L 153
              · exact L 33
          · exact L 99
          · obtain h | h | h | h := K (w 13)
            · exact L 168
            · exact L 104
            · exact L 168
            · exact L 351
        · exact L 224
  · obtain h | h | h | h := K (w 3)
    · exact L 3
    · obtain h | h | h | h := K (w 5)
      · exact L 4
      · obtain h | h | h | h := K (w 7)
        · exact L 49
        · obtain h | h | h | h := K (w 11)
          · exact L 120
          · exact L 440
          · exact L 98
          · obtain h | h | h | h := K (w 13)
            · exact L 168
            · exact L 77
            · exact L 168
            · exact L 64
        · exact L 49
        · obtain h | h | h | h := K (w 11)
          · exact L 120
          · exact L 440
          · exact L 21
          · obtain h | h | h | h := K (w 13)
            · obtain h | h | h | h := K (w 17)
              · exact L 16
              · exact L 119
              · exact L 33
              · exact L 50
            · obtain h | h | h | h := K (w 17)
              · exact L 16
              · exact L 119
              · exact L 33
              · exact L 50
            · exact L 324
            · exact L 64
      · obtain h | h | h | h := K (w 7)
        · obtain h | h | h | h := K (w 11)
          · exact L 10
          · obtain h | h | h | h := K (w 13)
            · exact L 324
            · exact L 195
            · exact L 25
            · exact L 39
          · exact L 99
          · obtain h | h | h | h := K (w 13)
            · exact L 324
            · exact L 195
            · exact L 25
            · exact L 39
        · obtain h | h | h | h := K (w 11)
          · exact L 10
          · obtain h | h | h | h := K (w 13)
            · exact L 168
            · obtain h | h | h | h := K (w 17)
              · exact L 16
              · exact L 255
              · exact L 153
              · obtain h | h | h | h := K (w 19)
                · exact L 18
                · exact L 285
                · exact L 399
                · obtain h | h | h | h := K (w 23)
                  · obtain h | h | h | h := K (w 29)
                    · obtain h | h | h | h := K (w 31)
                      · obtain h | h | h | h := K (w 37)
                        · exact L 666
                        · exact L 221
                        · exact L 296
                        · exact L 1035
                      · exact L 186
                      · exact L 154
                      · exact L 92
                    · obtain h | h | h | h := K (w 31)
                      · obtain h | h | h | h := K (w 37)
                        · obtain h | h | h | h := K (w 41)
                          · exact L 40
                          · exact L 245
                          · exact L 81
                          · exact L 123
                        · exact L 221
                        · exact L 296
                        · exact L 406
                      · exact L 186
                      · exact L 154
                      · exact L 92
                    · exact L 57
                    · exact L 203
                  · exact L 391
                  · exact L 45
                  · exact L 160
            · exact L 25
            · exact L 39
          · exact L 98
          · obtain h | h | h | h := K (w 13)
            · exact L 168
            · exact L 77
            · exact L 25
            · exact L 39
        · exact L 63
        · obtain h | h | h | h := K (w 11)
          · exact L 10
          · obtain h | h | h | h := K (w 13)
            · exact L 324
            · exact L 77
            · exact L 25
            · exact L 39
          · exact L 21
          · obtain h | h | h | h := K (w 13)
            · exact L 324
            · obtain h | h | h | h := K (w 17)
              · exact L 16
              · exact L 255
              · exact L 33
              · exact L 594
            · exact L 25
            · exact L 39
      · exact L 15
    · obtain h | h | h | h := K (w 5)
      · exact L 4
      · obtain h | h | h | h := K (w 7)
        · exact L 6
        · obtain h | h | h | h := K (w 11)
          · exact L 98
          · obtain h | h | h | h := K (w 13)
            · exact L 675
            · exact L 728
            · exact L 104
            · exact L 64
          · exact L 384
          · exact L 54
        · exact L 49
        · exact L 35
      · exact L 9
      · obtain h | h | h | h := K (w 7)
        · exact L 6
        · exact L 35
        · exact L 49
        · obtain h | h | h | h := K (w 11)
          · exact L 98
          · exact L 54
          · exact L 384
          · obtain h | h | h | h := K (w 13)
            · exact L 675
            · exact L 64
            · exact L 104
            · exact L 728
    · obtain h | h | h | h := K (w 5)
      · exact L 4
      · exact L 15
      · obtain h | h | h | h := K (w 7)
        · obtain h | h | h | h := K (w 11)
          · exact L 10
          · obtain h | h | h | h := K (w 13)
            · exact L 324
            · exact L 39
            · exact L 25
            · exact L 195
          · exact L 99
          · obtain h | h | h | h := K (w 13)
            · exact L 324
            · exact L 39
            · exact L 25
            · exact L 195
        · obtain h | h | h | h := K (w 11)
          · exact L 10
          · obtain h | h | h | h := K (w 13)
            · exact L 324
            · exact L 39
            · exact L 25
            · obtain h | h | h | h := K (w 17)
              · exact L 16
              · exact L 594
              · exact L 33
              · exact L 255
          · exact L 21
          · obtain h | h | h | h := K (w 13)
            · exact L 324
            · exact L 39
            · exact L 25
            · exact L 77
        · exact L 63
        · obtain h | h | h | h := K (w 11)
          · exact L 10
          · obtain h | h | h | h := K (w 13)
            · exact L 168
            · exact L 39
            · exact L 25
            · exact L 77
          · exact L 98
          · obtain h | h | h | h := K (w 13)
            · exact L 168
            · exact L 39
            · exact L 25
            · obtain h | h | h | h := K (w 17)
              · exact L 16
              · obtain h | h | h | h := K (w 19)
                · exact L 18
                · obtain h | h | h | h := K (w 23)
                  · obtain h | h | h | h := K (w 29)
                    · obtain h | h | h | h := K (w 31)
                      · obtain h | h | h | h := K (w 37)
                        · exact L 666
                        · exact L 1035
                        · exact L 296
                        · exact L 221
                      · exact L 92
                      · exact L 154
                      · exact L 186
                    · exact L 203
                    · exact L 57
                    · obtain h | h | h | h := K (w 31)
                      · obtain h | h | h | h := K (w 37)
                        · obtain h | h | h | h := K (w 41)
                          · exact L 40
                          · exact L 123
                          · exact L 81
                          · exact L 245
                        · exact L 406
                        · exact L 296
                        · exact L 221
                      · exact L 92
                      · exact L 154
                      · exact L 186
                  · exact L 160
                  · exact L 45
                  · exact L 391
                · exact L 399
                · exact L 285
              · exact L 153
              · exact L 255
      · obtain h | h | h | h := K (w 7)
        · exact L 49
        · obtain h | h | h | h := K (w 11)
          · exact L 120
          · obtain h | h | h | h := K (w 13)
            · obtain h | h | h | h := K (w 17)
              · exact L 16
              · exact L 50
              · exact L 33
              · exact L 119
            · exact L 64
            · exact L 324
            · obtain h | h | h | h := K (w 17)
              · exact L 16
              · exact L 50
              · exact L 33
              · exact L 119
          · exact L 21
          · exact L 440
        · exact L 49
        · obtain h | h | h | h := K (w 11)
          · exact L 120
          · obtain h | h | h | h := K (w 13)
            · exact L 168
            · exact L 64
            · exact L 168
            · exact L 77
          · exact L 98
          · exact L 440
  · obtain h | h | h | h := K (w 3)
    · obtain h | h | h | h := K (w 5)
      · exact L 15
      · exact L 9
      · obtain h | h | h | h := K (w 7)
        · exact L 20
        · exact L 224
        · exact L 27
        · obtain h | h | h | h := K (w 11)
          · obtain h | h | h | h := K (w 13)
            · exact L 143
            · exact L 25
            · exact L 168
            · exact L 363
          · obtain h | h | h | h := K (w 13)
            · exact L 168
            · exact L 25
            · exact L 65
            · exact L 143
          · exact L 55
          · obtain h | h | h | h := K (w 13)
            · exact L 168
            · exact L 25
            · exact L 168
            · exact L 675
      · obtain h | h | h | h := K (w 7)
        · exact L 48
        · obtain h | h | h | h := K (w 11)
          · exact L 99
          · obtain h | h | h | h := K (w 13)
            · exact L 13
            · exact L 26
            · exact L 728
            · exact L 104
          · exact L 120
          · obtain h | h | h | h := K (w 13)
            · exact L 13
            · exact L 26
            · exact L 728
            · exact L 104
        · exact L 27
        · obtain h | h | h | h := K (w 11)
          · exact L 99
          · exact L 55
          · exact L 120
          · obtain h | h | h | h := K (w 13)
            · exact L 39
            · exact L 26
            · exact L 168
            · obtain h | h | h | h := K (w 17)
              · exact L 16
              · exact L 119
              · exact L 935
              · exact L 1224
    · obtain h | h | h | h := K (w 5)
      · exact L 5
      · obtain h | h | h | h := K (w 7)
        · exact L 6
        · exact L 224
        · obtain h | h | h | h := K (w 11)
          · exact L 10
          · obtain h | h | h | h := K (w 13)
            · exact L 168
            · exact L 351
            · exact L 168
            · exact L 104
          · exact L 99
          · obtain h | h | h | h := K (w 13)
            · exact L 168
            · obtain h | h | h | h := K (w 17)
              · exact L 16
              · exact L 33
              · exact L 153
              · exact L 135
            · exact L 168
            · exact L 104
        · exact L 35
      · obtain h | h | h | h := K (w 7)
        · exact L 6
        · obtain h | h | h | h := K (w 11)
          · exact L 120
          · exact L 440
          · exact L 44
          · obtain h | h | h | h := K (w 13)
            · exact L 13
            · exact L 25
            · obtain h | h | h | h := K (w 17)
              · exact L 16
              · exact L 33
              · exact L 84
              · exact L 51
            · exact L 104
        · exact L 35
        · exact L 20
      · exact L 15
    · obtain h | h | h | h := K (w 5)
      · exact L 80
      · exact L 9
      · exact L 15
      · obtain h | h | h | h := K (w 7)
        · obtain h | h | h | h := K (w 11)
          · exact L 11
          · obtain h | h | h | h := K (w 13)
            · exact L 12
            · exact L 675
            · exact L 39
            · exact L 143
          · obtain h | h | h | h := K (w 13)
            · exact L 12
            · exact L 675
            · exact L 39
            · exact L 675
          · obtain h | h | h | h := K (w 13)
            · exact L 12
            · exact L 65
            · exact L 39
            · exact L 675
        · obtain h | h | h | h := K (w 11)
          · exact L 11
          · obtain h | h | h | h := K (w 13)
            · exact L 12
            · exact L 363
            · exact L 39
            · exact L 143
          · obtain h | h | h | h := K (w 13)
            · exact L 12
            · exact L 675
            · exact L 39
            · exact L 195
          · obtain h | h | h | h := K (w 13)
            · exact L 12
            · exact L 65
            · exact L 39
            · exact L 77
        · obtain h | h | h | h := K (w 11)
          · exact L 11
          · exact L 21
          · obtain h | h | h | h := K (w 13)
            · exact L 12
            · exact L 675
            · exact L 39
            · exact L 77
          · obtain h | h | h | h := K (w 13)
            · exact L 12
            · exact L 65
            · exact L 39
            · exact L 675
        · obtain h | h | h | h := K (w 11)
          · exact L 11
          · exact L 55
          · obtain h | h | h | h := K (w 13)
            · exact L 12
            · exact L 675
            · exact L 39
            · exact L 104
          · obtain h | h | h | h := K (w 13)
            · exact L 12
            · exact L 65
            · exact L 39
            · exact L 104
    · obtain h | h | h | h := K (w 5)
      · exact L 24
      · exact L 15
      · exact L 24
      · obtain h | h | h | h := K (w 7)
        · obtain h | h | h | h := K (w 11)
          · obtain h | h | h | h := K (w 13)
            · exact L 90
            · exact L 39
            · exact L 77
            · obtain h | h | h | h := K (w 17)
              · exact L 16
              · exact L 374
              · exact L 255
              · exact L 135
          · exact L 54
          · exact L 99
          · obtain h | h | h | h := K (w 13)
            · exact L 90
            · exact L 39
            · exact L 168
            · obtain h | h | h | h := K (w 17)
              · exact L 16
              · exact L 220
              · exact L 255
              · exact L 135
        · exact L 35
        · obtain h | h | h | h := K (w 11)
          · exact L 175
          · exact L 54
          · exact L 99
          · exact L 384
        · obtain h | h | h | h := K (w 11)
          · exact L 440
          · exact L 54
          · exact L 99
          · obtain h | h | h | h := K (w 13)
            · obtain h | h | h | h := K (w 17)
              · exact L 16
              · exact L 84
              · exact L 169
              · exact L 135
            · exact L 39
            · exact L 195
            · exact L 350

