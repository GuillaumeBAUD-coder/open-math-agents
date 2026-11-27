import OMAReductions.R_Fermat_fermat_number_are_composite_R1
import Mathlib

-- Step Fermat.fermat_number_are_composite.R1.H1: hypothesis H1 of reduction Fermat.fermat_number_are_composite.R1
-- Credit: @ivillar

/-!
The Fermat numbers `F_5, ..., F_19` are composite: each has an explicit known prime factor
(Euler, Landry, Morrison-Brillhart, Brent-Pollard, Western, Selfridge, Hallyburton-Brillhart,
Rajala-Woltman, Kraitchik, Gostin, ...), and divisibility is checked by kernel evaluation.
-/
namespace F2Fermat

theorem comp (n d : ℕ) (h1 : 2 ≤ d) (hd : d ∣ 2 ^ (2 ^ n) + 1) (h2 : d < 2 ^ (2 ^ n) + 1) :
    ¬ Prime n.fermatNumber := by
  rw [← Nat.prime_iff]
  exact Nat.not_prime_of_dvd_of_lt hd h1 h2

theorem small : ∀ n : ℕ, 4 < n → n ≤ 19 → ¬ Prime n.fermatNumber := by
  intro n h4 h19
  interval_cases n
  · exact comp 5 641 (by norm_num) (by decide +kernel) (by decide +kernel)
  · exact comp 6 274177 (by norm_num) (by decide +kernel) (by decide +kernel)
  · exact comp 7 59649589127497217 (by norm_num) (by decide +kernel) (by decide +kernel)
  · exact comp 8 1238926361552897 (by norm_num) (by decide +kernel) (by decide +kernel)
  · exact comp 9 2424833 (by norm_num) (by decide +kernel) (by decide +kernel)
  · exact comp 10 45592577 (by norm_num) (by decide +kernel) (by decide +kernel)
  · exact comp 11 319489 (by norm_num) (by decide +kernel) (by decide +kernel)
  · exact comp 12 114689 (by norm_num) (by decide +kernel) (by decide +kernel)
  · exact comp 13 2710954639361 (by norm_num) (by decide +kernel) (by decide +kernel)
  · exact comp 14 116928085873074369829035993834596371340386703423373313 (by norm_num) (by decide +kernel) (by decide +kernel)
  · exact comp 15 1214251009 (by norm_num) (by decide +kernel) (by decide +kernel)
  · exact comp 16 825753601 (by norm_num) (by decide +kernel) (by decide +kernel)
  · exact comp 17 31065037602817 (by norm_num) (by decide +kernel) (by decide +kernel)
  · exact comp 18 13631489 (by norm_num) (by decide +kernel) (by decide +kernel)
  · exact comp 19 70525124609 (by norm_num) (by decide +kernel) (by decide +kernel)

end F2Fermat

theorem OMA.solution : OMA.R_Fermat_fermat_number_are_composite_R1.H1 :=
  F2Fermat.small
