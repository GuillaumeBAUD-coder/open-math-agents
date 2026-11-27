import OMAReductions.R_Fermat_fermat_number_are_composite_R1

-- Step Fermat.fermat_number_are_composite.R1.H1: hypothesis H1 of reduction
-- Fermat.fermat_number_are_composite.R1
-- Credit: @JamesSlash. Each F_n (5 <= n <= 19) has a known proper factor (Euler, Landry, Morehead,
-- Western, Brillhart-Morrison, Brent, Rajala et al.; the 54-digit factor of F_14 is due to Rajala,
-- Woltman, Kruppa 2010). The divisibilities are checked by kernel arithmetic.

namespace OMAFermatH1

theorem not_prime_of_factor (n q : ℕ) (h2 : 2 ≤ q) (hlt : q < 2 ^ 2 ^ n + 1)
    (hdvd : (2 ^ 2 ^ n + 1) % q = 0) : ¬ Prime n.fermatNumber := by
  rw [← Nat.prime_iff]
  exact Nat.not_prime_of_dvd_of_lt (Nat.dvd_of_mod_eq_zero hdvd) h2 hlt

end OMAFermatH1

theorem OMA.solution : OMA.R_Fermat_fermat_number_are_composite_R1.H1 := by
  intro n h4 h19
  interval_cases n
  · exact OMAFermatH1.not_prime_of_factor 5 641 (by norm_num) (by decide +kernel) (by decide +kernel)
  · exact OMAFermatH1.not_prime_of_factor 6 274177 (by norm_num) (by decide +kernel) (by decide +kernel)
  · exact OMAFermatH1.not_prime_of_factor 7 59649589127497217 (by norm_num) (by decide +kernel) (by decide +kernel)
  · exact OMAFermatH1.not_prime_of_factor 8 1238926361552897 (by norm_num) (by decide +kernel) (by decide +kernel)
  · exact OMAFermatH1.not_prime_of_factor 9 2424833 (by norm_num) (by decide +kernel) (by decide +kernel)
  · exact OMAFermatH1.not_prime_of_factor 10 45592577 (by norm_num) (by decide +kernel) (by decide +kernel)
  · exact OMAFermatH1.not_prime_of_factor 11 319489 (by norm_num) (by decide +kernel) (by decide +kernel)
  · exact OMAFermatH1.not_prime_of_factor 12 114689 (by norm_num) (by decide +kernel) (by decide +kernel)
  · exact OMAFermatH1.not_prime_of_factor 13 2710954639361 (by norm_num) (by decide +kernel) (by decide +kernel)
  · exact OMAFermatH1.not_prime_of_factor 14 116928085873074369829035993834596371340386703423373313
      (by norm_num) (by decide +kernel) (by decide +kernel)
  · exact OMAFermatH1.not_prime_of_factor 15 1214251009 (by norm_num) (by decide +kernel) (by decide +kernel)
  · exact OMAFermatH1.not_prime_of_factor 16 825753601 (by norm_num) (by decide +kernel) (by decide +kernel)
  · exact OMAFermatH1.not_prime_of_factor 17 31065037602817 (by norm_num) (by decide +kernel) (by decide +kernel)
  · exact OMAFermatH1.not_prime_of_factor 18 13631489 (by norm_num) (by decide +kernel) (by decide +kernel)
  · exact OMAFermatH1.not_prime_of_factor 19 70525124609 (by norm_num) (by decide +kernel) (by decide +kernel)
