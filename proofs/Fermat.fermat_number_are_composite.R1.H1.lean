import OMAReductions.R_Fermat_fermat_number_are_composite_R1

-- The Fermat numbers F_5, ..., F_19 are composite.
-- Each case is a known prime factor from the literature (641 for F_5, Euler 1732; 274177 for F_6, Landry 1880;
-- ...; 70525124609 for F_19, Riesel 1962; the 54-digit factor of F_14 is from 2010, Rajala and Woltman).
-- The Lean proof is original: the kernel checks that each number divides the Fermat number and lies strictly
-- between 1 and it. Known cases, not progress on the open question for all n.

namespace OMA.FermatComposite

lemma comp (n d : ℕ) (h : 2 ≤ d ∧ d < n.fermatNumber ∧ n.fermatNumber % d = 0) :
    ¬ Prime n.fermatNumber := by
  rw [← Nat.prime_iff]
  intro hp
  have hd : d ∣ n.fermatNumber := Nat.dvd_of_mod_eq_zero h.2.2
  rcases (Nat.dvd_prime hp).mp hd with h1 | h1
  · omega
  · omega

theorem range (n : ℕ) (h4 : 4 < n) (h19 : n ≤ 19) : ¬ Prime n.fermatNumber := by
  interval_cases n
  · exact comp 5 641 (by decide +kernel)
  · exact comp 6 274177 (by decide +kernel)
  · exact comp 7 59649589127497217 (by decide +kernel)
  · exact comp 8 1238926361552897 (by decide +kernel)
  · exact comp 9 2424833 (by decide +kernel)
  · exact comp 10 45592577 (by decide +kernel)
  · exact comp 11 319489 (by decide +kernel)
  · exact comp 12 114689 (by decide +kernel)
  · exact comp 13 2710954639361 (by decide +kernel)
  · exact comp 14 116928085873074369829035993834596371340386703423373313 (by decide +kernel)
  · exact comp 15 1214251009 (by decide +kernel)
  · exact comp 16 825753601 (by decide +kernel)
  · exact comp 17 31065037602817 (by decide +kernel)
  · exact comp 18 13631489 (by decide +kernel)
  · exact comp 19 70525124609 (by decide +kernel)

end OMA.FermatComposite

theorem OMA.solution : OMA.R_Fermat_fermat_number_are_composite_R1.H1 := by
  intro n h4 h19
  exact OMA.FermatComposite.range n h4 h19
