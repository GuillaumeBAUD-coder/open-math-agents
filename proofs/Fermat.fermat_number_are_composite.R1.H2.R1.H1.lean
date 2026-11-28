import OMAReductions.R_Fermat_fermat_number_are_composite_R1_H2_R1

-- Step Fermat.fermat_number_are_composite.R1.H2.R1.H1: hypothesis H1 of reduction
-- Fermat.fermat_number_are_composite.R1.H2.R1
-- Credit: @luciusacarr. Each listed F_n has a known prime factor q = k * 2^m + 1 (W. Keller,
-- "Prime factors k * 2^n + 1 of Fermat numbers F_m and complete factoring status",
-- http://www.prothsearch.com/fermat.html). The divisibility 2^(2^n) = -1 mod q is checked in the
-- kernel by n modular squarings, so F_n itself is never computed.

/-! Known factors of the Fermat numbers listed in H1. -/

namespace OMAFermatH2R1H1

/-- `sq q k = 2 ^ (2 ^ k) % q`, computed by repeated squaring modulo `q`. -/
def sq (q : ℕ) : ℕ → ℕ
  | 0 => 2 % q
  | k + 1 => (sq q k) ^ 2 % q

theorem sq_eq (q k : ℕ) : sq q k = 2 ^ (2 ^ k) % q := by
  induction k with
  | zero => simp [sq]
  | succ k ih => rw [sq, ih, ← Nat.pow_mod, pow_succ 2 k, pow_mul]

theorem key (n q : ℕ) (hn : 21 ≤ n) (h2 : 2 ≤ q) (hq : q < 2 ^ 2000)
    (hm : (sq q n + 1) % q = 0) : ¬ Prime n.fermatNumber := by
  rw [← Nat.prime_iff]
  have hdvd : q ∣ 2 ^ 2 ^ n + 1 := by
    apply Nat.dvd_of_mod_eq_zero
    rw [Nat.add_mod, ← sq_eq]
    rcases Nat.lt_or_ge q 2 with h | h
    · omega
    · rw [Nat.one_mod_eq_one.mpr (by omega)]
      exact hm
  have h21 : 2 ^ 21 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hlt : q < 2 ^ 2 ^ n + 1 := by
    have : 2 ^ 2000 ≤ 2 ^ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (le_trans (by norm_num) h21)
    exact Nat.lt_succ_of_lt (lt_of_lt_of_le hq this)
  exact Nat.not_prime_of_dvd_of_lt hdvd h2 hlt

end OMAFermatH2R1H1

theorem OMA.solution : OMA.R_Fermat_fermat_number_are_composite_R1_H2_R1.H1 := by
  intro n hn
  simp only [Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact OMAFermatH2R1H1.key 21 4485296422913 (by norm_num) (by norm_num) (by decide +kernel)
      (by decide +kernel)
  · exact OMAFermatH2R1H1.key 22 64658705994591851009055774868504577 (by norm_num) (by norm_num) (by decide +kernel)
      (by decide +kernel)
  · exact OMAFermatH2R1H1.key 23 167772161 (by norm_num) (by norm_num) (by decide +kernel)
      (by decide +kernel)
  · exact OMAFermatH2R1H1.key 25 25991531462657 (by norm_num) (by norm_num) (by decide +kernel)
      (by decide +kernel)
  · exact OMAFermatH2R1H1.key 26 76861124116481 (by norm_num) (by norm_num) (by decide +kernel)
      (by decide +kernel)
  · exact OMAFermatH2R1H1.key 27 151413703311361 (by norm_num) (by norm_num) (by decide +kernel)
      (by decide +kernel)
  · exact OMAFermatH2R1H1.key 28 1766730974551267606529 (by norm_num) (by norm_num) (by decide +kernel)
      (by decide +kernel)
  · exact OMAFermatH2R1H1.key 29 2405286912458753 (by norm_num) (by norm_num) (by decide +kernel)
      (by decide +kernel)
  · exact OMAFermatH2R1H1.key 30 640126220763137 (by norm_num) (by norm_num) (by decide +kernel)
      (by decide +kernel)
  · exact OMAFermatH2R1H1.key 31 46931635677864055013377 (by norm_num) (by norm_num) (by decide +kernel)
      (by decide +kernel)
  · exact OMAFermatH2R1H1.key 32 25409026523137 (by norm_num) (by norm_num) (by decide +kernel)
      (by decide +kernel)
  · exact OMAFermatH2R1H1.key 36 2748779069441 (by norm_num) (by norm_num) (by decide +kernel)
      (by decide +kernel)
  · exact OMAFermatH2R1H1.key 37 701179711390136401921 (by norm_num) (by norm_num) (by decide +kernel)
      (by decide +kernel)
  · exact OMAFermatH2R1H1.key 38 6597069766657 (by norm_num) (by norm_num) (by decide +kernel)
      (by decide +kernel)
  · exact OMAFermatH2R1H1.key 39 46179488366593 (by norm_num) (by norm_num) (by decide +kernel)
      (by decide +kernel)
  · exact OMAFermatH2R1H1.key 42 1529992420282859521 (by norm_num) (by norm_num) (by decide +kernel)
      (by decide +kernel)
  · exact OMAFermatH2R1H1.key 43 7482850493766970889994241 (by norm_num) (by norm_num) (by decide +kernel)
      (by decide +kernel)
  · exact OMAFermatH2R1H1.key 48 2408911986953445595315961857 (by norm_num) (by norm_num) (by decide +kernel)
      (by decide +kernel)
  · exact OMAFermatH2R1H1.key 52 74201307460556292097 (by norm_num) (by norm_num) (by decide +kernel)
      (by decide +kernel)
  · exact OMAFermatH2R1H1.key 55 4179340454199820289 (by norm_num) (by norm_num) (by decide +kernel)
      (by decide +kernel)
  · exact OMAFermatH2R1H1.key 58 219055085875300925441 (by norm_num) (by norm_num) (by decide +kernel)
      (by decide +kernel)
  · exact OMAFermatH2R1H1.key 61 4057181540151185357230047233 (by norm_num) (by norm_num) (by decide +kernel)
      (by decide +kernel)
  · exact OMAFermatH2R1H1.key 62 12857380619375557476353 (by norm_num) (by norm_num) (by decide +kernel)
      (by decide +kernel)
  · exact OMAFermatH2R1H1.key 63 1328165573307087716353 (by norm_num) (by norm_num) (by decide +kernel)
      (by decide +kernel)
  · exact OMAFermatH2R1H1.key 64 2634732075339197803231444993 (by norm_num) (by norm_num) (by decide +kernel)
      (by decide +kernel)
  · exact OMAFermatH2R1H1.key 66 4457323664018586376077313 (by norm_num) (by norm_num) (by decide +kernel)
      (by decide +kernel)
  · exact OMAFermatH2R1H1.key 71 6450752615599935361908737 (by norm_num) (by norm_num) (by decide +kernel)
      (by decide +kernel)
  · exact OMAFermatH2R1H1.key 72 1443765874709062348345951911937 (by norm_num) (by norm_num) (by decide +kernel)
      (by decide +kernel)
  · exact OMAFermatH2R1H1.key 73 188894659314785808547841 (by norm_num) (by norm_num) (by decide +kernel)
      (by decide +kernel)
  · exact OMAFermatH2R1H1.key 75 520961043404985083798310879233 (by norm_num) (by norm_num) (by decide +kernel)
      (by decide +kernel)
  · exact OMAFermatH2R1H1.key 77 256896736668108699625062401 (by norm_num) (by norm_num) (by decide +kernel)
      (by decide +kernel)
  · exact OMAFermatH2R1H1.key 81 5241902353849032101525979137 (by norm_num) (by norm_num) (by decide +kernel)
      (by decide +kernel)
  · exact OMAFermatH2R1H1.key 91 14072902366596202965053244178433 (by norm_num) (by norm_num) (by decide +kernel)
      (by decide +kernel)
  · exact OMAFermatH2R1H1.key 99 329244355096077565991935730125897729 (by norm_num) (by norm_num) (by decide +kernel)
      (by decide +kernel)
  · exact OMAFermatH2R1H1.key 107 3346902437331832346018436558958369334886401 (by norm_num) (by norm_num) (by decide +kernel)
      (by decide +kernel)
  · exact OMAFermatH2R1H1.key 117 9304595970494411110326649421962412033 (by norm_num) (by norm_num) (by decide +kernel)
      (by decide +kernel)
  · exact OMAFermatH2R1H1.key 122 111331351706159727817280425663664652445286401 (by norm_num) (by norm_num) (by decide +kernel)
      (by decide +kernel)
  · exact OMAFermatH2R1H1.key 125 850705917302346158658436518579420528641 (by norm_num) (by norm_num) (by decide +kernel)
      (by decide +kernel)
  · exact OMAFermatH2R1H1.key 142 363618066009591119386121910507749518730588867002369 (by norm_num) (by norm_num) (by decide +kernel)
      (by decide +kernel)
  · exact OMAFermatH2R1H1.key 144 3032901347000164747248857685080177164813336577 (by norm_num) (by norm_num) (by decide +kernel)
      (by decide +kernel)
  · exact OMAFermatH2R1H1.key 146 13235038053749721162769301995307025251972223086886913 (by norm_num) (by norm_num) (by decide +kernel)
      (by decide +kernel)
  · exact OMAFermatH2R1H1.key 147 2230074519853062314153571827264836150598041600001 (by norm_num) (by norm_num) (by decide +kernel)
      (by decide +kernel)
  · exact OMAFermatH2R1H1.key 150 124204803210043452689216278205372864748572142206977 (by norm_num) (by norm_num) (by decide +kernel)
      (by decide +kernel)
  · exact OMAFermatH2R1H1.key 207 2468256835981809063232453773836025757474103798450369795022913537 (by norm_num) (by norm_num) (by decide +kernel)
      (by decide +kernel)
  · exact OMAFermatH2R1H1.key 226 12940774400232307101440167241769422723345829322819474790929732919623681 (by norm_num) (by norm_num) (by decide +kernel)
      (by decide +kernel)
  · exact OMAFermatH2R1H1.key 228 100075322028463174917803960003016869060541080096470605049856601245089793 (by norm_num) (by norm_num) (by decide +kernel)
      (by decide +kernel)
  · exact OMAFermatH2R1H1.key 250 2916513247664901672231194184906326679054237738765821706743837897199311952805889 (by norm_num) (by norm_num) (by decide +kernel)
      (by decide +kernel)
  · exact OMAFermatH2R1H1.key 255 145666448260543773842852299140929388079413640709375829561637640681954717087039489 (by norm_num) (by norm_num) (by decide +kernel)
      (by decide +kernel)
  · exact OMAFermatH2R1H1.key 267 671586706882722745220204604507349309522863301781696670432755461960519645471331844097 (by norm_num) (by norm_num) (by decide +kernel)
      (by decide +kernel)
  · exact OMAFermatH2R1H1.key 268 2549752921046269405581793752705868564968158976255933121643003787782311874331836153857 (by norm_num) (by norm_num) (by decide +kernel)
      (by decide +kernel)
  · exact OMAFermatH2R1H1.key 284 13925050619474025980350702948110983522812772222325736088332991353008465916350934514925569 (by norm_num) (by norm_num) (by decide +kernel)
      (by decide +kernel)
  · exact OMAFermatH2R1H1.key 298 2012591544618472253233224340148465623118850772941945015628506763962128724166176665709196607489 (by norm_num) (by norm_num) (by decide +kernel)
      (by decide +kernel)
