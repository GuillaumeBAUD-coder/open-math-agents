import OMAStatements.S_mo_258852
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Tactic

/-! The exponents 214 and 642 have a common largest prime factor. The
factor data used to locate the witness are from the Cunningham tables,
Table 2LM (https://homes.cerias.purdue.edu/~ssw/cun/pmain1126.txt). The arithmetic and primality certificate below are checked in Lean. -/

namespace PowersCounterexample

private theorem prime_2 : Nat.Prime 2 := by norm_num

private theorem prime_19 : Nat.Prime 19 := by norm_num

private theorem prime_107 : Nat.Prime 107 := by norm_num

private theorem prime_353 : Nat.Prime 353 := by norm_num

private theorem prime_91813 : Nat.Prime 91813 := by norm_num

private theorem prime_3 : Nat.Prime 3 := by norm_num

private theorem prime_547 : Nat.Prime 547 := by norm_num

private theorem prime_1103 : Nat.Prime 1103 := by norm_num

private theorem prime_7 : Nat.Prime 7 := by norm_num

private theorem prime_23 : Nat.Prime 23 := by norm_num

private theorem prime_137 : Nat.Prime 137 := by norm_num

private theorem prime_1973 : Nat.Prime 1973 := by norm_num

private theorem prime_1653701519 : Nat.Prime 1653701519 := by
  apply lucas_primality 1653701519 7
  · change (7 : ZMod 1653701519) ^ 1653701518 = 1
    reduce_mod_char
  · intro q hq hd
    rw [show (1653701519 : ℕ) - 1 = 2 ^ 1 * 7 ^ 1 * 19 ^ 1 * 23 ^ 1 * 137 ^ 1 * 1973 ^ 1 by decide] at hd
    simp only [hq.dvd_mul, or_assoc] at hd
    rcases hd with h | h | h | h | h | h
    · have he := Nat.prime_eq_prime_of_dvd_pow hq prime_2 h
      subst q
      change (7 : ZMod 1653701519) ^ 826850759 ≠ 1
      reduce_mod_char
      decide
    · have he := Nat.prime_eq_prime_of_dvd_pow hq prime_7 h
      subst q
      change (7 : ZMod 1653701519) ^ 236243074 ≠ 1
      reduce_mod_char
      decide
    · have he := Nat.prime_eq_prime_of_dvd_pow hq prime_19 h
      subst q
      change (7 : ZMod 1653701519) ^ 87036922 ≠ 1
      reduce_mod_char
      decide
    · have he := Nat.prime_eq_prime_of_dvd_pow hq prime_23 h
      subst q
      change (7 : ZMod 1653701519) ^ 71900066 ≠ 1
      reduce_mod_char
      decide
    · have he := Nat.prime_eq_prime_of_dvd_pow hq prime_137 h
      subst q
      change (7 : ZMod 1653701519) ^ 12070814 ≠ 1
      reduce_mod_char
      decide
    · have he := Nat.prime_eq_prime_of_dvd_pow hq prime_1973 h
      subst q
      change (7 : ZMod 1653701519) ^ 838166 ≠ 1
      reduce_mod_char
      decide

private theorem prime_143675413657196977 : Nat.Prime 143675413657196977 := by
  apply lucas_primality 143675413657196977 5
  · change (5 : ZMod 143675413657196977) ^ 143675413657196976 = 1
    reduce_mod_char
  · intro q hq hd
    rw [show (143675413657196977 : ℕ) - 1 = 2 ^ 4 * 3 ^ 2 * 547 ^ 1 * 1103 ^ 1 * 1653701519 ^ 1 by decide] at hd
    simp only [hq.dvd_mul, or_assoc] at hd
    rcases hd with h | h | h | h | h
    · have he := Nat.prime_eq_prime_of_dvd_pow hq prime_2 h
      subst q
      change (5 : ZMod 143675413657196977) ^ 71837706828598488 ≠ 1
      reduce_mod_char
      decide
    · have he := Nat.prime_eq_prime_of_dvd_pow hq prime_3 h
      subst q
      change (5 : ZMod 143675413657196977) ^ 47891804552398992 ≠ 1
      reduce_mod_char
      decide
    · have he := Nat.prime_eq_prime_of_dvd_pow hq prime_547 h
      subst q
      change (5 : ZMod 143675413657196977) ^ 262660719665808 ≠ 1
      reduce_mod_char
      decide
    · have he := Nat.prime_eq_prime_of_dvd_pow hq prime_1103 h
      subst q
      change (5 : ZMod 143675413657196977) ^ 130258761248592 ≠ 1
      reduce_mod_char
      decide
    · have he := Nat.prime_eq_prime_of_dvd_pow hq prime_1653701519 h
      subst q
      change (5 : ZMod 143675413657196977) ^ 86881104 ≠ 1
      reduce_mod_char
      decide

private theorem prime_37866809061660057264219253397 : Nat.Prime 37866809061660057264219253397 := by
  apply lucas_primality 37866809061660057264219253397 3
  · change (3 : ZMod 37866809061660057264219253397) ^ 37866809061660057264219253396 = 1
    reduce_mod_char
  · intro q hq hd
    rw [show (37866809061660057264219253397 : ℕ) - 1 = 2 ^ 2 * 19 ^ 1 * 107 ^ 1 * 353 ^ 1 * 91813 ^ 1 * 143675413657196977 ^ 1 by decide] at hd
    simp only [hq.dvd_mul, or_assoc] at hd
    rcases hd with h | h | h | h | h | h
    · have he := Nat.prime_eq_prime_of_dvd_pow hq prime_2 h
      subst q
      change (3 : ZMod 37866809061660057264219253397) ^ 18933404530830028632109626698 ≠ 1
      reduce_mod_char
      decide
    · have he := Nat.prime_eq_prime_of_dvd_pow hq prime_19 h
      subst q
      change (3 : ZMod 37866809061660057264219253397) ^ 1992989950613687224432592284 ≠ 1
      reduce_mod_char
      decide
    · have he := Nat.prime_eq_prime_of_dvd_pow hq prime_107 h
      subst q
      change (3 : ZMod 37866809061660057264219253397) ^ 353895411791215488450647228 ≠ 1
      reduce_mod_char
      decide
    · have he := Nat.prime_eq_prime_of_dvd_pow hq prime_353 h
      subst q
      change (3 : ZMod 37866809061660057264219253397) ^ 107271413772408094232915732 ≠ 1
      reduce_mod_char
      decide
    · have he := Nat.prime_eq_prime_of_dvd_pow hq prime_91813 h
      subst q
      change (3 : ZMod 37866809061660057264219253397) ^ 412434067742695013388292 ≠ 1
      reduce_mod_char
      decide
    · have he := Nat.prime_eq_prime_of_dvd_pow hq prime_143675413657196977 h
      subst q
      change (3 : ZMod 37866809061660057264219253397) ^ 263558030548 ≠ 1
      reduce_mod_char
      decide

open OMA.S_mo_258852

private theorem largeTerm : term 160 = 18249762470488780874564686422801165299572914028994239722316770071597100668834709546023651245269485599114569238294377629242754818885501751993010645278888856753007978697441059800331496768986415105 := by
  simp only [term, show (4 * 160 + 2 : ℕ) = 214 * 3 by decide, pow_mul]
  norm_num

set_option maxRecDepth 4000 in
private theorem greatest : IsGreatest {q : ℕ | q.Prime ∧ q ∣ term 160} 37866809061660057264219253397 := by
  refine ⟨⟨prime_37866809061660057264219253397, by rw [largeTerm]; decide⟩, ?_⟩
  intro q hq
  obtain ⟨prime, divides⟩ := hq
  rw [show term 160 = 2761218489699424389505 *
        92878358660705627641 *
        192343993140277293096491917 *
        87251820842149 *
        157500130135806013 *
        3396103766435902981 *
        166125681371619629161 *
        1260176658389613436649482957 *
        37866809061660057264219253397 by rw [largeTerm]] at divides
  simp only [prime.dvd_mul, or_assoc] at divides
  rcases divides with h | h | h | h | h | h | h | h | h
  all_goals exact (Nat.le_of_dvd (by decide) h).trans (by decide)

end PowersCounterexample

set_option maxRecDepth 4000 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_258852.main) := by
  intro claim
  have equal := claim 160 53 (by decide) (by decide)
    (by rw [PowersCounterexample.largeTerm]; decide) _
    PowersCounterexample.greatest (by norm_num [OMA.S_mo_258852.term, Nat.dvd_iff_mod_eq_zero])
  exact (by rw [PowersCounterexample.largeTerm]; decide : OMA.S_mo_258852.term 53 ≠ OMA.S_mo_258852.term 160) equal
