import OMAStatements.S_oeis_a088883
import Mathlib

namespace A088883aux

open OMA.S_oeis_a088883 in
lemma rev_mod (p : ℕ) : rev p ≡ p [MOD 3] := by
  unfold rev
  have h1 : Nat.ofDigits 10 (Nat.digits 10 p).reverse
      ≡ Nat.ofDigits 1 (Nat.digits 10 p).reverse [MOD 3] :=
    Nat.ofDigits_modEq' 10 1 3 (by decide) _
  rw [Nat.ofDigits_one, List.sum_reverse] at h1
  exact h1.trans (Nat.modEq_three_digits_sum p).symm

open OMA.S_oeis_a088883 in
lemma big_mod (p : ℕ) :
    (p * 10 ^ (Nat.digits 10 p).length + rev p + 2) % 3 = (2 * p + 2) % 3 := by
  have hpow : 10 ^ (Nat.digits 10 p).length ≡ 1 [MOD 3] := by
    have h := Nat.ModEq.pow (Nat.digits 10 p).length (show 10 ≡ 1 [MOD 3] by decide)
    rwa [one_pow] at h
  have h := ((Nat.ModEq.mul_left p hpow).add (rev_mod p)).add_right 2
  unfold Nat.ModEq at h
  rw [h]
  congr 1
  ring

end A088883aux

theorem OMA.solution : type_of% @OMA.S_oeis_a088883.main := by
  intro p hp hN
  by_cases h2 : p = 2
  · subst h2
    exfalso
    rw [show Nat.digits 10 2 = [2] from Nat.digits_of_lt 10 2 (by norm_num) (by norm_num)] at hN
    unfold OMA.S_oeis_a088883.rev at hN
    rw [show Nat.digits 10 2 = [2] from Nat.digits_of_lt 10 2 (by norm_num) (by norm_num)] at hN
    norm_num [Nat.ofDigits] at hN
  by_cases h3 : p = 3
  · subst h3
    exfalso
    rw [show Nat.digits 10 3 = [3] from Nat.digits_of_lt 10 3 (by norm_num) (by norm_num)] at hN
    unfold OMA.S_oeis_a088883.rev at hN
    rw [show Nat.digits 10 3 = [3] from Nat.digits_of_lt 10 3 (by norm_num) (by norm_num)] at hN
    norm_num [Nat.ofDigits] at hN
  have hodd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · exact absurd h h2
    · exact h
  have hp3 : p % 3 ≠ 0 := by
    intro h0
    have hdvd : 3 ∣ p := Nat.dvd_of_mod_eq_zero h0
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp hdvd
    omega
  have hmod := A088883aux.big_mod p
  by_contra hne
  have h5 : p % 3 = 2 := by omega
  have h0 : (p * 10 ^ (Nat.digits 10 p).length + OMA.S_oeis_a088883.rev p + 2) % 3 = 0 := by
    rw [hmod]
    omega
  have hdvd : 3 ∣ p * 10 ^ (Nat.digits 10 p).length + OMA.S_oeis_a088883.rev p + 2 :=
    Nat.dvd_of_mod_eq_zero h0
  have heq := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hN).mp hdvd
  have hpos : 1 ≤ 10 ^ (Nat.digits 10 p).length := Nat.one_le_pow _ _ (by norm_num)
  have hge : p ≤ p * 10 ^ (Nat.digits 10 p).length := Nat.le_mul_of_pos_right p hpos
  have hp2 := hp.two_le
  omega
