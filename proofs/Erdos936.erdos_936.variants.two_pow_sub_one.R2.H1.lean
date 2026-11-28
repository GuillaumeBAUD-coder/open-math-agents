import OMAReductions.R_Erdos936_erdos_936_variants_two_pow_sub_one_R2
import Mathlib

-- Problem: Erdos936.erdos_936.variants.two_pow_sub_one.R2.H1
-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Proof sketch: let d = gcd(n, p - 1). Since gcd(2^n - 1, 2^(p-1) - 1) = 2^d - 1 and
-- p divides both (Fermat), p divides 2^d - 1. Lifting the exponent (padicValNat.pow_sub_pow) for
-- (2^d)^j - 1 gives v_p(2^(dj) - 1) = v_p(2^d - 1) + v_p(j). Apply it with n = d m and
-- p - 1 = d k; as 0 < d, k <= p - 1 < p, v_p(d) = v_p(k) = 0, so v_p(n) = v_p(m) and the formula follows.

namespace OMA.Sol_Erdos936_R2_H1
open OMA.R_Erdos936_erdos_936_variants_two_pow_sub_one_R2

theorem val_zero {p j : ℕ} (hp : p.Prime) (hj : j ≠ 0) (hjp : j < p) : padicValNat p j = 0 :=
  padicValNat.eq_zero_of_not_dvd (fun h => by have := Nat.le_of_dvd (Nat.pos_of_ne_zero hj) h; omega)

theorem h1 : H1 := by
  intro p n hp hp2 hn hdvd
  haveI := Fact.mk hp
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hp1 : p - 1 ≠ 0 := by have := hp.two_le; omega
  obtain ⟨d, hd⟩ : ∃ d, d = Nat.gcd n (p - 1) := ⟨_, rfl⟩
  have hd0 : 0 < d := hd ▸ Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero hn)
  have hdp : p ∣ 2 ^ d - 1 := by
    have h2 := dvd_two_pow_pred_sub_one hp hp2
    have := Nat.dvd_gcd hdvd h2
    rwa [Nat.pow_sub_one_gcd_pow_sub_one, ← hd] at this
  have hx : ¬ p ∣ 2 ^ d := fun h =>
    hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))
  have hy : 1 < 2 ^ d := Nat.one_lt_two_pow hd0.ne'
  have key : ∀ j, j ≠ 0 →
      padicValNat p (2 ^ (d * j) - 1) = padicValNat p (2 ^ d - 1) + padicValNat p j := by
    intro j hj
    have := padicValNat.pow_sub_pow (p := p) (x := 2 ^ d) (y := 1) hodd hy (by simpa using hdp) hx hj
    rwa [one_pow, ← pow_mul] at this
  obtain ⟨m, hm⟩ : d ∣ n := hd ▸ Nat.gcd_dvd_left n (p - 1)
  obtain ⟨k, hk⟩ : d ∣ p - 1 := hd ▸ Nat.gcd_dvd_right n (p - 1)
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm; exact hn hm
  have hk0 : k ≠ 0 := by rintro rfl; simp at hk; exact hp1 hk
  have hkp : k < p := by
    have : k ≤ p - 1 := hk ▸ Nat.le_mul_of_pos_left k hd0
    omega
  have hdlt : d < p := by
    have : d ≤ p - 1 := hk ▸ Nat.le_mul_of_pos_right d (Nat.pos_of_ne_zero hk0)
    omega
  have e1 : padicValNat p (2 ^ n - 1) = padicValNat p (2 ^ d - 1) + padicValNat p m := by
    rw [hm]; exact key m hm0
  have e2 : padicValNat p (2 ^ (p - 1) - 1) = padicValNat p (2 ^ d - 1) + padicValNat p k := by
    rw [hk]; exact key k hk0
  have e3 : padicValNat p n = padicValNat p d + padicValNat p m := by
    rw [hm]; exact padicValNat.mul hd0.ne' hm0
  rw [e1, e2, e3, val_zero hp hk0 hkp, val_zero hp hd0.ne' hdlt]
  omega

end OMA.Sol_Erdos936_R2_H1

theorem OMA.solution : OMA.R_Erdos936_erdos_936_variants_two_pow_sub_one_R2.H1 :=
  OMA.Sol_Erdos936_R2_H1.h1
