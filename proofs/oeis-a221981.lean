import OMAStatements.S_oeis_a221981
import Mathlib
open OMA.S_oeis_a221981

namespace OMA.P_oeis_a221981

theorem three_ns : ¬ IsSquare (3 : ZMod 5) := by unfold IsSquare; decide

theorem ord_aux {P k c : ℕ} [hPf : Fact P.Prime] (a : ZMod P) (hk : k.Prime) (hP : P - 1 = c * k)
    (hc : c = 4 ∨ c = 8) (hhalf : a ^ (c / 2 * k) = -1) (hsmall : a ^ c ≠ 1) (hP2 : P ≠ 2) :
    orderOf a = c * k := by
  have hPp := hPf.out
  have hP3 : 2 < P := by have := hPp.two_le; omega
  have hne : (-1 : ZMod P) ≠ 1 := by
    haveI : Fact (2 < P) := ⟨hP3⟩
    exact ZMod.neg_one_ne_one
  have ha : a ≠ 0 := by
    rintro rfl
    rw [zero_pow] at hhalf
    · exact zero_ne_one (neg_eq_zero.mp hhalf.symm).symm
    · have := hk.pos; rcases hc with rfl | rfl <;> positivity
  have h1 : a ^ (c * k) = 1 := by rw [← hP]; exact ZMod.pow_card_sub_one_eq_one ha
  have hd : orderOf a ∣ c * k := orderOf_dvd_of_pow_eq_one h1
  have hnd : ¬ orderOf a ∣ c / 2 * k := by
    intro h
    rw [orderOf_dvd_iff_pow_eq_one, hhalf] at h
    exact hne h
  by_cases hkn : k ∣ orderOf a
  · obtain ⟨m, hm⟩ := hkn
    rw [hm] at hd hnd ⊢
    have hmc : m ∣ c := by
      rw [mul_comm c k] at hd
      exact Nat.dvd_of_mul_dvd_mul_left hk.pos hd
    have hmc2 : ¬ m ∣ c / 2 := by
      intro h; apply hnd; rw [mul_comm (c/2) k]; exact Nat.mul_dvd_mul_left k h
    rcases hc with rfl | rfl
    · have := Nat.le_of_dvd (by norm_num) hmc
      interval_cases m <;> simp_all <;> ring
    · have := Nat.le_of_dvd (by norm_num) hmc
      interval_cases m <;> simp_all <;> first | ring | omega
  · exfalso
    have hcop : Nat.Coprime k (orderOf a) := (Nat.Prime.coprime_iff_not_dvd hk).mpr hkn
    have : orderOf a ∣ c := hcop.symm.dvd_of_dvd_mul_right hd
    exact hsmall (orderOf_dvd_iff_pow_eq_one.mp this)

theorem dvd_of_pow {P N : ℕ} (a : ZMod P) (e : ℕ) (hN : ((N : ℕ) : ZMod P) = a ^ e - 1)
    (h : a ^ e = 1) : P ∣ N := by
  rw [← ZMod.natCast_eq_zero_iff, hN, h, sub_self]

theorem partA (q : ℕ) (hq : InSeq q) : orderOf (40 : ZMod q) = q - 1 := by
  obtain ⟨hqp, p, hp, hp5, rfl⟩ := hq
  haveI : Fact (4 * p + 1).Prime := ⟨hqp⟩
  have hp2 : p ≠ 2 := by rintro rfl; norm_num at hqp
  have hodd := hp.eq_two_or_odd.resolve_left hp2
  have hq2 : 4 * p + 1 ≠ 2 := by omega
  -- 2 is a non-square
  have h2ns : ¬ IsSquare (2 : ZMod (4 * p + 1)) := by
    rw [ZMod.exists_sq_eq_two_iff hq2]; omega
  have h5s : IsSquare ((5 : ℕ) : ZMod (4 * p + 1)) := by
    haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    rw [← ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one (by norm_num) hq2]
    have : ((4 * p + 1 : ℕ) : ZMod 5) = 4 := by
      rw [← ZMod.natCast_mod]; rw [show (4 * p + 1) % 5 = 4 by omega]; rfl
    rw [this]; exact ⟨2, rfl⟩
  have hP := hqp.two_le
  have h20 : (2 : ZMod (4 * p + 1)) ≠ 0 := by
    intro h
    have := (ZMod.natCast_eq_zero_iff 2 (4 * p + 1)).mp (by exact_mod_cast h)
    have := Nat.le_of_dvd (by norm_num) this; omega
  have h50 : ((5 : ℕ) : ZMod (4 * p + 1)) ≠ 0 := by
    intro h
    have := (ZMod.natCast_eq_zero_iff 5 (4 * p + 1)).mp h
    have := Nat.le_of_dvd (by norm_num) this; omega
  have e2 : (2 : ZMod (4 * p + 1)) ^ ((4 * p + 1) / 2) = -1 := by
    rcases ZMod.pow_div_two_eq_neg_one_or_one _ h20 with h | h
    · exact absurd ((ZMod.euler_criterion _ h20).mpr h) h2ns
    · exact h
  have e5 : ((5 : ℕ) : ZMod (4 * p + 1)) ^ ((4 * p + 1) / 2) = 1 :=
    (ZMod.euler_criterion _ h50).mp h5s
  have hdiv : (4 * p + 1) / 2 = 2 * p := by omega
  rw [hdiv] at e2 e5
  push_cast at e5
  have hhalf : (40 : ZMod (4 * p + 1)) ^ (4 / 2 * p) = -1 := by
    rw [show (40 : ZMod (4 * p + 1)) = 2 ^ 3 * 5 by norm_num, show 4 / 2 * p = 2 * p by omega,
      mul_pow, ← pow_mul, mul_comm 3, pow_mul, e2, e5]; norm_num
  rw [ord_aux (k := p) (c := 4) _ hp (by omega) (Or.inl rfl) hhalf _ hq2]
  · omega
  · intro h
    have hd := dvd_of_pow (N := 2559999) (40 : ZMod (4 * p + 1)) 4 (by push_cast; norm_num) h
    rw [show (2559999 : ℕ) = 3 * 13 * 41 * 1601 by norm_num] at hd
    rcases (Nat.Prime.dvd_mul hqp).mp hd with hd | hd
    · rcases (Nat.Prime.dvd_mul hqp).mp hd with hd | hd
      · rcases (Nat.Prime.dvd_mul hqp).mp hd with hd | hd
        · have := Nat.le_of_dvd (by norm_num) hd; omega
        · have := (Nat.prime_dvd_prime_iff_eq hqp (by norm_num)).mp hd; omega
      · have := (Nat.prime_dvd_prime_iff_eq hqp (by norm_num)).mp hd; omega
    · have := (Nat.prime_dvd_prime_iff_eq hqp (by norm_num)).mp hd; omega

theorem partB (q : ℕ) (hq : InSeq q) (hr : (8 * q + 1).Prime) :
    orderOf (10 : ZMod (8 * q + 1)) = 8 * q + 1 - 1 := by
  obtain ⟨hqp, p, hp, hp5, rfl⟩ := hq
  haveI : Fact (8 * (4 * p + 1) + 1).Prime := ⟨hr⟩
  have hp2 : p ≠ 2 := by rintro rfl; norm_num at hqp
  have hq2 : 8 * (4 * p + 1) + 1 ≠ 2 := by omega
  have h2s : IsSquare (2 : ZMod (8 * (4 * p + 1) + 1)) := by
    rw [ZMod.exists_sq_eq_two_iff hq2]; omega
  have h5ns : ¬ IsSquare ((5 : ℕ) : ZMod (8 * (4 * p + 1) + 1)) := by
    haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    rw [← ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one (by norm_num) hq2]
    have : ((8 * (4 * p + 1) + 1 : ℕ) : ZMod 5) = 3 := by
      rw [← ZMod.natCast_mod]; rw [show (8 * (4 * p + 1) + 1) % 5 = 3 by omega]; rfl
    rw [this]; exact three_ns
  have hP := hr.two_le
  have h20 : (2 : ZMod (8 * (4 * p + 1) + 1)) ≠ 0 := by
    intro h
    have := (ZMod.natCast_eq_zero_iff 2 (8 * (4 * p + 1) + 1)).mp (by exact_mod_cast h)
    have := Nat.le_of_dvd (by norm_num) this; omega
  have h50 : ((5 : ℕ) : ZMod (8 * (4 * p + 1) + 1)) ≠ 0 := by
    intro h
    have := (ZMod.natCast_eq_zero_iff 5 (8 * (4 * p + 1) + 1)).mp h
    have := Nat.le_of_dvd (by norm_num) this; omega
  have e5 : ((5 : ℕ) : ZMod (8 * (4 * p + 1) + 1)) ^ ((8 * (4 * p + 1) + 1) / 2) = -1 := by
    rcases ZMod.pow_div_two_eq_neg_one_or_one _ h50 with h | h
    · exact absurd ((ZMod.euler_criterion _ h50).mpr h) h5ns
    · exact h
  have e2 : (2 : ZMod (8 * (4 * p + 1) + 1)) ^ ((8 * (4 * p + 1) + 1) / 2) = 1 :=
    (ZMod.euler_criterion _ h20).mp h2s
  have hdiv : (8 * (4 * p + 1) + 1) / 2 = 8 / 2 * (4 * p + 1) := by omega
  rw [hdiv] at e2 e5
  push_cast at e5
  have hhalf : (10 : ZMod (8 * (4 * p + 1) + 1)) ^ (8 / 2 * (4 * p + 1)) = -1 := by
    rw [show (10 : ZMod (8 * (4 * p + 1) + 1)) = 2 * 5 by norm_num, mul_pow, e2, e5]; norm_num
  rw [ord_aux (k := 4 * p + 1) (c := 8) _ hqp (by omega) (Or.inr rfl) hhalf _ hq2]
  · omega
  · intro h
    have hd := dvd_of_pow (N := 99999999) (10 : ZMod (8 * (4 * p + 1) + 1)) 8
      (by push_cast; norm_num) h
    rw [show (99999999 : ℕ) = 9 * 11 * 73 * 101 * 137 by norm_num] at hd
    rcases (Nat.Prime.dvd_mul hr).mp hd with hd | hd
    · rcases (Nat.Prime.dvd_mul hr).mp hd with hd | hd
      · rcases (Nat.Prime.dvd_mul hr).mp hd with hd | hd
        · rcases (Nat.Prime.dvd_mul hr).mp hd with hd | hd
          · have := Nat.le_of_dvd (by norm_num) hd; omega
          · have := (Nat.prime_dvd_prime_iff_eq hr (by norm_num)).mp hd; omega
        · have := (Nat.prime_dvd_prime_iff_eq hr (by norm_num)).mp hd
          have hp2' : p = 2 := by omega
          exact hp2 hp2'
      · have := (Nat.prime_dvd_prime_iff_eq hr (by norm_num)).mp hd; omega
    · have := (Nat.prime_dvd_prime_iff_eq hr (by norm_num)).mp hd; omega

end OMA.P_oeis_a221981

theorem OMA.solution : type_of% @OMA.S_oeis_a221981.main := by
  exact ⟨OMA.P_oeis_a221981.partA, OMA.P_oeis_a221981.partB⟩
