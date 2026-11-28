import OMAStatements.S_oeis_a092028
import Mathlib

open OMA.S_oeis_a092028

theorem OMA.solution : type_of% @OMA.S_oeis_a092028.main := by
  intro n hn
  have hn1 : n - 1 ≠ 1 := by omega
  have hpp : (n - 1).minFac.Prime := Nat.minFac_prime hn1
  have mem : (n - 1).minFac ∈ {m : ℕ | 1 < m ∧ m ∣ n ^ m - 1} := by
    refine ⟨hpp.one_lt, ?_⟩
    have h1 : n - 1 ∣ n ^ (n - 1).minFac - 1 := by
      exact Nat.sub_one_dvd_pow_sub_one n _
    exact (Nat.minFac_dvd (n - 1)).trans h1
  have low : ∀ m ∈ {m : ℕ | 1 < m ∧ m ∣ n ^ m - 1}, (n - 1).minFac ≤ m := by
    rintro m ⟨hm1, hmd⟩
    have hm0 : m ≠ 1 := by omega
    set q := m.minFac with hqdef
    have hq : q.Prime := Nat.minFac_prime hm0
    have := Fact.mk hq
    have hqd : q ∣ n ^ m - 1 := (Nat.minFac_dvd m).trans hmd
    have hpow : (n : ZMod q) ^ m = 1 := by
      have h0 := (ZMod.natCast_eq_zero_iff (n ^ m - 1) q).mpr hqd
      rw [Nat.cast_sub (Nat.one_le_pow _ _ (by omega))] at h0
      push_cast at h0
      exact sub_eq_zero.mp h0
    have hne : (n : ZMod q) ≠ 0 := by
      intro h
      rw [h, zero_pow (by omega)] at hpow
      exact zero_ne_one hpow
    have hferm : (n : ZMod q) ^ (q - 1) = 1 := ZMod.pow_card_sub_one_eq_one hne
    have hcop : Nat.gcd m (q - 1) = 1 := by
      by_contra hc
      have hr := Nat.minFac_prime hc
      have hr1 : (Nat.gcd m (q - 1)).minFac ∣ m := (Nat.minFac_dvd _).trans (Nat.gcd_dvd_left _ _)
      have hr2 : (Nat.gcd m (q - 1)).minFac ∣ q - 1 := (Nat.minFac_dvd _).trans (Nat.gcd_dvd_right _ _)
      have e1 : q ≤ (Nat.gcd m (q - 1)).minFac := Nat.minFac_le_of_dvd hr.two_le hr1
      have e2 : (Nat.gcd m (q - 1)).minFac ≤ q - 1 := Nat.le_of_dvd (by have := hq.two_le; omega) hr2
      have := hq.two_le
      omega
    have hord : orderOf (n : ZMod q) ∣ Nat.gcd m (q - 1) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hpow) (orderOf_dvd_of_pow_eq_one hferm)
    rw [hcop, Nat.dvd_one, orderOf_eq_one_iff] at hord
    have hqn : q ∣ n - 1 := by
      apply (ZMod.natCast_eq_zero_iff (n - 1) q).mp
      rw [Nat.cast_sub (by omega)]
      push_cast
      rw [hord, sub_self]
    have e3 : (n - 1).minFac ≤ q := Nat.minFac_le_of_dvd hq.two_le hqn
    have e4 : q ≤ m := Nat.minFac_le (by omega)
    omega
  have heq : a n = (n - 1).minFac := by
    apply le_antisymm (Nat.sInf_le mem)
    exact le_csInf ⟨_, mem⟩ low
  rw [heq]
  exact ⟨hpp, rfl⟩
