import OMAStatements.S_oeis_a092028
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic

namespace OMA.P_oeis_a092028

open OMA.S_oeis_a092028

private lemma dvd_pow_sub_one {n q : ℕ} (hn : 1 ≤ n) (hdvd : q ∣ n - 1) :
    q ∣ n ^ q - 1 := by
  have h1 : 1 ≤ n ^ q := Nat.one_le_pow q n (by omega)
  rw [← ZMod.natCast_eq_zero_iff] at hdvd ⊢
  rw [Nat.cast_sub hn, Nat.cast_one] at hdvd
  rw [Nat.cast_sub h1, Nat.cast_pow, Nat.cast_one]
  have hnq : (n : ZMod q) = 1 := sub_eq_zero.mp hdvd
  rw [hnq, one_pow, sub_self]

private lemma coprime_minFac_sub_one {m : ℕ} (hm : 1 < m) :
    Nat.Coprime m (m.minFac - 1) := by
  refine Nat.coprime_iff_gcd_eq_one.mpr ?_
  by_contra hne
  set r := (Nat.gcd m (m.minFac - 1)).minFac
  have hr_prime : r.Prime := Nat.minFac_prime hne
  have hr_dvd_g : r ∣ Nat.gcd m (m.minFac - 1) := Nat.minFac_dvd _
  have hr_dvd_m : r ∣ m := hr_dvd_g.trans (Nat.gcd_dvd_left _ _)
  have hr_dvd_sub : r ∣ m.minFac - 1 := hr_dvd_g.trans (Nat.gcd_dvd_right _ _)
  have hp_prime : m.minFac.Prime := Nat.minFac_prime (by omega)
  have hsub_pos : 0 < m.minFac - 1 := by have := hp_prime.two_le; omega
  have hr_le : r ≤ m.minFac - 1 := Nat.le_of_dvd hsub_pos hr_dvd_sub
  have hmin_le : m.minFac ≤ r := Nat.minFac_le_of_dvd hr_prime.two_le hr_dvd_m
  omega

private lemma minFac_dvd_sub_one {n m : ℕ} (hn : 1 ≤ n) (hm : 1 < m) (hdvd : m ∣ n ^ m - 1) :
    m.minFac ∣ n - 1 := by
  set p := m.minFac
  have hp_prime : p.Prime := Nat.minFac_prime (by omega)
  have hp_dvd_m : p ∣ m := Nat.minFac_dvd m
  have hp_dvd : p ∣ n ^ m - 1 := hp_dvd_m.trans hdvd
  have : Fact p.Prime := ⟨hp_prime⟩
  have hpow1 : 1 ≤ n ^ m := Nat.one_le_pow m n (by omega)
  have hpow_eq : (n : ZMod p) ^ m = 1 := by
    rw [← ZMod.natCast_eq_zero_iff] at hp_dvd
    rw [Nat.cast_sub hpow1, Nat.cast_pow, Nat.cast_one] at hp_dvd
    exact sub_eq_zero.mp hp_dvd
  have hn_ne : (n : ZMod p) ≠ 0 := by
    intro hz
    rw [hz, zero_pow (by omega)] at hpow_eq
    exact zero_ne_one hpow_eq
  have hflt : (n : ZMod p) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one hn_ne
  have hcop : Nat.Coprime m (p - 1) := coprime_minFac_sub_one hm
  have hord_dvd1 : orderOf (n : ZMod p) ∣ m := orderOf_dvd_of_pow_eq_one hpow_eq
  have hord_dvd2 : orderOf (n : ZMod p) ∣ p - 1 := orderOf_dvd_of_pow_eq_one hflt
  have hord_dvd : orderOf (n : ZMod p) ∣ 1 := by
    rw [← hcop.gcd_eq_one]; exact Nat.dvd_gcd hord_dvd1 hord_dvd2
  have hord1 : orderOf (n : ZMod p) = 1 := Nat.dvd_one.mp hord_dvd
  have hn1 : (n : ZMod p) = 1 := orderOf_eq_one_iff.mp hord1
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub hn, Nat.cast_one, hn1, sub_self]

private theorem prove_main : type_of% @OMA.S_oeis_a092028.main := by
  intro n hn
  set S : Set ℕ := {m : ℕ | 1 < m ∧ m ∣ n ^ m - 1}
  set q := (n - 1).minFac
  have hq_prime : q.Prime := Nat.minFac_prime (by omega)
  have hq_dvd : q ∣ n - 1 := Nat.minFac_dvd (n - 1)
  have hq_mem : q ∈ S := ⟨hq_prime.one_lt, dvd_pow_sub_one (by omega) hq_dvd⟩
  have hne : S.Nonempty := ⟨q, hq_mem⟩
  have hm_mem : a n ∈ S := Nat.sInf_mem hne
  have hm_le_q : a n ≤ q := Nat.sInf_le hq_mem
  have hp_dvd : (a n).minFac ∣ n - 1 := minFac_dvd_sub_one (by omega) hm_mem.1 hm_mem.2
  have hp_prime : (a n).minFac.Prime := Nat.minFac_prime (by have := hm_mem.1; omega)
  have hq_le_p : q ≤ (a n).minFac := Nat.minFac_le_of_dvd hp_prime.two_le hp_dvd
  have hp_le_m : (a n).minFac ≤ a n := Nat.minFac_le (by have := hm_mem.1; omega)
  have heq : a n = q := le_antisymm hm_le_q (hq_le_p.trans hp_le_m)
  exact ⟨heq ▸ hq_prime, heq⟩

end OMA.P_oeis_a092028

theorem OMA.solution : type_of% @OMA.S_oeis_a092028.main :=
  OMA.P_oeis_a092028.prove_main
