import OMAStatements.S_oeis_a078251
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic

namespace OMA.P_oeis_a078251

open OMA.S_oeis_a078251

private lemma geom_sum_mul (B k : ℕ) :
    (B - 1) * (∑ j ∈ Finset.range k, B ^ j) = B ^ k - 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    cases B with
    | zero =>
      cases k <;> simp
    | succ B =>
      have h1 : 1 ≤ (B + 1) ^ k := Nat.one_le_pow k (B + 1) (by omega)
      rw [Nat.add_sub_cancel]
      zify [h1, show 1 ≤ (B + 1) ^ (k + 1) from Nat.one_le_pow (k + 1) (B + 1) (by omega)]
      ring

private lemma exists_dvd_geom_sum {p B : ℕ} (hp : p.Prime) (hB : 1 ≤ B) (hcop : Nat.Coprime B p) :
    ∃ k : ℕ, 0 < k ∧ p ∣ ∑ j ∈ Finset.range k, B ^ j := by
  have : Fact p.Prime := ⟨hp⟩
  by_cases hd : p ∣ B - 1
  · refine ⟨p, hp.pos, ?_⟩
    rw [← ZMod.natCast_eq_zero_iff] at hd ⊢
    rw [Nat.cast_sub hB, Nat.cast_one] at hd
    have hB1 : (B : ZMod p) = 1 := sub_eq_zero.mp hd
    push_cast
    simp [hB1]
  · refine ⟨p - 1, by have := hp.two_le; omega, ?_⟩
    have hcop' : Nat.Coprime p (B - 1) := hp.coprime_iff_not_dvd.mpr hd
    apply hcop'.dvd_of_dvd_mul_left
    rw [geom_sum_mul]
    have hB_ne : (B : ZMod p) ≠ 0 := by
      intro hz
      have hpd : p ∣ B := (ZMod.natCast_eq_zero_iff B p).mp hz
      have h1 : p ∣ Nat.gcd B p := Nat.dvd_gcd hpd (dvd_refl p)
      rw [hcop.gcd_eq_one] at h1
      have := Nat.le_of_dvd (by norm_num) h1
      have := hp.two_le
      omega
    have hflt : (B : ZMod p) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one hB_ne
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub (Nat.one_le_pow (p - 1) B hB), Nat.cast_pow,
      Nat.cast_one, hflt, sub_self]

private lemma nth_prime_ge_seven {n : ℕ} (hn : 3 < n) : 7 ≤ Nat.nth Nat.Prime (n - 1) := by
  have h3 : Nat.nth Nat.Prime 3 = 7 := by
    have h2 : Nat.nth Nat.Prime 2 = 5 := Nat.nth_prime_two_eq_five
    have hlt : 5 < Nat.nth Nat.Prime 3 := by
      rw [← h2]; exact Nat.nth_strictMono Nat.infinite_setOfPred_prime (by norm_num)
    have hle : Nat.nth Nat.Prime 3 ≤ 7 := by
      have hcount : Nat.count Nat.Prime 7 = 3 := by decide
      rw [← hcount]
      exact (Nat.nth_count (by decide : Nat.Prime 7)).le
    have hp3 : (Nat.nth Nat.Prime 3).Prime := Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime 3
    have h6 : Nat.nth Nat.Prime 3 ≠ 6 := by intro h; rw [h] at hp3; exact absurd hp3 (by decide)
    omega
  have hmono : Nat.nth Nat.Prime 3 ≤ Nat.nth Nat.Prime (n - 1) :=
    (Nat.nth_strictMono Nat.infinite_setOfPred_prime).monotone (by omega)
  omega

private theorem prove_main : type_of% @OMA.S_oeis_a078251.main := by
  intro n hn
  set p := Nat.nth Nat.Prime (n - 1)
  have hp : p.Prime := Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime (n - 1)
  have hp7 : 7 ≤ p := nth_prime_ge_seven hn
  have hcop10 : Nat.Coprime 10 p := by
    refine (hp.coprime_iff_not_dvd.mpr ?_).symm
    intro h
    have hmul : p ∣ 2 * 5 := by simpa using h
    rcases hp.dvd_mul.mp hmul with h2 | h5
    · have := Nat.le_of_dvd (by norm_num) h2; omega
    · have := Nat.le_of_dvd (by norm_num) h5; omega
  set d := (Nat.digits 10 n).length
  have hcopB : Nat.Coprime (10 ^ d) p := hcop10.pow_left d
  obtain ⟨k, hk_pos, hk_dvd⟩ := exists_dvd_geom_sum hp (Nat.one_le_pow d 10 (by norm_num)) hcopB
  have hex : ∃ k : ℕ, 0 < k ∧ p ∣ repConcat n k :=
    ⟨k, hk_pos, dvd_mul_of_dvd_right hk_dvd n⟩
  unfold a
  rw [dif_pos hex]
  set k0 := sInf {k : ℕ | 0 < k ∧ p ∣ repConcat n k}
  have hk0_mem : k0 ∈ {k : ℕ | 0 < k ∧ p ∣ repConcat n k} := Nat.sInf_mem hex
  have hk0_pos : 0 < k0 := hk0_mem.1
  unfold repConcat
  have hsum_pos : 0 < ∑ j ∈ Finset.range k0, (10 ^ d) ^ j := by
    have h0mem : 0 ∈ Finset.range k0 := Finset.mem_range.mpr hk0_pos
    have hle : (10 ^ d) ^ 0 ≤ ∑ j ∈ Finset.range k0, (10 ^ d) ^ j :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) h0mem
    simp at hle
    omega
  exact Nat.mul_ne_zero (by omega) (Nat.ne_of_gt hsum_pos)

end OMA.P_oeis_a078251

theorem OMA.solution : type_of% @OMA.S_oeis_a078251.main :=
  OMA.P_oeis_a078251.prove_main
