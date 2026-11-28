import OMAStatements.S_oeis_a400825
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic

namespace OMA.P_oeis_a400825

open OMA.S_oeis_a400825

private lemma prove_a400825 (k : ℕ) (hk : 1 ≤ k)
    (hcong : (2 : ZMod (N k)) ^ ((N k - 1) / 4) = -1) : (N k).Prime := by
  have h2k : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk
  have hN_ge : 33 ≤ N k := by
    dsimp [N]
    have h4 : 32 ≤ 2 ^ (k + 4) := by
      calc 32 = 2 ^ 5 := by norm_num
        _ ≤ 2 ^ (k + 4) := Nat.pow_le_pow_right (by decide) (by omega)
    have h1 : 1 ≤ 2 ^ k - 1 := by omega
    nlinarith
  have hN_ne1 : N k ≠ 1 := by omega
  have hN_odd : N k % 2 = 1 := by
    dsimp [N]
    have h2dvd : 2 ∣ 2 ^ (k + 4) := dvd_pow_self 2 (by omega)
    obtain ⟨t, ht⟩ := h2dvd
    rw [ht, show (2 ^ k - 1) * (2 * t) = 2 * ((2 ^ k - 1) * t) by ring]
    omega
  set m := (N k - 1) / 4
  have hm_eq : m = (2 ^ k - 1) * 2 ^ (k + 2) := by
    dsimp [m, N]
    rw [show k + 4 = (k + 2) + 2 by omega, pow_add]
    have : (2 ^ k - 1) * (2 ^ (k + 2) * 2 ^ 2) = ((2 ^ k - 1) * 2 ^ (k + 2)) * 4 := by ring
    rw [this, Nat.mul_div_cancel _ (by decide)]
  -- Let `q = (N k).minFac`, a prime divisor of `N k`.
  set q := (N k).minFac
  have hq_prime : q.Prime := Nat.minFac_prime hN_ne1
  have hq_dvd : q ∣ N k := Nat.minFac_dvd (N k)
  have hq_ne2 : q ≠ 2 := by
    intro h2
    rw [h2] at hq_dvd
    omega
  have : Fact q.Prime := ⟨hq_prime⟩
  -- Project `2 ^ m = -1` from `ZMod (N k)` to `ZMod q`.
  have h2m : (2 : ZMod q) ^ m = -1 := by
    have h := congr_arg (ZMod.castHom hq_dvd (ZMod q)) hcong
    simpa [map_pow, map_neg, map_one, map_ofNat] using h
  have h2_2m : (2 : ZMod q) ^ (2 * m) = 1 := by
    rw [mul_comm, pow_mul, h2m]
    norm_num
  have hne_neg1 : (-1 : ZMod q) ≠ 1 := by
    intro heq
    have h2zero : ((2 : ℕ) : ZMod q) = 0 := by
      calc ((2 : ℕ) : ZMod q) = 1 - (-1) := by norm_num
        _ = 1 - 1 := by rw [heq]
        _ = 0 := sub_self 1
    rw [ZMod.natCast_eq_zero_iff] at h2zero
    have := Nat.le_of_dvd (by decide) h2zero
    have := hq_prime.two_le
    omega
  have h2m_ne1 : (2 : ZMod q) ^ m ≠ 1 := by rw [h2m]; exact hne_neg1
  -- Show `2 ^ (k + 3) ∣ orderOf (2 : ZMod q)`.
  set d := orderOf (2 : ZMod q)
  have hd_dvd_2m : d ∣ 2 * m := orderOf_dvd_of_pow_eq_one h2_2m
  have hd_ndvd_m : ¬ d ∣ m := fun hd => h2m_ne1 (orderOf_dvd_iff_pow_eq_one.mp hd)
  have h2k3_dvd_d : 2 ^ (k + 3) ∣ d := by
    have h2m_eq : 2 * m = (2 ^ k - 1) * 2 ^ (k + 3) := by
      rw [hm_eq, show k + 3 = (k + 2) + 1 by omega, pow_succ]; ring
    rw [h2m_eq] at hd_dvd_2m
    have hd_pos : 0 < d := by
      by_contra h0
      have hd0 : d = 0 := by omega
      rw [hd0, zero_dvd_iff] at hd_dvd_2m
      have : 0 < (2 ^ k - 1) * 2 ^ (k + 3) := Nat.mul_pos (by omega) (pow_pos (by decide) _)
      omega
    -- Factor `d = 2 ^ v * r` with `r` odd (`¬ 2 ∣ r`)
    have hv_le : Nat.factorization d 2 ≤ k + 3 := by
      have hne0 : (2 ^ k - 1) * 2 ^ (k + 3) ≠ 0 := by
        have := Nat.mul_pos (by omega : 0 < 2 ^ k - 1) (pow_pos (by decide : 0 < 2) (k + 3))
        omega
      have hle := (Nat.factorization_le_iff_dvd hd_pos.ne' hne0).mpr hd_dvd_2m 2
      rw [Nat.factorization_mul (by omega) (by positivity), Finsupp.add_apply,
        Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same] at hle
      have hodd : ¬ 2 ∣ (2 ^ k - 1) := by
        have h2dvd : 2 ∣ 2 ^ k := dvd_pow_self 2 (by omega)
        obtain ⟨t, ht⟩ := h2dvd
        omega
      have hfac0 : (2 ^ k - 1).factorization 2 = 0 :=
        Nat.factorization_eq_zero_of_not_dvd hodd
      omega
    have hv_ge : k + 3 ≤ Nat.factorization d 2 := by
      by_contra hlt
      have hle2 : Nat.factorization d 2 ≤ k + 2 := by omega
      apply hd_ndvd_m
      rw [hm_eq]
      have hm_ne0 : (2 ^ k - 1) * 2 ^ (k + 2) ≠ 0 := by
        have := Nat.mul_pos (by omega : 0 < 2 ^ k - 1) (pow_pos (by decide : 0 < 2) (k + 2))
        omega
      rw [← Nat.factorization_le_iff_dvd hd_pos.ne' hm_ne0]
      intro r
      by_cases hr2 : r = 2
      · subst hr2
        rw [Nat.factorization_mul (by omega) (by positivity), Finsupp.add_apply,
          Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same]
        omega
      · have hne0 : (2 ^ k - 1) * 2 ^ (k + 3) ≠ 0 := by
          have := Nat.mul_pos (by omega : 0 < 2 ^ k - 1) (pow_pos (by decide : 0 < 2) (k + 3))
          omega
        have hle := (Nat.factorization_le_iff_dvd hd_pos.ne' hne0).mpr hd_dvd_2m r
        rw [Nat.factorization_mul (by omega) (by positivity), Finsupp.add_apply,
          Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_of_ne hr2,
          add_zero] at hle
        rw [Nat.factorization_mul (by omega) (by positivity), Finsupp.add_apply,
          Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_of_ne hr2,
          add_zero]
        exact hle
    have hv_eq : Nat.factorization d 2 = k + 3 := by omega
    rw [← hv_eq]
    exact Nat.ordProj_dvd d 2
  -- By Fermat's Little Theorem in `ZMod q`, `d ∣ q - 1`.
  have h2_ne0 : (2 : ZMod q) ≠ 0 := by
    intro h2z
    have h2z' : ((2 : ℕ) : ZMod q) = 0 := by simpa using h2z
    rw [ZMod.natCast_eq_zero_iff] at h2z'
    have := Nat.le_of_dvd (by decide) h2z'
    have := hq_prime.two_le
    omega
  have hd_dvd_q1 : d ∣ q - 1 :=
    orderOf_dvd_of_pow_eq_one (ZMod.pow_card_sub_one_eq_one h2_ne0)
  have hq_ge : 2 ^ (k + 3) + 1 ≤ q := by
    have hq1_pos : 0 < q - 1 := by have := hq_prime.two_le; omega
    have := Nat.le_of_dvd hq1_pos (dvd_trans h2k3_dvd_d hd_dvd_q1)
    omega
  -- If `N k` were composite, `q ^ 2 ≤ N k`, contradicting `(2 ^ (k + 3) + 1) ^ 2 > N k`!
  by_contra hnotp
  have hsq : q * q ≤ N k := by
    have h := Nat.minFac_sq_le_self (by omega) hnotp
    rwa [pow_two] at h
  have hbig : N k < (2 ^ (k + 3) + 1) * (2 ^ (k + 3) + 1) := by
    dsimp [N]
    have hpow1 : 2 ^ (k + 4) = 16 * 2 ^ k := by rw [pow_add]; ring
    have hpow2 : 2 ^ (k + 3) = 8 * 2 ^ k := by rw [pow_add]; ring
    rw [hpow1, hpow2]
    have h1 : (2 ^ k - 1) * (16 * 2 ^ k) + 1 ≤ 2 ^ k * (16 * 2 ^ k) := by
      have : 1 ≤ 16 * 2 ^ k := by omega
      have hmul : (2 ^ k - 1 + 1) * (16 * 2 ^ k) = 2 ^ k * (16 * 2 ^ k) := by
        rw [Nat.sub_add_cancel (by omega : 1 ≤ 2 ^ k)]
      rw [add_mul, one_mul] at hmul
      omega
    have h2 : 2 ^ k * (16 * 2 ^ k) < (8 * 2 ^ k + 1) * (8 * 2 ^ k + 1) := by
      have : (8 * 2 ^ k + 1) * (8 * 2 ^ k + 1) = 64 * (2 ^ k * 2 ^ k) + 16 * 2 ^ k + 1 := by ring
      have h3 : 2 ^ k * (16 * 2 ^ k) = 16 * (2 ^ k * 2 ^ k) := by ring
      omega
    exact lt_of_le_of_lt h1 h2
  have hle_sq : (2 ^ (k + 3) + 1) * (2 ^ (k + 3) + 1) ≤ q * q := Nat.mul_le_mul hq_ge hq_ge
  omega

end OMA.P_oeis_a400825

theorem OMA.solution : type_of% @OMA.S_oeis_a400825.main :=
  OMA.P_oeis_a400825.prove_a400825
