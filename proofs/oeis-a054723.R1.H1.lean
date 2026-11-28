import OMAReductions.R_oeis_a054723_R1
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity

/-!
# Proof of `oeis-a054723.R1.H1`

Proves the Euler–Lagrange criterion: for a prime `p ≡ 3 (mod 4)`, `2 * p + 1` is prime if and only
if `2 * p + 1 ∣ 2 ^ p - 1`.

- Forward (`(2 * p + 1).Prime → 2 * p + 1 ∣ 2 ^ p - 1`): `q = 2 * p + 1 ≡ 7 (mod 8)`, so `2` is a
  square modulo `q` (`ZMod.exists_sq_eq_two_iff`). Writing `2 = c ^ 2` in `ZMod q` (with `c ≠ 0`),
  `2 ^ p = c ^ (2 * p) = c ^ (q - 1) = 1` in `ZMod q`, so `q ∣ 2 ^ p - 1`.
- Backward (`2 * p + 1 ∣ 2 ^ p - 1 → (2 * p + 1).Prime`): let `r` be the smallest prime factor of
  `2 * p + 1`. Then `r` is odd and `r ∣ 2 ^ p - 1`, so `orderOf (2 : ZMod r) = p`, hence `p ∣ r - 1`
  and `2 * p ∣ r - 1`, giving `2 * p + 1 ≤ r ≤ 2 * p + 1`, so `2 * p + 1 = r` is prime.
-/

theorem OMA.solution : OMA.R_oeis_a054723_R1.H1 := by
  intro p hp hp4
  set q := 2 * p + 1
  constructor
  · intro hq
    have : Fact q.Prime := ⟨hq⟩
    have hq2 : q ≠ 2 := by dsimp [q]; omega
    have hq8 : q % 8 = 7 := by dsimp [q]; omega
    have hsq : IsSquare (2 : ZMod q) := by
      rw [ZMod.exists_sq_eq_two_iff hq2]
      exact Or.inr hq8
    obtain ⟨c, hc⟩ := hsq
    have hc0 : c ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hc
      have h2q : q ∣ 2 := (ZMod.natCast_eq_zero_iff 2 q).mp (by simpa using hc)
      have := Nat.le_of_dvd (by decide) h2q
      have := hq.two_le
      omega
    have h2p : (2 : ZMod q) ^ p = 1 := by
      have hsq' : (2 : ZMod q) = c ^ 2 := by rw [sq, hc]
      rw [hsq', ← pow_mul, show 2 * p = q - 1 by omega]
      exact ZMod.pow_card_sub_one_eq_one hc0
    have hmod : 2 ^ p ≡ 1 [MOD q] := by
      rw [← ZMod.natCast_eq_natCast_iff]
      simpa using h2p
    exact (Nat.modEq_iff_dvd' Nat.one_le_two_pow).mp hmod.symm
  · intro hdvd
    have hq1 : q ≠ 1 := by dsimp [q]; have := hp.two_le; omega
    set r := q.minFac
    have hr : r.Prime := Nat.minFac_prime hq1
    have hrdvd_q : r ∣ q := Nat.minFac_dvd q
    have hr_le : r ≤ q := Nat.le_of_dvd (by dsimp [q]; omega) hrdvd_q
    have hr_odd : r ≠ 2 := by
      rintro heq
      have h2q : 2 ∣ q := heq ▸ hrdvd_q
      dsimp [q] at h2q
      omega
    have hrdvd : r ∣ 2 ^ p - 1 := dvd_trans hrdvd_q hdvd
    have : Fact r.Prime := ⟨hr⟩
    have h2u : (2 : ZMod r) ≠ 0 := by
      intro h0
      have hd : r ∣ 2 := (ZMod.natCast_eq_zero_iff 2 r).mp (by simpa using h0)
      have := Nat.le_of_dvd (by decide) hd
      have := hr.two_le
      omega
    have h2p1 : (2 : ZMod r) ^ p = 1 := by
      have hmod : 2 ^ p ≡ 1 [MOD r] := ((Nat.modEq_iff_dvd' Nat.one_le_two_pow).mpr hrdvd).symm
      have := (ZMod.natCast_eq_natCast_iff (2 ^ p) 1 r).mpr hmod
      simpa using this
    have h2ne1 : (2 : ZMod r) ≠ 1 := by
      intro h1
      have : (1 : ZMod r) = 0 := by linear_combination h1
      exact one_ne_zero this
    have hord_dvd_p : orderOf (2 : ZMod r) ∣ p := orderOf_dvd_of_pow_eq_one h2p1
    have hord_ne1 : orderOf (2 : ZMod r) ≠ 1 := fun h1 => h2ne1 (orderOf_eq_one_iff.mp h1)
    have hord_eq : orderOf (2 : ZMod r) = p :=
      (Nat.dvd_prime hp).mp hord_dvd_p |>.resolve_left hord_ne1
    have hp_dvd_r1 : p ∣ r - 1 := by
      rw [← hord_eq]
      exact orderOf_dvd_of_pow_eq_one (ZMod.pow_card_sub_one_eq_one h2u)
    have h2_dvd_r1 : 2 ∣ r - 1 := by
      have := hr.two_le
      have hrodd : r % 2 = 1 := by
        by_contra hev
        have h2r : 2 ∣ r := Nat.dvd_of_mod_eq_zero (by omega)
        rcases (Nat.dvd_prime hr).mp h2r with h | h <;> omega
      omega
    have hcop : Nat.Coprime 2 p := by
      refine (Nat.coprime_primes Nat.prime_two hp).mpr ?_
      omega
    have h2p_dvd : 2 * p ∣ r - 1 := hcop.mul_dvd_of_dvd_of_dvd h2_dvd_r1 hp_dvd_r1
    have hr1_pos : 0 < r - 1 := by have := hr.two_le; omega
    have h2p_le : 2 * p ≤ r - 1 := Nat.le_of_dvd hr1_pos h2p_dvd
    have hrq : r = q := by dsimp [q] at *; omega
    exact hrq ▸ hr
