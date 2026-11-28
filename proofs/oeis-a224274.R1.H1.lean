import OMAReductions.R_oeis_a224274_R1

namespace OMA.Proof_oeis_a224274_R1_H1

private lemma two_mul_prod_one_add {ι R : Type*} [DecidableEq ι] [CommRing R]
    (a : R) (ha3 : a ^ 3 = 0) (f : ι → R) (A : Finset ι) :
    2 * (∏ i ∈ A, (1 + a * f i)) =
      2 + 2 * a * (∑ i ∈ A, f i) +
        a ^ 2 * ((∑ i ∈ A, f i) ^ 2 - ∑ i ∈ A, (f i) ^ 2) := by
  induction A using Finset.induction_on with
  | empty =>
    simp
  | @insert x s hx ih =>
    rw [Finset.prod_insert hx, Finset.sum_insert hx, Finset.sum_insert hx]
    have hmul : 2 * ((1 + a * f x) * ∏ i ∈ s, (1 + a * f i)) =
        (1 + a * f x) * (2 * ∏ i ∈ s, (1 + a * f i)) := by ring
    rw [hmul, ih]
    linear_combination
      (f x * ((∑ i ∈ s, f i) ^ 2 - ∑ i ∈ s, (f i) ^ 2)) * ha3

private lemma sum_zmod_sq_eq_zero (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) :
    ∑ k ∈ Finset.Icc 1 (p - 1), ((k : ZMod p) ^ 2) = 0 := by
  have hp : p.Prime := Fact.out
  have h3ne : (3 : ZMod p) ≠ 0 := by
    intro h0
    have hd : p ∣ 3 := (ZMod.natCast_eq_zero_iff 3 p).mp h0
    exact absurd (Nat.le_of_dvd (by decide) hd) (by omega)
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro h0
    have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h0
    exact absurd (Nat.le_of_dvd (by decide) hd) (by omega)
  have hbij : ∑ k ∈ Finset.Icc 1 (p - 1), ((2 * k : ZMod p) ^ 2) =
      ∑ k ∈ Finset.Icc 1 (p - 1), ((k : ZMod p) ^ 2) := by
    refine Finset.sum_bij (fun k _ => 2 * k % p) ?_ ?_ ?_ ?_
    · intro k hk
      rw [Finset.mem_Icc] at hk
      have h2kp : ¬ p ∣ 2 * k := fun h => by
        rcases hp.dvd_mul.mp h with h2 | hkp
        · exact absurd (Nat.le_of_dvd (by decide) h2) (by omega)
        · exact Nat.not_dvd_of_pos_of_lt hk.1 (by omega) hkp
      have hpos : 0 < 2 * k % p := Nat.pos_of_ne_zero (fun h => h2kp (Nat.dvd_of_mod_eq_zero h))
      rw [Finset.mem_Icc]
      exact ⟨by omega, by have := Nat.mod_lt (2 * k) hp.pos; omega⟩
    · intro k1 hk1 k2 hk2 heq
      rw [Finset.mem_Icc] at hk1 hk2
      have hz : (2 : ZMod p) * (k1 : ZMod p) = (2 : ZMod p) * (k2 : ZMod p) := by
        have h1 : ((2 * k1 % p : ℕ) : ZMod p) = (2 : ZMod p) * (k1 : ZMod p) := by
          rw [ZMod.natCast_mod, Nat.cast_mul, Nat.cast_ofNat]
        have h2 : ((2 * k2 % p : ℕ) : ZMod p) = (2 : ZMod p) * (k2 : ZMod p) := by
          rw [ZMod.natCast_mod, Nat.cast_mul, Nat.cast_ofNat]
        rw [← h1, ← h2, heq]
      have h12 : (k1 : ZMod p) = (k2 : ZMod p) := mul_left_cancel₀ h2ne hz
      have := congrArg ZMod.val h12
      rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega)] at this
      exact this
    · intro s hs
      rw [Finset.mem_Icc] at hs
      let k : ℕ := ((p + 1) / 2 * s) % p
      have hodd : p % 2 = 1 := hp.odd_of_ne_two (by omega) |> Nat.odd_iff.mp
      have h2inv : 2 * ((p + 1) / 2) = p + 1 := by omega
      have h2k : 2 * k % p = s := by
        have hz : ((2 * k % p : ℕ) : ZMod p) = (s : ZMod p) := by
          rw [ZMod.natCast_mod, Nat.cast_mul, ZMod.natCast_mod, Nat.cast_mul, ← mul_assoc,
            ← Nat.cast_mul, h2inv]
          simp
        have := congrArg ZMod.val hz
        rw [ZMod.val_natCast_of_lt (Nat.mod_lt _ hp.pos), ZMod.val_natCast_of_lt (by omega)] at this
        exact this
      have hk1 : 1 ≤ k := by
        by_contra h0
        have hk0 : k = 0 := by omega
        rw [hk0] at h2k
        simp at h2k
        omega
      exact ⟨k, Finset.mem_Icc.mpr ⟨hk1, by have := Nat.mod_lt ((p + 1) / 2 * s) hp.pos; omega⟩, h2k⟩
    · intro k _
      rw [ZMod.natCast_mod, Nat.cast_mul, Nat.cast_ofNat]
  have h4 : ∑ k ∈ Finset.Icc 1 (p - 1), ((2 * k : ZMod p) ^ 2) =
      4 * ∑ k ∈ Finset.Icc 1 (p - 1), ((k : ZMod p) ^ 2) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => by ring
  have h3s : (3 : ZMod p) * ∑ k ∈ Finset.Icc 1 (p - 1), ((k : ZMod p) ^ 2) = 0 := by
    linear_combination h4.symm.trans hbij
  exact (mul_eq_zero.mp h3s).resolve_left h3ne

private lemma sum_zmod_inv_eq_zero (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) :
    ∑ k ∈ Finset.Icc 1 (p - 1), ((k : ZMod p)⁻¹) = 0 := by
  have hp : p.Prime := Fact.out
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro h0
    have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h0
    exact absurd (Nat.le_of_dvd (by decide) hd) (by omega)
  have hrev : ∑ k ∈ Finset.Icc 1 (p - 1), (((p - k : ℕ) : ZMod p)⁻¹) =
      ∑ k ∈ Finset.Icc 1 (p - 1), ((k : ZMod p)⁻¹) := by
    refine Finset.sum_bij (fun k _ => p - k) ?_ ?_ ?_ ?_
    · intro k hk; rw [Finset.mem_Icc] at hk ⊢; omega
    · intro k1 hk1 k2 hk2 heq; rw [Finset.mem_Icc] at hk1 hk2; omega
    · intro k hk; rw [Finset.mem_Icc] at hk; exact ⟨p - k, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
    · intro k _; rfl
  have hneg : ∀ k ∈ Finset.Icc 1 (p - 1), (((p - k : ℕ) : ZMod p)⁻¹) = -((k : ZMod p)⁻¹) := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    rw [Nat.cast_sub (by omega), ZMod.natCast_self, zero_sub, inv_neg]
  have h2s : (2 : ZMod p) * ∑ k ∈ Finset.Icc 1 (p - 1), ((k : ZMod p)⁻¹) = 0 := by
    have : ∑ k ∈ Finset.Icc 1 (p - 1), (((p - k : ℕ) : ZMod p)⁻¹) =
        -(∑ k ∈ Finset.Icc 1 (p - 1), ((k : ZMod p)⁻¹)) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl hneg
    linear_combination hrev.symm.trans this
  exact (mul_eq_zero.mp h2s).resolve_left h2ne

private lemma sum_zmod_inv_sq_eq_zero (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) :
    ∑ k ∈ Finset.Icc 1 (p - 1), ((k : ZMod p)⁻¹) ^ 2 = 0 := by
  have hp : p.Prime := Fact.out
  have hbij : ∑ k ∈ Finset.Icc 1 (p - 1), ((k : ZMod p)⁻¹) ^ 2 =
      ∑ k ∈ Finset.Icc 1 (p - 1), ((k : ZMod p) ^ 2) := by
    refine Finset.sum_bij (fun k _ => ((k : ZMod p)⁻¹).val) ?_ ?_ ?_ ?_
    · intro k hk
      rw [Finset.mem_Icc] at hk
      have hkne : (k : ZMod p) ≠ 0 := by
        intro h0
        exact Nat.not_dvd_of_pos_of_lt hk.1 (by omega) ((ZMod.natCast_eq_zero_iff k p).mp h0)
      have hinv_ne : (k : ZMod p)⁻¹ ≠ 0 := inv_ne_zero hkne
      have hpos : 0 < ((k : ZMod p)⁻¹).val := Nat.pos_of_ne_zero fun h => hinv_ne (by
        have := ZMod.natCast_zmod_val ((k : ZMod p)⁻¹); rw [h, Nat.cast_zero] at this; exact this.symm)
      exact Finset.mem_Icc.mpr ⟨by omega, by have := ((k : ZMod p)⁻¹).val_lt; omega⟩
    · intro k1 hk1 k2 hk2 heq
      rw [Finset.mem_Icc] at hk1 hk2
      have h1 : (k1 : ZMod p)⁻¹ = (k2 : ZMod p)⁻¹ := by
        rw [← ZMod.natCast_zmod_val ((k1 : ZMod p)⁻¹), ← ZMod.natCast_zmod_val ((k2 : ZMod p)⁻¹), heq]
      have h2 : (k1 : ZMod p) = (k2 : ZMod p) := inv_injective h1
      have := congrArg ZMod.val h2
      rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega)] at this
      exact this
    · intro s hs
      rw [Finset.mem_Icc] at hs
      have hsne : (s : ZMod p) ≠ 0 := by
        intro h0
        exact Nat.not_dvd_of_pos_of_lt hs.1 (by omega) ((ZMod.natCast_eq_zero_iff s p).mp h0)
      have hinv_ne : (s : ZMod p)⁻¹ ≠ 0 := inv_ne_zero hsne
      let k := ((s : ZMod p)⁻¹).val
      have hkpos : 0 < k := Nat.pos_of_ne_zero fun h => hinv_ne (by
        have hval : (k : ZMod p) = (s : ZMod p)⁻¹ := ZMod.natCast_zmod_val ((s : ZMod p)⁻¹)
        rw [h, Nat.cast_zero] at hval
        exact hval.symm)
      refine ⟨k, Finset.mem_Icc.mpr ⟨by omega, by have := ((s : ZMod p)⁻¹).val_lt; omega⟩, ?_⟩
      have hk : (k : ZMod p) = (s : ZMod p)⁻¹ := ZMod.natCast_zmod_val _
      rw [hk, inv_inv, ZMod.val_natCast_of_lt (by omega)]
    · intro k _
      rw [ZMod.natCast_zmod_val]
  rw [hbij]
  exact sum_zmod_sq_eq_zero p hp5

private lemma mul_inv_eq_one_zmod {m k : ℕ} (hcop : Nat.Coprime k m) :
    (k : ZMod m) * (k : ZMod m)⁻¹ = 1 := by
  have hunit : IsUnit (k : ZMod m) := (ZMod.isUnit_iff_coprime k m).mpr hcop
  exact ZMod.mul_inv_of_unit (k : ZMod m) hunit

private lemma p_mul_sum_inv_eq_zero_zmod_p3 (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) :
    (p : ZMod (p ^ 3)) * ∑ k ∈ Finset.Icc 1 (p - 1), (k : ZMod (p ^ 3))⁻¹ = 0 := by
  have hp : p.Prime := Fact.out
  let S := Finset.Icc 1 (p - 1)
  have hcop : ∀ k ∈ S, Nat.Coprime k (p ^ 3) := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    exact (hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hk.1 (by omega))).symm.pow_right 3
  have hrev : ∑ k ∈ S, ((p - k : ℕ) : ZMod (p ^ 3))⁻¹ = ∑ k ∈ S, (k : ZMod (p ^ 3))⁻¹ := by
    refine Finset.sum_bij (fun k _ => p - k) ?_ ?_ ?_ ?_
    · intro k hk; rw [Finset.mem_Icc] at hk ⊢; omega
    · intro k1 hk1 k2 hk2 heq; rw [Finset.mem_Icc] at hk1 hk2; omega
    · intro k hk; rw [Finset.mem_Icc] at hk; exact ⟨p - k, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
    · intro k _; rfl
  have hpair : (2 : ZMod (p ^ 3)) * (∑ k ∈ S, (k : ZMod (p ^ 3))⁻¹) =
      (p : ZMod (p ^ 3)) * ∑ k ∈ S, (k : ZMod (p ^ 3))⁻¹ * ((p - k : ℕ) : ZMod (p ^ 3))⁻¹ := by
    have h2sum : (2 : ZMod (p ^ 3)) * (∑ k ∈ S, (k : ZMod (p ^ 3))⁻¹) =
        ∑ k ∈ S, ((k : ZMod (p ^ 3))⁻¹ + ((p - k : ℕ) : ZMod (p ^ 3))⁻¹) := by
      rw [Finset.sum_add_distrib, hrev, two_mul]
    rw [h2sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_Icc.mp hk
    have hpk : p - k ∈ S := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    have h1 := mul_inv_eq_one_zmod (hcop k hk)
    have h2 := mul_inv_eq_one_zmod (hcop (p - k) hpk)
    have hsum : (k : ZMod (p ^ 3)) + ((p - k : ℕ) : ZMod (p ^ 3)) = (p : ZMod (p ^ 3)) := by
      rw [← Nat.cast_add, Nat.add_sub_of_le (by omega)]
    calc
      (k : ZMod (p ^ 3))⁻¹ + ((p - k : ℕ) : ZMod (p ^ 3))⁻¹
          = (k : ZMod (p ^ 3))⁻¹ * (((p - k : ℕ) : ZMod (p ^ 3)) * ((p - k : ℕ) : ZMod (p ^ 3))⁻¹) +
            ((k : ZMod (p ^ 3)) * (k : ZMod (p ^ 3))⁻¹) * ((p - k : ℕ) : ZMod (p ^ 3))⁻¹ := by
              rw [h1, h2, mul_one, one_mul]
      _ = ((k : ZMod (p ^ 3)) + ((p - k : ℕ) : ZMod (p ^ 3))) *
            ((k : ZMod (p ^ 3))⁻¹ * ((p - k : ℕ) : ZMod (p ^ 3))⁻¹) := by ring
      _ = (p : ZMod (p ^ 3)) * ((k : ZMod (p ^ 3))⁻¹ * ((p - k : ℕ) : ZMod (p ^ 3))⁻¹) := by rw [hsum]
  have h2cop : Nat.Coprime 2 (p ^ 3) :=
    ((Nat.coprime_primes Nat.prime_two hp).mpr (by omega)).pow_right 3
  have h2unit : IsUnit (2 : ZMod (p ^ 3)) := (ZMod.isUnit_iff_coprime 2 (p ^ 3)).mpr h2cop
  have h2mul : (2 : ZMod (p ^ 3)) * ((p : ZMod (p ^ 3)) * ∑ k ∈ S, (k : ZMod (p ^ 3))⁻¹) =
      (p : ZMod (p ^ 3)) ^ 2 * ∑ k ∈ S, (k : ZMod (p ^ 3))⁻¹ * ((p - k : ℕ) : ZMod (p ^ 3))⁻¹ := by
    calc
      (2 : ZMod (p ^ 3)) * ((p : ZMod (p ^ 3)) * ∑ k ∈ S, (k : ZMod (p ^ 3))⁻¹)
          = (p : ZMod (p ^ 3)) * ((2 : ZMod (p ^ 3)) * ∑ k ∈ S, (k : ZMod (p ^ 3))⁻¹) := by ring
      _ = (p : ZMod (p ^ 3)) * ((p : ZMod (p ^ 3)) *
            ∑ k ∈ S, (k : ZMod (p ^ 3))⁻¹ * ((p - k : ℕ) : ZMod (p ^ 3))⁻¹) := by rw [hpair]
      _ = (p : ZMod (p ^ 3)) ^ 2 *
            ∑ k ∈ S, (k : ZMod (p ^ 3))⁻¹ * ((p - k : ℕ) : ZMod (p ^ 3))⁻¹ := by ring
  let T : ZMod (p ^ 3) := ∑ k ∈ S, (k : ZMod (p ^ 3))⁻¹ * ((p - k : ℕ) : ZMod (p ^ 3))⁻¹
  have hdvd : p ∣ T.val := by
    have hcast : ZMod.castHom (dvd_pow_self p (by decide : 3 ≠ 0)) (ZMod p) T = 0 := by
      have hmap : ∀ k ∈ S,
          ZMod.castHom (dvd_pow_self p (by decide : 3 ≠ 0)) (ZMod p)
            ((k : ZMod (p ^ 3))⁻¹ * ((p - k : ℕ) : ZMod (p ^ 3))⁻¹) =
            -((k : ZMod p)⁻¹) ^ 2 := by
        intro k hk
        have hk' := Finset.mem_Icc.mp hk
        have hpk : p - k ∈ S := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
        let φ := ZMod.castHom (dvd_pow_self p (by decide : 3 ≠ 0)) (ZMod p)
        have hφk : φ (k : ZMod (p ^ 3))⁻¹ = (k : ZMod p)⁻¹ := by
          have h1 := congrArg φ (mul_inv_eq_one_zmod (hcop k hk))
          rw [map_mul, map_one, map_natCast] at h1
          have hkne : (k : ZMod p) ≠ 0 := by
            intro h0
            exact Nat.not_dvd_of_pos_of_lt hk'.1 (by omega) ((ZMod.natCast_eq_zero_iff k p).mp h0)
          exact mul_left_cancel₀ hkne (h1.trans (mul_inv_cancel₀ hkne).symm)
        have hφpk : φ ((p - k : ℕ) : ZMod (p ^ 3))⁻¹ = -((k : ZMod p)⁻¹) := by
          have h1 := congrArg φ (mul_inv_eq_one_zmod (hcop (p - k) hpk))
          rw [map_mul, map_one, map_natCast, Nat.cast_sub (by omega), ZMod.natCast_self, zero_sub] at h1
          have hkne : (k : ZMod p) ≠ 0 := by
            intro h0
            exact Nat.not_dvd_of_pos_of_lt hk'.1 (by omega) ((ZMod.natCast_eq_zero_iff k p).mp h0)
          have hneg : -(k : ZMod p) ≠ 0 := neg_ne_zero.mpr hkne
          exact mul_left_cancel₀ hneg (h1.trans (by rw [mul_neg, neg_mul, neg_neg, mul_inv_cancel₀ hkne]))
        rw [map_mul, hφk, hφpk]
        ring
      change ZMod.castHom (dvd_pow_self p (by decide : 3 ≠ 0)) (ZMod p)
        (∑ k ∈ S, (k : ZMod (p ^ 3))⁻¹ * ((p - k : ℕ) : ZMod (p ^ 3))⁻¹) = 0
      rw [map_sum, Finset.sum_congr rfl hmap, Finset.sum_neg_distrib,
        sum_zmod_inv_sq_eq_zero p hp5, neg_zero]
    rw [← ZMod.natCast_eq_zero_iff]
    rw [← hcast]
    have hv := ZMod.natCast_zmod_val T
    conv_rhs => rw [← hv]
    rw [map_natCast]
  obtain ⟨c, hc⟩ := hdvd
  have hT : T = (p : ZMod (p ^ 3)) * (c : ZMod (p ^ 3)) := by
    rw [← ZMod.natCast_zmod_val T, hc, Nat.cast_mul]
  have hp2T : (p : ZMod (p ^ 3)) ^ 2 * T = 0 := by
    rw [hT]
    have hp3z : ((p : ZMod (p ^ 3)) ^ 3) = 0 := by
      rw [← Nat.cast_pow, ZMod.natCast_self]
    linear_combination (c : ZMod (p ^ 3)) * hp3z
  rw [hp2T] at h2mul
  exact h2unit.mul_left_cancel (h2mul.trans (mul_zero _).symm)

private lemma p2_mul_quad_eq_zero_zmod_p3 (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) :
    (p : ZMod (p ^ 3)) ^ 2 *
      ((∑ k ∈ Finset.Icc 1 (p - 1), (k : ZMod (p ^ 3))⁻¹) ^ 2 -
        ∑ k ∈ Finset.Icc 1 (p - 1), ((k : ZMod (p ^ 3))⁻¹) ^ 2) = 0 := by
  have hp : p.Prime := Fact.out
  let S := Finset.Icc 1 (p - 1)
  have hcop : ∀ k ∈ S, Nat.Coprime k (p ^ 3) := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    exact (hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hk.1 (by omega))).symm.pow_right 3
  let Q : ZMod (p ^ 3) :=
    (∑ k ∈ S, (k : ZMod (p ^ 3))⁻¹) ^ 2 - ∑ k ∈ S, ((k : ZMod (p ^ 3))⁻¹) ^ 2
  have hdvd : p ∣ Q.val := by
    let φ := ZMod.castHom (dvd_pow_self p (by decide : 3 ≠ 0)) (ZMod p)
    have hφk : ∀ k ∈ S, φ (k : ZMod (p ^ 3))⁻¹ = (k : ZMod p)⁻¹ := by
      intro k hk
      have hk' := Finset.mem_Icc.mp hk
      have h1 := congrArg φ (mul_inv_eq_one_zmod (hcop k hk))
      rw [map_mul, map_one, map_natCast] at h1
      have hkne : (k : ZMod p) ≠ 0 := by
        intro h0
        exact Nat.not_dvd_of_pos_of_lt hk'.1 (by omega) ((ZMod.natCast_eq_zero_iff k p).mp h0)
      exact mul_left_cancel₀ hkne (h1.trans (mul_inv_cancel₀ hkne).symm)
    have hφQ : φ Q = 0 := by
      simp only [Q, map_sub, map_pow, map_sum]
      rw [Finset.sum_congr rfl hφk]
      have hsq : ∑ k ∈ S, (φ (k : ZMod (p ^ 3))⁻¹) ^ 2 = ∑ k ∈ S, ((k : ZMod p)⁻¹) ^ 2 := by
        refine Finset.sum_congr rfl fun k hk => ?_
        rw [hφk k hk]
      rw [hsq, sum_zmod_inv_eq_zero p hp5, sum_zmod_inv_sq_eq_zero p hp5]
      ring
    rw [← ZMod.natCast_eq_zero_iff, ← hφQ]
    conv_rhs => rw [← ZMod.natCast_zmod_val Q]
    rw [map_natCast]
  obtain ⟨c, hc⟩ := hdvd
  have hQ : Q = (p : ZMod (p ^ 3)) * (c : ZMod (p ^ 3)) := by
    rw [← ZMod.natCast_zmod_val Q, hc, Nat.cast_mul]
  change (p : ZMod (p ^ 3)) ^ 2 * Q = 0
  rw [hQ]
  have hp3z : ((p : ZMod (p ^ 3)) ^ 3) = 0 := by
    rw [← Nat.cast_pow, ZMod.natCast_self]
  linear_combination (c : ZMod (p ^ 3)) * hp3z

private lemma choose_four_mul_div_four (p : ℕ) (hp : 0 < p) :
    (4 * p).choose p / 4 = (4 * p - 1).choose (p - 1) := by
  have hmul := Nat.add_one_mul_choose_eq (4 * p - 1) (p - 1)
  rw [show 4 * p - 1 + 1 = 4 * p by omega, show p - 1 + 1 = p by omega] at hmul
  have heq : (4 * p).choose p = 4 * (4 * p - 1).choose (p - 1) := by
    have h1 : p * (4 * p).choose p = p * (4 * (4 * p - 1).choose (p - 1)) := by
      linear_combination -hmul
    exact Nat.eq_of_mul_eq_mul_left hp h1
  rw [heq, Nat.mul_div_right _ (by decide : 0 < 4)]

private lemma choose_mul_factorial_eq_prod (p : ℕ) (hp : 1 ≤ p) :
    (4 * p - 1).choose (p - 1) * (p - 1).factorial =
      ∏ k ∈ Finset.Icc 1 (p - 1), (3 * p + k) := by
  have h1 := Nat.descFactorial_eq_factorial_mul_choose (4 * p - 1) (p - 1)
  rw [mul_comm (p - 1).factorial] at h1
  rw [← h1]
  have hdesc : ∀ m : ℕ, (3 * p + m).descFactorial m = ∏ k ∈ Finset.Icc 1 m, (3 * p + k) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [show 3 * p + (m + 1) = (3 * p + m) + 1 by omega, Nat.succ_descFactorial_succ, ih]
      rw [show Finset.Icc 1 (m + 1) = insert (m + 1) (Finset.Icc 1 m) by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega]
      rw [Finset.prod_insert (by simp)]
      ring
  have hsub : 4 * p - 1 = 3 * p + (p - 1) := by omega
  rw [hsub]
  exact hdesc (p - 1)

private lemma factorial_eq_prod_Icc (m : ℕ) :
    m.factorial = ∏ k ∈ Finset.Icc 1 m, k := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.factorial_succ, ih]
    rw [show Finset.Icc 1 (m + 1) = insert (m + 1) (Finset.Icc 1 m) by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega]
    rw [Finset.prod_insert (by simp)]

end OMA.Proof_oeis_a224274_R1_H1

theorem OMA.solution : OMA.R_oeis_a224274_R1.H1 := by
  intro p hp hodd
  open OMA.Proof_oeis_a224274_R1_H1 in
  by_cases hp3 : p = 3
  · subst hp3
    decide
  · have hp2 : p ≠ 2 := by
      intro h; rw [h] at hodd; exact absurd hodd (by decide)
    have hp5 : 5 ≤ p := by
      have hge := hp.two_le
      have : p ≠ 4 := fun h => by rw [h] at hp; exact absurd hp (by decide)
      omega
    have : Fact p.Prime := ⟨hp⟩
    change (4 * p).choose p / 4 ≡ 1 [MOD p ^ 3]
    rw [choose_four_mul_div_four p hp.pos]
    rw [← ZMod.natCast_eq_natCast_iff]
    rw [Nat.cast_one]
    let S := Finset.Icc 1 (p - 1)
    have hcop : ∀ k ∈ S, Nat.Coprime k (p ^ 3) := by
      intro k hk
      rw [Finset.mem_Icc] at hk
      exact (hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hk.1 (by omega))).symm.pow_right 3
    have hfac_cop : Nat.Coprime (p - 1).factorial (p ^ 3) := by
      have hfp : Nat.Coprime (p - 1).factorial p := by
        rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
        intro hd
        exact absurd (hp.dvd_factorial.mp hd) (by omega)
      exact hfp.pow_right 3
    have hfac_unit : IsUnit ((p - 1).factorial : ZMod (p ^ 3)) :=
      (ZMod.isUnit_iff_coprime _ _).mpr hfac_cop
    apply hfac_unit.mul_right_cancel
    rw [one_mul, ← Nat.cast_mul, choose_mul_factorial_eq_prod p hp.one_le,
      factorial_eq_prod_Icc (p - 1), Nat.cast_prod, Nat.cast_prod]
    have hprod_factor :
        (∏ k ∈ S, ((3 * p + k : ℕ) : ZMod (p ^ 3))) =
          (∏ k ∈ S, (k : ZMod (p ^ 3))) *
            ∏ k ∈ S, (1 + (3 * (p : ZMod (p ^ 3))) * (k : ZMod (p ^ 3))⁻¹) := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k hk => ?_
      have h1 := mul_inv_eq_one_zmod (hcop k hk)
      push_cast
      calc
        3 * (p : ZMod (p ^ 3)) + (k : ZMod (p ^ 3))
            = (k : ZMod (p ^ 3)) + 3 * (p : ZMod (p ^ 3)) * ((k : ZMod (p ^ 3)) * (k : ZMod (p ^ 3))⁻¹) := by
              rw [h1, mul_one]; ring
        _ = (k : ZMod (p ^ 3)) * (1 + 3 * (p : ZMod (p ^ 3)) * (k : ZMod (p ^ 3))⁻¹) := by ring
    rw [hprod_factor]
    have hprod_one : ∏ k ∈ S, (1 + (3 * (p : ZMod (p ^ 3))) * (k : ZMod (p ^ 3))⁻¹) = 1 := by
      have ha3 : (3 * (p : ZMod (p ^ 3))) ^ 3 = 0 := by
        have hp3z : (p : ZMod (p ^ 3)) ^ 3 = 0 := by
          rw [← Nat.cast_pow, ZMod.natCast_self]
        linear_combination 27 * hp3z
      have h2eq := two_mul_prod_one_add (3 * (p : ZMod (p ^ 3))) ha3
        (fun k : ℕ => (k : ZMod (p ^ 3))⁻¹) S
      have hterm1 : (3 * (p : ZMod (p ^ 3))) * ∑ k ∈ S, (k : ZMod (p ^ 3))⁻¹ = 0 := by
        have h := p_mul_sum_inv_eq_zero_zmod_p3 p hp5
        linear_combination 3 * h
      have hterm2 : (3 * (p : ZMod (p ^ 3))) ^ 2 *
          ((∑ k ∈ S, (k : ZMod (p ^ 3))⁻¹) ^ 2 - ∑ k ∈ S, ((k : ZMod (p ^ 3))⁻¹) ^ 2) = 0 := by
        have h := p2_mul_quad_eq_zero_zmod_p3 p hp5
        linear_combination 9 * h
      rw [show 2 * (3 * (p : ZMod (p ^ 3))) * ∑ k ∈ S, (k : ZMod (p ^ 3))⁻¹ =
        2 * ((3 * (p : ZMod (p ^ 3))) * ∑ k ∈ S, (k : ZMod (p ^ 3))⁻¹) by ring,
        hterm1, hterm2, mul_zero, add_zero, add_zero] at h2eq
      have h2cop : Nat.Coprime 2 (p ^ 3) :=
        ((Nat.coprime_primes Nat.prime_two hp).mpr (by omega)).pow_right 3
      have h2unit : IsUnit (2 : ZMod (p ^ 3)) := (ZMod.isUnit_iff_coprime 2 (p ^ 3)).mpr h2cop
      exact h2unit.mul_left_cancel (h2eq.trans (mul_one _).symm)
    rw [hprod_one, mul_one]
