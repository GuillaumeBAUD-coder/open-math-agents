import OMAReductions.R_oeis_a284760_R1
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Proof of `oeis-a284760.R1.H2`

Proves that whenever `0 < n` and `4 ∣ n`, `n ^ 4` does not divide `∑ i ∈ Ico 1 n, i ^ (n - 2)`.

Write `n = 2 ^ a * b` with `a ≥ 2` and `b` odd, and work modulo `2 ^ a`:
- Every even term satisfies `2 ^ a ∣ i ^ (n - 2)` since `a ≤ 2 ^ a - 2 ≤ n - 2`.
- Every odd term is a unit modulo `2 ^ a`; since `φ(2 ^ a) = 2 ^ (a - 1) ∣ n`, we have
  `i ^ (n - 2) ≡ (i⁻¹) ^ 2 (mod 2 ^ a)`.
- Summing over `b` full periods of length `2 ^ a` and reindexing by `i ↦ i⁻¹` yields
  `∑_{i=1}^{n-1} i ^ (n - 2) ≡ b * ∑_{j=0}^{2^(a-1)-1} (2*j + 1)^2 (mod 2 ^ a)`.
- By the identity `3 * ∑_{j=0}^{m-1} (2*j + 1)^2 = m * (4 * m^2 - 1)`, the sum has `2`-adic
  valuation `a - 1 < a`, so `2 ^ a` (and hence `n ^ 4`) cannot divide it.
-/

namespace OeisA284760R1H2Proof

open Finset

private lemma a_le_two_pow_sub_two {a : ℕ} (ha : 2 ≤ a) : a + 2 ≤ 2 ^ a := by
  induction a, ha using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
    rw [pow_succ]
    have h4 : 4 ≤ 2 ^ k := by
      have := Nat.pow_le_pow_right (by decide : 0 < 2) hk
      norm_num at this
      exact this
    omega

private lemma three_mul_sum_odd_sq (m : ℕ) :
    3 * ∑ j ∈ range m, (2 * j + 1) ^ 2 = m * (4 * m ^ 2 - 1) := by
  induction m with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ, mul_add, ih]
    rcases eq_or_ne k 0 with rfl | hk
    · decide
    · have h1 : 1 ≤ 4 * k ^ 2 := by
        have : 1 ≤ k ^ 2 := Nat.one_le_pow 2 k (Nat.pos_of_ne_zero hk)
        omega
      have h2 : 1 ≤ 4 * (k + 1) ^ 2 := by
        have : 1 ≤ (k + 1) ^ 2 := Nat.one_le_pow 2 (k + 1) (by omega)
        omega
      zify [h1, h2]
      ring

private lemma odd_pow_mod_two_pow_pos {a n i : ℕ} (ha : 2 ≤ a) (hn : 0 < n) (hdvd : 2 ^ a ∣ n)
    (hodd : Odd i) :
    (i : ZMod (2 ^ a)) ^ (n - 2) * (i : ZMod (2 ^ a)) ^ 2 = 1 := by
  have h4 : 4 ≤ 2 ^ a := by
    have := Nat.pow_le_pow_right (by decide : 0 < 2) ha
    norm_num at this
    exact this
  have hge : 2 ≤ n := le_trans (by omega : 2 ≤ 4) (le_trans h4 (Nat.le_of_dvd hn hdvd))
  have hcop : Nat.Coprime i (2 ^ a) := (Nat.coprime_two_right.mpr hodd).pow_right a
  have htot : Nat.totient (2 ^ a) = 2 ^ (a - 1) := by
    rw [Nat.totient_prime_pow Nat.prime_two (by omega)]
    simp
  have htot_dvd : Nat.totient (2 ^ a) ∣ n := by
    rw [htot]
    exact dvd_trans (Nat.pow_dvd_pow 2 (by omega : a - 1 ≤ a)) hdvd
  obtain ⟨k, hk⟩ := htot_dvd
  rw [← pow_add, Nat.sub_add_cancel hge, hk, pow_mul]
  have heul : ((i ^ Nat.totient (2 ^ a) : ℕ) : ZMod (2 ^ a)) = 1 := by
    rw [← Nat.cast_one, ZMod.natCast_eq_natCast_iff]
    exact Nat.ModEq.pow_totient hcop
  push_cast at heul ⊢
  rw [heul, one_pow]

private lemma sum_units_inv_sq (M : ℕ) [NeZero M] :
    ∑ u : (ZMod M)ˣ, ((u⁻¹ : (ZMod M)ˣ) : ZMod M) ^ 2 =
      ∑ u : (ZMod M)ˣ, (u : ZMod M) ^ 2 := by
  exact Fintype.sum_equiv (Equiv.inv (ZMod M)ˣ) _ _ (fun _ => rfl)

private lemma sum_range_pow_mod_two_pow {a n : ℕ} (ha : 2 ≤ a) (hn : 0 < n) (hdvd : 2 ^ a ∣ n) :
    ∑ i ∈ range (2 ^ a), (i : ZMod (2 ^ a)) ^ (n - 2) =
      ∑ j ∈ range (2 ^ (a - 1)), ((2 * j + 1 : ℕ) : ZMod (2 ^ a)) ^ 2 := by
  have : NeZero (2 ^ a) := ⟨pow_ne_zero a (by decide)⟩
  have hpos2a : 0 < 2 ^ a := pow_pos (by decide) a
  have hle_exp : a ≤ n - 2 := by
    have h1 := a_le_two_pow_sub_two ha
    have h2 : 2 ^ a ≤ n := Nat.le_of_dvd hn hdvd
    omega
  -- Split range (2^a) into even and odd indices
  have hodd_only :
      ∑ i ∈ range (2 ^ a), (i : ZMod (2 ^ a)) ^ (n - 2) =
        ∑ i ∈ (range (2 ^ a)).filter (fun i => i % 2 = 1), (i : ZMod (2 ^ a)) ^ (n - 2) := by
    rw [← Finset.sum_filter_add_sum_filter_not (range (2 ^ a)) (fun i => i % 2 = 1)]
    have heven_zero :
        ∑ i ∈ (range (2 ^ a)).filter (fun i => ¬ i % 2 = 1), (i : ZMod (2 ^ a)) ^ (n - 2) = 0 := by
      refine Finset.sum_eq_zero fun i hi => ?_
      have hmod : i % 2 = 0 := by
        have := (Finset.mem_filter.mp hi).2
        omega
      obtain ⟨j, rfl⟩ := Nat.dvd_of_mod_eq_zero hmod
      have hd : 2 ^ a ∣ (2 * j) ^ (n - 2) := by
        rw [mul_pow]
        exact dvd_mul_of_dvd_left (Nat.pow_dvd_pow 2 hle_exp) _
      rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
      exact hd
    rw [heven_zero, add_zero]
  rw [hodd_only]
  -- Reindex odd numbers in range (2^a) to (ZMod (2^a))ˣ
  have hunit_eq :
      ∑ i ∈ (range (2 ^ a)).filter (fun i => i % 2 = 1), (i : ZMod (2 ^ a)) ^ (n - 2) =
        ∑ u : (ZMod (2 ^ a))ˣ, ((u⁻¹ : (ZMod (2 ^ a))ˣ) : ZMod (2 ^ a)) ^ 2 := by
    symm
    refine Finset.sum_nbij'
      (fun u : (ZMod (2 ^ a))ˣ => (u : ZMod (2 ^ a)).val)
      (fun i => if hi : Nat.Coprime i (2 ^ a) then ZMod.unitOfCoprime i hi else 1)
      ?_ ?_ ?_ ?_ ?_
    · intro u _
      rw [Finset.mem_filter, Finset.mem_range]
      refine ⟨ZMod.val_lt _, ?_⟩
      have hcop : Nat.Coprime (u : ZMod (2 ^ a)).val (2 ^ a) := by
        have hunit : IsUnit ((u : ZMod (2 ^ a)).val : ZMod (2 ^ a)) := by
          rw [ZMod.natCast_zmod_val]
          exact u.isUnit
        exact (ZMod.isUnit_iff_coprime _ _).mp hunit
      have hcop2 : Nat.Coprime (u : ZMod (2 ^ a)).val 2 :=
        Nat.Coprime.coprime_dvd_right (dvd_pow_self 2 (by omega)) hcop
      have hodd := Nat.coprime_two_right.mp hcop2
      exact Nat.odd_iff.mp hodd
    · intro i _
      exact Finset.mem_univ _
    · intro u _
      have hcop : Nat.Coprime (u : ZMod (2 ^ a)).val (2 ^ a) :=
        (ZMod.isUnit_iff_coprime _ _).mp (by rw [ZMod.natCast_zmod_val]; exact u.isUnit)
      rw [dif_pos hcop]
      ext
      simp [ZMod.coe_unitOfCoprime]
    · intro i hi
      rw [Finset.mem_filter, Finset.mem_range] at hi
      have hcop : Nat.Coprime i (2 ^ a) :=
        (Nat.coprime_two_right.mpr (Nat.odd_iff.mpr hi.2)).pow_right a
      rw [dif_pos hcop]
      simp [ZMod.coe_unitOfCoprime, ZMod.val_natCast_of_lt hi.1]
    · intro u _
      have hval_cast : (((u : ZMod (2 ^ a)).val : ℕ) : ZMod (2 ^ a)) = (u : ZMod (2 ^ a)) :=
        ZMod.natCast_zmod_val _
      have hcop : Nat.Coprime (u : ZMod (2 ^ a)).val (2 ^ a) :=
        (ZMod.isUnit_iff_coprime _ _).mp (by rw [hval_cast]; exact u.isUnit)
      have hodd : Odd (u : ZMod (2 ^ a)).val :=
        Nat.coprime_two_right.mp (Nat.Coprime.coprime_dvd_right (dvd_pow_self 2 (by omega)) hcop)
      have hmul := odd_pow_mod_two_pow_pos ha hn hdvd hodd
      rw [hval_cast] at hmul ⊢
      have hinv : ((u⁻¹ : (ZMod (2 ^ a))ˣ) : ZMod (2 ^ a)) ^ 2 * (u : ZMod (2 ^ a)) ^ 2 = 1 := by
        rw [← mul_pow]
        norm_cast
        simp
      have heq : (u : ZMod (2 ^ a)) ^ (n - 2) =
          ((u⁻¹ : (ZMod (2 ^ a))ˣ) : ZMod (2 ^ a)) ^ 2 := by
        calc (u : ZMod (2 ^ a)) ^ (n - 2)
            = (u : ZMod (2 ^ a)) ^ (n - 2) * 1 := (mul_one _).symm
          _ = (u : ZMod (2 ^ a)) ^ (n - 2) *
                ((u : ZMod (2 ^ a)) ^ 2 * ((u⁻¹ : (ZMod (2 ^ a))ˣ) : ZMod (2 ^ a)) ^ 2) := by
              rw [mul_comm ((u : ZMod (2 ^ a)) ^ 2), hinv]
          _ = ((u : ZMod (2 ^ a)) ^ (n - 2) * (u : ZMod (2 ^ a)) ^ 2) *
                ((u⁻¹ : (ZMod (2 ^ a))ˣ) : ZMod (2 ^ a)) ^ 2 := by ring
          _ = 1 * ((u⁻¹ : (ZMod (2 ^ a))ˣ) : ZMod (2 ^ a)) ^ 2 := by rw [hmul]
          _ = ((u⁻¹ : (ZMod (2 ^ a))ˣ) : ZMod (2 ^ a)) ^ 2 := one_mul _
      exact heq.symm
  rw [hunit_eq, sum_units_inv_sq]
  -- Reindex (ZMod (2^a))ˣ to j ∈ range (2^(a-1)) via j ↦ 2*j + 1
  symm
  refine Finset.sum_nbij'
    (fun j => if hj : Nat.Coprime (2 * j + 1) (2 ^ a) then ZMod.unitOfCoprime (2 * j + 1) hj else 1)
    (fun u : (ZMod (2 ^ a))ˣ => (u : ZMod (2 ^ a)).val / 2)
    ?_ ?_ ?_ ?_ ?_
  · intro j _
    exact Finset.mem_univ _
  · intro u _
    rw [Finset.mem_range]
    have hlt : (u : ZMod (2 ^ a)).val < 2 ^ a := ZMod.val_lt _
    have hpow : 2 ^ a = 2 * 2 ^ (a - 1) := by
      conv_lhs => rw [show a = (a - 1) + 1 by omega, pow_succ']
    omega
  · intro j hj
    rw [Finset.mem_range] at hj
    have hcop : Nat.Coprime (2 * j + 1) (2 ^ a) :=
      (Nat.coprime_two_right.mpr ⟨j, rfl⟩).pow_right a
    rw [dif_pos hcop]
    have hpow : 2 ^ a = 2 * 2 ^ (a - 1) := by
      conv_lhs => rw [show a = (a - 1) + 1 by omega, pow_succ']
    have hlt : 2 * j + 1 < 2 ^ a := by omega
    rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast_of_lt hlt]
    omega
  · intro u _
    have hcop_u : Nat.Coprime (u : ZMod (2 ^ a)).val (2 ^ a) :=
      (ZMod.isUnit_iff_coprime _ _).mp (by rw [ZMod.natCast_zmod_val]; exact u.isUnit)
    have hodd_u : (u : ZMod (2 ^ a)).val % 2 = 1 :=
      Nat.odd_iff.mp (Nat.coprime_two_right.mp
        (Nat.Coprime.coprime_dvd_right (dvd_pow_self 2 (by omega)) hcop_u))
    have hval_eq : 2 * ((u : ZMod (2 ^ a)).val / 2) + 1 = (u : ZMod (2 ^ a)).val := by omega
    have hcop' : Nat.Coprime (2 * ((u : ZMod (2 ^ a)).val / 2) + 1) (2 ^ a) := by
      rw [hval_eq]; exact hcop_u
    rw [dif_pos hcop']
    ext
    simp [ZMod.coe_unitOfCoprime, hval_eq]
  · intro j _
    have hcop : Nat.Coprime (2 * j + 1) (2 ^ a) :=
      (Nat.coprime_two_right.mpr ⟨j, rfl⟩).pow_right a
    rw [dif_pos hcop]
    simp [ZMod.coe_unitOfCoprime]

private lemma sum_mul_period {M k e : ℕ} :
    ∑ i ∈ range (k * M), (i : ZMod M) ^ e =
      (k : ZMod M) * ∑ i ∈ range M, (i : ZMod M) ^ e := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih]
    have hper : ∑ x ∈ range M, ((k * M + x : ℕ) : ZMod M) ^ e =
        ∑ x ∈ range M, (x : ZMod M) ^ e := by
      refine Finset.sum_congr rfl fun x _ => ?_
      push_cast
      simp
    rw [hper, Nat.cast_succ, add_mul, one_mul]

end OeisA284760R1H2Proof

theorem OMA.solution : OMA.R_oeis_a284760_R1.H2 := by
  intro n hn h4
  obtain ⟨a, b, hb_odd, hn_eq⟩ := Nat.exists_eq_two_pow_mul_odd hn.ne'
  have ha2 : 2 ≤ a := by
    by_contra hlt
    have ha_le : a ≤ 1 := by omega
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp ha_le with rfl | rfl
    · simp at hn_eq
      obtain ⟨c, hc⟩ := h4
      obtain ⟨k, hk⟩ := hb_odd
      omega
    · simp at hn_eq
      obtain ⟨c, hc⟩ := h4
      obtain ⟨k, hk⟩ := hb_odd
      omega
  have hdvd2a : 2 ^ a ∣ n := ⟨b, hn_eq⟩
  intro hmod
  have hdvd_n4 : n ^ 4 ∣ ∑ i ∈ Finset.Ico 1 n, i ^ (n - 2) := Nat.dvd_of_mod_eq_zero hmod
  have hdvd_2a : 2 ^ a ∣ ∑ i ∈ Finset.Ico 1 n, i ^ (n - 2) :=
    dvd_trans hdvd2a (dvd_trans (dvd_pow_self n (by decide)) hdvd_n4)
  have hzero : ((∑ i ∈ Finset.Ico 1 n, i ^ (n - 2) : ℕ) : ZMod (2 ^ a)) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr hdvd_2a
  have hico_eq : ∑ i ∈ Finset.Ico 1 n, i ^ (n - 2) = ∑ i ∈ Finset.range n, i ^ (n - 2) := by
    have hn1 : 1 ≤ n := hn
    have h0 : 0 ^ (n - 2) = 0 := by
      have h4le : 4 ≤ n := Nat.le_of_dvd hn h4
      exact zero_pow (by omega)
    rw [← Finset.sum_range_add_sum_Ico _ hn1, Finset.sum_range_one, h0, zero_add]
  rw [hico_eq, Nat.cast_sum] at hzero
  have hcast : ∑ i ∈ Finset.range n, ((i ^ (n - 2) : ℕ) : ZMod (2 ^ a)) =
      ∑ i ∈ Finset.range (b * 2 ^ a), (i : ZMod (2 ^ a)) ^ (n - 2) := by
    rw [show n = b * 2 ^ a by rw [hn_eq, mul_comm]]
    refine Finset.sum_congr rfl fun i _ => by push_cast; rfl
  rw [hcast, OeisA284760R1H2Proof.sum_mul_period,
    OeisA284760R1H2Proof.sum_range_pow_mod_two_pow ha2 hn hdvd2a] at hzero
  have hmul3 : (3 : ZMod (2 ^ a)) * ((b : ZMod (2 ^ a)) *
      ∑ j ∈ Finset.range (2 ^ (a - 1)), ((2 * j + 1 : ℕ) : ZMod (2 ^ a)) ^ 2) = 0 := by
    rw [hzero, mul_zero]
  have hsum_nat :
      (3 : ZMod (2 ^ a)) *
        ∑ j ∈ Finset.range (2 ^ (a - 1)), ((2 * j + 1 : ℕ) : ZMod (2 ^ a)) ^ 2 =
        ((2 ^ (a - 1) * (4 * (2 ^ (a - 1)) ^ 2 - 1) : ℕ) : ZMod (2 ^ a)) := by
    have h := congrArg (Nat.cast : ℕ → ZMod (2 ^ a))
      (OeisA284760R1H2Proof.three_mul_sum_odd_sq (2 ^ (a - 1)))
    simpa only [Nat.cast_mul, Nat.cast_sum, Nat.cast_pow, Nat.cast_ofNat] using h
  have hzero2 : ((b * (2 ^ (a - 1) * (4 * (2 ^ (a - 1)) ^ 2 - 1)) : ℕ) : ZMod (2 ^ a)) = 0 := by
    rw [Nat.cast_mul, ← hsum_nat]
    linear_combination hmul3
  have hdvd_fin : 2 ^ a ∣ b * (2 ^ (a - 1) * (4 * (2 ^ (a - 1)) ^ 2 - 1)) :=
    (ZMod.natCast_eq_zero_iff _ _).mp hzero2
  have hrew : b * (2 ^ (a - 1) * (4 * (2 ^ (a - 1)) ^ 2 - 1)) =
      2 ^ (a - 1) * (b * (4 * (2 ^ (a - 1)) ^ 2 - 1)) := by ring
  rw [hrew] at hdvd_fin
  have hpow_split : 2 ^ a = 2 ^ (a - 1) * 2 := by
    conv_lhs => rw [show a = (a - 1) + 1 by omega, pow_succ]
  rw [hpow_split] at hdvd_fin
  have h2dvd : 2 ∣ b * (4 * (2 ^ (a - 1)) ^ 2 - 1) :=
    (mul_dvd_mul_iff_left (pow_ne_zero (a - 1) (by decide))).mp hdvd_fin
  have hodd_fac : Odd (4 * (2 ^ (a - 1)) ^ 2 - 1) := by
    have hpos : 1 ≤ (2 ^ (a - 1)) ^ 2 := Nat.one_le_pow 2 _ (pow_pos (by decide) _)
    refine ⟨2 * (2 ^ (a - 1)) ^ 2 - 1, ?_⟩
    omega
  have hodd_prod : Odd (b * (4 * (2 ^ (a - 1)) ^ 2 - 1)) := hb_odd.mul hodd_fac
  exact Nat.not_even_iff_odd.mpr hodd_prod (even_iff_two_dvd.mpr h2dvd)
