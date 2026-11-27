import OMAReductions.R_OeisA1818_conjecture2_R1_H2_R1_H2_R1
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic

/-!
Fourier eigenbasis for the normalized reciprocal-difference kernel in `ZMod (p^2)`.
-/

namespace OMA.Spectrum1818

open Finset

private lemma y_isUnit {m : ℕ} (hp : (2 * m + 1).Prime) (j : Fin (2 * m)) :
    IsUnit (((j.val + 1 : ℕ) : ZMod ((2 * m + 1) ^ 2)) ^ (2 * m + 1)) := by
  have hcop : Nat.Coprime (j.val + 1) ((2 * m + 1) ^ 2) := by
    refine Nat.Coprime.pow_right 2 ?_
    exact (hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (Nat.succ_pos _) (by omega))).symm
  exact ((ZMod.isUnit_iff_coprime (j.val + 1) ((2 * m + 1) ^ 2)).mpr hcop).pow _

private lemma y_pow {m : ℕ} (hp : (2 * m + 1).Prime) (j : Fin (2 * m)) :
    (((j.val + 1 : ℕ) : ZMod ((2 * m + 1) ^ 2)) ^ (2 * m + 1)) ^ (2 * m) = 1 := by
  let p := 2 * m + 1
  have hcop : Nat.Coprime (j.val + 1) (p ^ 2) := by
    refine Nat.Coprime.pow_right 2 ?_
    exact (hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (Nat.succ_pos _) (by omega))).symm
  have htot : (p ^ 2).totient = p * (2 * m) := by
    rw [Nat.totient_prime_pow hp (by omega)]
    simp [p]
  rw [← pow_mul, ← htot]
  have h := congrArg Units.val (ZMod.pow_totient (ZMod.unitOfCoprime (j.val + 1) hcop))
  simpa [ZMod.coe_unitOfCoprime] using h

private lemma y_sub_isUnit {m : ℕ} (hp : (2 * m + 1).Prime) {i j : Fin (2 * m)} (hij : i ≠ j) :
    IsUnit ((((i.val + 1 : ℕ) : ZMod ((2 * m + 1) ^ 2)) ^ (2 * m + 1)) -
      (((j.val + 1 : ℕ) : ZMod ((2 * m + 1) ^ 2)) ^ (2 * m + 1))) := by
  let p := 2 * m + 1
  haveI : Fact p.Prime := ⟨hp⟩
  let z : ZMod (p ^ 2) :=
    (((i.val + 1 : ℕ) : ZMod (p ^ 2)) ^ p) - (((j.val + 1 : ℕ) : ZMod (p ^ 2)) ^ p)
  change IsUnit z
  rw [← ZMod.natCast_zmod_val z, ZMod.isUnit_iff_coprime]
  refine Nat.Coprime.pow_right 2 ?_
  refine (hp.coprime_iff_not_dvd.mpr ?_).symm
  intro hdvd
  have hcast0 : (ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p)) z = 0 := by
    rw [← ZMod.natCast_zmod_val z]
    simp only [map_natCast]
    exact (ZMod.natCast_eq_zero_iff z.val p).mpr hdvd
  have hcast : (ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p)) z =
      ((i.val + 1 : ℕ) : ZMod p) - ((j.val + 1 : ℕ) : ZMod p) := by
    simp only [z, map_sub, map_pow, map_natCast, ZMod.pow_card]
  rw [hcast, sub_eq_zero] at hcast0
  have hmod : i.val + 1 ≡ j.val + 1 [MOD p] := (ZMod.natCast_eq_natCast_iff _ _ p).mp hcast0
  have hi : i.val + 1 < p := by omega
  have hj : j.val + 1 < p := by omega
  rw [Nat.ModEq, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at hmod
  exact hij (Fin.ext (by omega))

private lemma unit_of_cast_ne_zero {p : ℕ} (hp : p.Prime) {z : ZMod (p ^ 2)}
    (hz : ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p) z ≠ 0) : IsUnit z := by
  haveI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  rw [← ZMod.natCast_zmod_val z, ZMod.isUnit_iff_coprime]
  refine Nat.Coprime.pow_right 2 ?_
  refine (hp.coprime_iff_not_dvd.mpr ?_).symm
  intro hdvd
  apply hz
  rw [← ZMod.natCast_zmod_val z]
  simp only [map_natCast]
  exact (ZMod.natCast_eq_zero_iff z.val p).mpr hdvd

private lemma pow_p_eq_of_cast_eq {p : ℕ} (hp : p.Prime) {a b : ZMod (p ^ 2)}
    (h : ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p) a =
         ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p) b) :
    a ^ p = b ^ p := by
  haveI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hdvd : p ∣ (b - a).val := by
    rw [← ZMod.natCast_eq_zero_iff]
    have h0 : ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p) (b - a) = 0 := by
      rw [map_sub, h, sub_self]
    rw [← ZMod.natCast_zmod_val (b - a), map_natCast] at h0
    exact h0
  obtain ⟨c, hc⟩ := hdvd
  have hba : b = a + (p : ZMod (p ^ 2)) * (c : ZMod (p ^ 2)) := by
    have h1 : b - a = ((b - a).val : ZMod (p ^ 2)) := (ZMod.natCast_zmod_val _).symm
    rw [hc, Nat.cast_mul] at h1
    calc b = (b - a) + a := by ring
      _ = a + (p : ZMod (p ^ 2)) * (c : ZMod (p ^ 2)) := by rw [h1]; ring
  rw [hba, add_pow]
  rw [Finset.sum_eq_single p]
  · simp
  · intro k hk hkp_ne
    have hkp : k ≤ p := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hklt : k < p := lt_of_le_of_ne hkp hkp_ne
    by_cases hk0 : k = 0
    · subst hk0
      have hp0 : (p : ZMod (p ^ 2)) ^ p = 0 := by
        have hd : p ^ 2 ∣ p ^ p := Nat.pow_dvd_pow p hp.two_le
        exact_mod_cast (ZMod.natCast_eq_zero_iff (p ^ p) (p ^ 2)).mpr hd
      simp [mul_pow, hp0]
    · have hch : p ∣ p.choose k := hp.dvd_choose_self hk0 hklt
      have hmul : (p : ZMod (p ^ 2)) ^ (p - k) * (p.choose k : ZMod (p ^ 2)) = 0 := by
        obtain ⟨q, hq⟩ := hch
        rw [hq, Nat.cast_mul]
        have hpow : (p : ZMod (p ^ 2)) ^ (p - k) =
            (p : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)) ^ (p - k - 1) := by
          rw [← pow_succ', Nat.sub_add_cancel (by omega)]
        rw [hpow]
        have hp2 : (p : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)) = 0 := by
          have : ((p * p : ℕ) : ZMod (p ^ 2)) = 0 :=
            (ZMod.natCast_eq_zero_iff (p * p) (p ^ 2)).mpr (by rw [sq])
          simpa [Nat.cast_mul] using this
        calc (p : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)) ^ (p - k - 1) * ((p : ZMod (p ^ 2)) * (q : ZMod (p ^ 2)))
            = ((p : ZMod (p ^ 2)) * (p : ZMod (p ^ 2))) * ((p : ZMod (p ^ 2)) ^ (p - k - 1) * (q : ZMod (p ^ 2))) := by ring
          _ = 0 := by rw [hp2, zero_mul]
      calc a ^ k * ((p : ZMod (p ^ 2)) * (c : ZMod (p ^ 2))) ^ (p - k) * (p.choose k : ZMod (p ^ 2))
          = a ^ k * (c : ZMod (p ^ 2)) ^ (p - k) * ((p : ZMod (p ^ 2)) ^ (p - k) * (p.choose k : ZMod (p ^ 2))) := by ring
        _ = 0 := by rw [hmul, mul_zero]
  · intro hp_mem
    exfalso
    exact hp_mem (Finset.mem_range.mpr (Nat.lt_succ_self _))

theorem spectrum_1818 : OMA.R_OeisA1818_conjecture2_R1_H2_R1_H2_R1.H2 := by
  intro m hp
  let p := 2 * m + 1
  letI : Fact p.Prime := ⟨hp⟩
  let R := ZMod (p ^ 2)
  let y (i : Fin (2 * m)) : R := ((i.val + 1 : ℕ) : R) ^ p
  let B : Matrix (Fin (2 * m)) (Fin (2 * m)) R := fun i j =>
    if i = j then 0 else y i * (y i - y j)⁻¹
  let V : Matrix (Fin (2 * m)) (Fin (2 * m)) R := fun j i => (y j) ^ (i.val + 1)
  have hm_pos : 0 < 2 * m := by
    have := hp.two_le
    omega
  let zeroFin : Fin (2 * m) := ⟨0, hm_pos⟩
  have hy0 : y zeroFin = 1 := by simp [y, zeroFin]
  refine ⟨V, ?_, ?_⟩
  · -- IsUnit V.det
    have hV : V = Matrix.diagonal y * Matrix.vandermonde y := by
      ext j i
      simp [V, Matrix.diagonal_mul, Matrix.vandermonde_apply, pow_succ']
    rw [hV, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_vandermonde]
    refine IsUnit.mul (IsUnit.prod _ fun j _ => y_isUnit hp j) ?_
    refine IsUnit.prod _ fun i _ => IsUnit.prod _ fun j hj => ?_
    exact y_sub_isUnit hp (Finset.mem_Ioi.mp hj).ne'
  · -- ((2 : R) • B) * V = V * Matrix.diagonal ...
    let castP := ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p)
    have hzero_val : ∀ i : Fin (2 * m), ((i.val + 1 : ℕ) : ZMod p) ≠ 0 := by
      intro i h
      have hd : p ∣ i.val + 1 := (ZMod.natCast_eq_zero_iff (i.val + 1) p).mp h
      exact Nat.not_dvd_of_pos_of_lt (Nat.succ_pos _) (by omega) hd
    let mulIdx (j l : Fin (2 * m)) : Fin (2 * m) :=
      ⟨(((l.val + 1 : ℕ) : ZMod p) * ((j.val + 1 : ℕ) : ZMod p)⁻¹).val - 1, by
        have hne : ((l.val + 1 : ℕ) : ZMod p) * ((j.val + 1 : ℕ) : ZMod p)⁻¹ ≠ 0 :=
          mul_ne_zero (hzero_val l) (inv_ne_zero (hzero_val j))
        have hpos : 0 < (((l.val + 1 : ℕ) : ZMod p) * ((j.val + 1 : ℕ) : ZMod p)⁻¹).val :=
          Nat.pos_of_ne_zero fun h => hne (by rw [← ZMod.natCast_zmod_val (((l.val + 1 : ℕ) : ZMod p) * ((j.val + 1 : ℕ) : ZMod p)⁻¹), h]; rfl)
        have hlt := ZMod.val_lt (((l.val + 1 : ℕ) : ZMod p) * ((j.val + 1 : ℕ) : ZMod p)⁻¹)
        omega⟩
    have hmulIdx_cast (j l : Fin (2 * m)) :
        (((mulIdx j l).val + 1 : ℕ) : ZMod p) =
          ((l.val + 1 : ℕ) : ZMod p) * ((j.val + 1 : ℕ) : ZMod p)⁻¹ := by
      have hne : ((l.val + 1 : ℕ) : ZMod p) * ((j.val + 1 : ℕ) : ZMod p)⁻¹ ≠ 0 :=
        mul_ne_zero (hzero_val l) (inv_ne_zero (hzero_val j))
      have hpos : 0 < (((l.val + 1 : ℕ) : ZMod p) * ((j.val + 1 : ℕ) : ZMod p)⁻¹).val :=
        Nat.pos_of_ne_zero fun h => hne (by rw [← ZMod.natCast_zmod_val (((l.val + 1 : ℕ) : ZMod p) * ((j.val + 1 : ℕ) : ZMod p)⁻¹), h]; rfl)
      change ((((((l.val + 1 : ℕ) : ZMod p) * ((j.val + 1 : ℕ) : ZMod p)⁻¹).val - 1 + 1 : ℕ)) : ZMod p) = _
      rw [Nat.sub_add_cancel hpos, ZMod.natCast_zmod_val]
    have hmulIdx_inj (j : Fin (2 * m)) : Function.Injective (mulIdx j) := by
      intro l₁ l₂ h
      have hc := congrArg (fun x : Fin (2 * m) => ((x.val + 1 : ℕ) : ZMod p)) h
      rw [hmulIdx_cast, hmulIdx_cast] at hc
      have hinv : ((j.val + 1 : ℕ) : ZMod p)⁻¹ ≠ 0 := inv_ne_zero (hzero_val j)
      have heq := mul_right_cancel₀ hinv hc
      have hmod : l₁.val + 1 ≡ l₂.val + 1 [MOD p] := (ZMod.natCast_eq_natCast_iff _ _ p).mp heq
      rw [Nat.ModEq, Nat.mod_eq_of_lt (by omega : l₁.val + 1 < p),
        Nat.mod_eq_of_lt (by omega : l₂.val + 1 < p)] at hmod
      exact Fin.ext (by omega)
    have hmulIdx_bij (j : Fin (2 * m)) : Function.Bijective (mulIdx j) :=
      Fintype.bijective_iff_injective_and_card.mpr ⟨hmulIdx_inj j, rfl⟩
    have hmulIdx_self (j : Fin (2 * m)) : mulIdx j j = zeroFin := by
      apply Fin.ext
      have hc := hmulIdx_cast j j
      rw [mul_inv_cancel₀ (hzero_val j)] at hc
      have hmod : (mulIdx j j).val + 1 ≡ 1 [MOD p] := (ZMod.natCast_eq_natCast_iff _ _ p).mp hc
      rw [Nat.ModEq, Nat.mod_eq_of_lt (by omega : (mulIdx j j).val + 1 < p),
        Nat.mod_eq_of_lt (by omega : 1 < p)] at hmod
      omega
    have hy_mul (j l : Fin (2 * m)) : y (mulIdx j l) = y l * (y j)⁻¹ := by
      have hj_unit : IsUnit ((j.val + 1 : ℕ) : R) := by
        rw [ZMod.isUnit_iff_coprime]
        exact (Nat.Coprime.pow_right 2 (hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (Nat.succ_pos _) (by omega))).symm)
      have hb_inv : ((j.val + 1 : ℕ) : R) * ((j.val + 1 : ℕ) : R)⁻¹ = 1 :=
        ZMod.mul_inv_of_unit _ hj_unit
      have hcast_inv : castP (((j.val + 1 : ℕ) : R)⁻¹) = ((j.val + 1 : ℕ) : ZMod p)⁻¹ := by
        apply mul_left_cancel₀ (hzero_val j)
        rw [mul_inv_cancel₀ (hzero_val j), ← map_natCast castP, ← map_mul, hb_inv, map_one]
      have hcast_eq : castP (((mulIdx j l).val + 1 : ℕ) : R) =
          castP (((l.val + 1 : ℕ) : R) * ((j.val + 1 : ℕ) : R)⁻¹) := by
        rw [map_natCast, hmulIdx_cast, map_mul, map_natCast, hcast_inv]
      have hpow_eq := pow_p_eq_of_cast_eq hp hcast_eq
      change y (mulIdx j l) = _
      dsimp [y]
      rw [hpow_eq, mul_pow]
      congr 1
      apply ZMod.inv_eq_of_mul_eq_one
      rw [← mul_pow, hb_inv, one_pow]
    have h1_sub_unit : ∀ r ∈ univ.erase zeroFin, IsUnit (1 - y r) := by
      intro r hr
      rw [← hy0]
      exact y_sub_isUnit hp (Finset.mem_erase.mp hr).1.symm
    let S (k : ℕ) : R := ∑ r ∈ univ.erase zeroFin, (1 - y r)⁻¹ * (y r) ^ k
    have hBV : ∀ j i : Fin (2 * m), (((2 : R) • B) * V) j i = V j i * (2 * S (i.val + 1)) := by
      intro j i
      rw [Matrix.mul_apply]
      simp only [B, V]
      have hsplit : ∑ l : Fin (2 * m), (2 * (if j = l then 0 else y j * (y j - y l)⁻¹)) * (y l) ^ (i.val + 1) =
          2 * ∑ l ∈ univ.erase j, y j * (y j - y l)⁻¹ * (y l) ^ (i.val + 1) := by
        rw [Finset.mul_sum]
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
        simp only [if_true, mul_zero, zero_mul, zero_add]
        apply Finset.sum_congr rfl
        intro l hl
        have hjl : j ≠ l := (Finset.mem_erase.mp hl).1.symm
        simp only [if_neg hjl]
        ring
      rw [hsplit]
      have hbij : ∑ l ∈ univ.erase j, y j * (y j - y l)⁻¹ * (y l) ^ (i.val + 1) =
          (y j) ^ (i.val + 1) * S (i.val + 1) := by
        rw [Finset.mul_sum]
        refine Finset.sum_bij (fun l _ => mulIdx j l) ?_ ?_ ?_ ?_
        · intro l hl
          rw [Finset.mem_erase]
          refine ⟨fun h => (Finset.mem_erase.mp hl).1 (hmulIdx_inj j (h.trans (hmulIdx_self j).symm)), Finset.mem_univ _⟩
        · intro l₁ _ l₂ _ h
          exact hmulIdx_inj j h
        · intro r hr
          obtain ⟨l, hl⟩ := (hmulIdx_bij j).surjective r
          refine ⟨l, Finset.mem_erase.mpr ⟨fun h => ?_, Finset.mem_univ _⟩, hl⟩
          rw [h, hmulIdx_self] at hl
          exact (Finset.mem_erase.mp hr).1 hl.symm
        · intro l hl
          have hr_mem : mulIdx j l ∈ univ.erase zeroFin :=
            Finset.mem_erase.mpr ⟨fun h => (Finset.mem_erase.mp hl).1 (hmulIdx_inj j (h.trans (hmulIdx_self j).symm)), Finset.mem_univ _⟩
          have hyj_u := y_isUnit hp j
          have hyj_inv : y j * (y j)⁻¹ = 1 := ZMod.mul_inv_of_unit _ hyj_u
          have hyl : y l = y j * y (mulIdx j l) := by
            rw [hy_mul, mul_comm (y l), ← mul_assoc, hyj_inv, one_mul]
          have hsub : (y j - y l)⁻¹ = (1 - y (mulIdx j l))⁻¹ * (y j)⁻¹ := by
            apply ZMod.inv_eq_of_mul_eq_one
            have h1u := h1_sub_unit _ hr_mem
            calc (y j - y l) * ((1 - y (mulIdx j l))⁻¹ * (y j)⁻¹)
                = (y j * (1 - y (mulIdx j l))) * ((1 - y (mulIdx j l))⁻¹ * (y j)⁻¹) := by rw [hyl]; ring
              _ = ((1 - y (mulIdx j l)) * (1 - y (mulIdx j l))⁻¹) * (y j * (y j)⁻¹) := by ring
              _ = 1 := by rw [ZMod.mul_inv_of_unit _ h1u, hyj_inv, mul_one]
          rw [hsub, hyl, mul_pow]
          calc y j * ((1 - y (mulIdx j l))⁻¹ * (y j)⁻¹) * ((y j) ^ (i.val + 1) * (y (mulIdx j l)) ^ (i.val + 1))
              = (y j * (y j)⁻¹) * ((y j) ^ (i.val + 1) * ((1 - y (mulIdx j l))⁻¹ * (y (mulIdx j l)) ^ (i.val + 1))) := by ring
            _ = (y j) ^ (i.val + 1) * ((1 - y (mulIdx j l))⁻¹ * (y (mulIdx j l)) ^ (i.val + 1)) := by rw [hyj_inv, one_mul]
      rw [hbij]
      ring
    -- Compute S(k+1) - S(k) and S(2m)
    have hS_step : ∀ k : ℕ, 1 ≤ k → k < 2 * m → S (k + 1) = S k + 1 := by
      intro k hk1 hk2
      have hdiff : S (k + 1) - S k = - ∑ r ∈ univ.erase zeroFin, (y r) ^ k := by
        dsimp [S]
        rw [← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro r hr
        have h1u := h1_sub_unit r hr
        calc (1 - y r)⁻¹ * (y r) ^ (k + 1) - (1 - y r)⁻¹ * (y r) ^ k
            = -((1 - y r) * (1 - y r)⁻¹) * (y r) ^ k := by rw [pow_succ']; ring
          _ = -((y r) ^ k) := by rw [ZMod.mul_inv_of_unit _ h1u, one_mul]
      obtain ⟨g, hg⟩ := IsCyclic.exists_monoid_generator (α := (ZMod p)ˣ)
      have hord : orderOf g = 2 * m := by
        rw [orderOf_eq_card_of_forall_mem_powers hg, ZMod.card_units_eq_totient, Nat.totient_prime hp]
        omega
      let r₀ : Fin (2 * m) := ⟨(g : ZMod p).val - 1, by
        have hpos : 0 < (g : ZMod p).val := Nat.pos_of_ne_zero fun h =>
          g.ne_zero (by rw [← ZMod.natCast_zmod_val (g : ZMod p), h]; rfl)
        have hlt := ZMod.val_lt (g : ZMod p)
        omega⟩
      have hr₀_cast : ((r₀.val + 1 : ℕ) : ZMod p) = (g : ZMod p) := by
        have hpos : 0 < (g : ZMod p).val := Nat.pos_of_ne_zero fun h =>
          g.ne_zero (by rw [← ZMod.natCast_zmod_val (g : ZMod p), h]; rfl)
        change (((g : ZMod p).val - 1 + 1 : ℕ) : ZMod p) = (g : ZMod p)
        rw [Nat.sub_add_cancel hpos, ZMod.natCast_zmod_val]
      have hgk_ne : (g : ZMod p) ^ k ≠ 1 := by
        intro h1
        have hdvd : orderOf g ∣ k := orderOf_dvd_of_pow_eq_one (Units.ext (by simpa using h1))
        rw [hord] at hdvd
        exact absurd (Nat.le_of_dvd hk1 hdvd) (not_le_of_gt hk2)
      have hunit_sub : IsUnit (1 - ((y r₀)⁻¹) ^ k) := by
        apply unit_of_cast_ne_zero hp
        have hyr₀_u := y_isUnit hp r₀
        have hyr₀_inv : y r₀ * (y r₀)⁻¹ = 1 := ZMod.mul_inv_of_unit _ hyr₀_u
        have hcast_y : castP (y r₀) = (g : ZMod p) := by
          simp only [y, map_pow, map_natCast, ZMod.pow_card, hr₀_cast]
        have hcast_inv : castP ((y r₀)⁻¹) = (g : ZMod p)⁻¹ := by
          apply mul_left_cancel₀ g.ne_zero
          rw [mul_inv_cancel₀ g.ne_zero, ← hcast_y, ← map_mul, hyr₀_inv, map_one]
        rw [map_sub, map_one, map_pow, hcast_inv, sub_ne_zero]
        intro h1
        exact hgk_ne (by
          have h2 : ((g : ZMod p)⁻¹) ^ k = (1 : ZMod p) := h1.symm
          calc (g : ZMod p) ^ k = (g : ZMod p) ^ k * ((g : ZMod p)⁻¹) ^ k := by rw [h2, mul_one]
            _ = ((g : ZMod p) * (g : ZMod p)⁻¹) ^ k := by rw [← mul_pow]
            _ = 1 := by rw [mul_inv_cancel₀ g.ne_zero, one_pow])
      have hsum_zero : ∑ r : Fin (2 * m), (y r) ^ k = 0 := by
        have hrot : ∑ r : Fin (2 * m), (y r) ^ k = ((y r₀)⁻¹) ^ k * ∑ r : Fin (2 * m), (y r) ^ k := by
          rw [Finset.mul_sum]
          refine Finset.sum_bij (fun l _ => mulIdx r₀ l) (fun _ _ => Finset.mem_univ _)
            (fun _ _ _ _ h => hmulIdx_inj r₀ h) (fun r _ => ⟨_, Finset.mem_univ _, (hmulIdx_bij r₀).surjective r |>.choose_spec⟩) ?_
          intro l _
          rw [hy_mul, mul_pow, mul_comm]
        have hmul0 : (1 - ((y r₀)⁻¹) ^ k) * ∑ r : Fin (2 * m), (y r) ^ k = 0 := by
          calc (1 - ((y r₀)⁻¹) ^ k) * ∑ r : Fin (2 * m), (y r) ^ k
              = ∑ r : Fin (2 * m), (y r) ^ k - ((y r₀)⁻¹) ^ k * ∑ r : Fin (2 * m), (y r) ^ k := by ring
            _ = 0 := sub_eq_zero.mpr hrot
        exact hunit_sub.mul_right_eq_zero.mp hmul0
      have hsum_erase : ∑ r ∈ univ.erase zeroFin, (y r) ^ k = -1 := by
        have h := Finset.add_sum_erase (univ : Finset (Fin (2 * m))) (fun r => (y r) ^ k) (Finset.mem_univ zeroFin)
        rw [hsum_zero, hy0, one_pow] at h
        linear_combination h
      rw [hsum_erase, neg_neg] at hdiff
      linear_combination hdiff
    have hS_top : 2 * S (2 * m) = (2 * m : R) - 1 := by
      have hpow_eq : S (2 * m) = S 0 := by
        dsimp [S]
        apply Finset.sum_congr rfl
        intro r _
        rw [y_pow hp r, pow_zero]
      rw [hpow_eq]
      dsimp [S]
      simp only [pow_zero, mul_one]
      let invIdx (r : Fin (2 * m)) : Fin (2 * m) := mulIdx r zeroFin
      have hinv_y (r : Fin (2 * m)) : y (invIdx r) = (y r)⁻¹ := by
        dsimp [invIdx]
        rw [hy_mul, hy0, one_mul]
      have hinv_inj : Function.Injective invIdx := by
        intro r₁ r₂ h
        have hy1 : (y r₁)⁻¹ = (y r₂)⁻¹ := by rw [← hinv_y r₁, ← hinv_y r₂, h]
        have hyr1 := y_isUnit hp r₁
        have hyr2 := y_isUnit hp r₂
        have hy_eq : y r₁ = y r₂ := by
          calc y r₁ = y r₁ * (y r₂ * (y r₂)⁻¹) := by rw [ZMod.mul_inv_of_unit _ hyr2, mul_one]
            _ = (y r₁ * (y r₁)⁻¹) * y r₂ := by rw [hy1]; ring
            _ = y r₂ := by rw [ZMod.mul_inv_of_unit _ hyr1, one_mul]
        by_contra hne
        have hsub := y_sub_isUnit hp hne
        change IsUnit (y r - y zeroFin) at hsub
        rw [hy_eq, sub_self] at hsub
        exact not_isUnit_zero hsub
      have hinv_mem : ∀ r ∈ univ.erase zeroFin, invIdx r ∈ univ.erase zeroFin := by
        intro r hr
        rw [Finset.mem_erase]
        refine ⟨fun h => ?_, Finset.mem_univ _⟩
        have h1 : (y r)⁻¹ = 1 := by rw [← hinv_y r, h, hy0]
        have h2 : y r = 1 := by
          calc y r = y r * (y r)⁻¹ := by rw [h1, mul_one]
            _ = 1 := ZMod.mul_inv_of_unit _ (y_isUnit hp r)
        have hne : r ≠ zeroFin := (Finset.mem_erase.mp hr).1
        have hsub := y_sub_isUnit hp hne
        change IsUnit (y r - y zeroFin) at hsub
        rw [h2, hy0, sub_self] at hsub
        exact not_isUnit_zero hsub
      have hsum_inv : ∑ r ∈ univ.erase zeroFin, (1 - y r)⁻¹ =
          ∑ r ∈ univ.erase zeroFin, (1 - (y r)⁻¹)⁻¹ := by
        refine Finset.sum_bij (fun r _ => invIdx r) hinv_mem (fun _ _ _ _ h => hinv_inj h) ?_ ?_
        · intro r hr
          have hbij : Function.Bijective invIdx :=
            Fintype.bijective_iff_injective_and_card.mpr ⟨hinv_inj, rfl⟩
          obtain ⟨a, ha⟩ := hbij.surjective r
          refine ⟨a, Finset.mem_erase.mpr ⟨fun ha0 => ?_, Finset.mem_univ _⟩, ha⟩
          have h1 : y r = 1 := by
            rw [← ha, hinv_y, ha0, hy0]
            exact ZMod.inv_eq_of_mul_eq_one _ (by rw [mul_one])
          have hsub := y_sub_isUnit hp (Finset.mem_erase.mp hr).1
          change IsUnit (y r - y zeroFin) at hsub
          rw [h1, hy0, sub_self] at hsub
          exact not_isUnit_zero hsub
        · intro r _
          rw [hinv_y]
      have hpair : ∀ r ∈ univ.erase zeroFin, (1 - y r)⁻¹ + (1 - (y r)⁻¹)⁻¹ = 1 := by
        intro r hr
        have hyu := y_isUnit hp r
        have hyi : y r * (y r)⁻¹ = 1 := ZMod.mul_inv_of_unit _ hyu
        have h1u := h1_sub_unit r hr
        have h1ui : IsUnit (1 - (y r)⁻¹) := by
          rw [← hinv_y r]
          exact h1_sub_unit _ (hinv_mem r hr)
        apply h1u.mul_left_cancel
        rw [mul_one, mul_add, ZMod.mul_inv_of_unit _ h1u]
        have hmul : (1 - y r) * (1 - (y r)⁻¹)⁻¹ = -y r := by
          have h1yr : 1 - y r = -y r * (1 - (y r)⁻¹) := by
            linear_combination -(y r) * hyi
          rw [h1yr, mul_assoc, mul_comm (1 - (y r)⁻¹), ZMod.mul_inv_of_unit _ h1ui, mul_one]
        rw [hmul]
        ring
      calc 2 * ∑ r ∈ univ.erase zeroFin, (1 - y r)⁻¹
          = ∑ r ∈ univ.erase zeroFin, (1 - y r)⁻¹ + ∑ r ∈ univ.erase zeroFin, (1 - (y r)⁻¹)⁻¹ := by
            rw [← hsum_inv, two_mul]
        _ = ∑ r ∈ univ.erase zeroFin, ((1 - y r)⁻¹ + (1 - (y r)⁻¹)⁻¹) := Finset.sum_add_distrib.symm
        _ = ∑ _r ∈ univ.erase zeroFin, (1 : R) := Finset.sum_congr rfl hpair
        _ = ((univ.erase zeroFin).card : R) := by simp
        _ = (2 * m : R) - 1 := by
            rw [Finset.card_erase_of_mem (Finset.mem_univ zeroFin), Finset.card_univ, Fintype.card_fin]
            rw [Nat.cast_sub hm_pos]
            simp only [Nat.cast_mul, Nat.cast_ofNat]
            ring
    have hS_val : ∀ k : ℕ, 1 ≤ k → k ≤ 2 * m → 2 * S k = 2 * (k : R) - 1 - 2 * m := by
      intro k hk1 hk2
      obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hk2
      induction d generalizing k with
      | zero =>
        have hk2m : k = 2 * m := by omega
        subst hk2m
        rw [hS_top]
        simp only [Nat.cast_mul, Nat.cast_ofNat]
        ring
      | succ d ih =>
        have hklt : k < 2 * m := by omega
        have hk1_le : 1 ≤ k + 1 := by omega
        have hk1_le2 : k + 1 ≤ 2 * m := by omega
        have ih' := ih (k + 1) hk1_le hk1_le2 (by omega)
        rw [hS_step k hk1 hklt] at ih'
        push_cast at ih'
        linear_combination ih'
    ext j i
    rw [hBV, Matrix.mul_diagonal]
    congr 1
    rw [hS_val (i.val + 1) (Nat.succ_pos _) i.isLt]
    push_cast
    ring

end OMA.Spectrum1818

theorem OMA.solution : OMA.R_OeisA1818_conjecture2_R1_H2_R1_H2_R1.H2 :=
  OMA.Spectrum1818.spectrum_1818
