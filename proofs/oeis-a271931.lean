import OMAStatements.S_oeis_a271931
import Mathlib

namespace OMA.S_oeis_a271931

open PowerSeries BigOperators

private lemma coeff_lt_pow_zero {R : Type*} [CommRing R] {F : PowerSeries R} {d : ℕ}
    (hF : ∀ j < d, PowerSeries.coeff j F = 0) :
    ∀ (k j : ℕ), j < k * d → PowerSeries.coeff j (F ^ k) = 0 := by
  intro k
  induction k with
  | zero => intro j hj; omega
  | succ k ih =>
      intro j hj
      rw [pow_succ, PowerSeries.coeff_mul,
          Finset.Nat.sum_antidiagonal_eq_sum_range_succ
            (fun a b => PowerSeries.coeff a (F ^ k) * PowerSeries.coeff b F)]
      refine Finset.sum_eq_zero fun a ha => ?_
      have haj : a ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
      by_cases hlt : a < k * d
      · rw [ih a hlt, zero_mul]
      · have hbd : j - a < d := by
          have h1 : a + (j - a) = j := Nat.add_sub_of_le haj
          nlinarith
        rw [hF (j - a) hbd, mul_zero]

private lemma coeff_self_pow_of_order_one {R : Type*} [CommRing R] {F : PowerSeries R}
    (h0 : PowerSeries.coeff 0 F = 0) :
    ∀ k : ℕ, PowerSeries.coeff k (F ^ k) = (PowerSeries.coeff 1 F) ^ k := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, pow_succ, PowerSeries.coeff_mul,
          Finset.Nat.sum_antidiagonal_eq_sum_range_succ
            (fun a b => PowerSeries.coeff a (F ^ k) * PowerSeries.coeff b F)]
      rw [Finset.sum_eq_single k]
      · rw [ih, Nat.add_sub_cancel_left]
      · intro a ha hne
        have hak : a ≤ k + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
        by_cases hlt : a < k
        · have hF1 : ∀ j < 1, PowerSeries.coeff j F = 0 := fun j hj => by
            have : j = 0 := by omega
            subst this; exact h0
          rw [coeff_lt_pow_zero hF1 k a (by simpa using hlt), zero_mul]
        · have haeq : a = k + 1 := by omega
          rw [haeq, Nat.sub_self, h0, mul_zero]
      · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h

private lemma coeff_pow_congr_of_order_one {R : Type*} [CommRing R] {F₁ F₂ : PowerSeries R} {n : ℕ}
    (h0₁ : PowerSeries.coeff 0 F₁ = 0) (h0₂ : PowerSeries.coeff 0 F₂ = 0)
    (hagree : ∀ j < n, PowerSeries.coeff j F₁ = PowerSeries.coeff j F₂) :
    ∀ (k j : ℕ), j + 1 < k + n → PowerSeries.coeff j (F₁ ^ k) = PowerSeries.coeff j (F₂ ^ k) := by
  intro k
  induction k with
  | zero => intro j _; rw [pow_zero, pow_zero]
  | succ k ih =>
      intro j hj
      rw [pow_succ, pow_succ, PowerSeries.coeff_mul, PowerSeries.coeff_mul,
          Finset.Nat.sum_antidiagonal_eq_sum_range_succ
            (fun a b => PowerSeries.coeff a (F₁ ^ k) * PowerSeries.coeff b F₁),
          Finset.Nat.sum_antidiagonal_eq_sum_range_succ
            (fun a b => PowerSeries.coeff a (F₂ ^ k) * PowerSeries.coeff b F₂)]
      refine Finset.sum_congr rfl fun a ha => ?_
      have haj : a ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
      by_cases hlt : a < k
      · have h1 : ∀ r < 1, PowerSeries.coeff r F₁ = 0 := fun r hr => by
          have : r = 0 := by omega
          subst this; exact h0₁
        have h2 : ∀ r < 1, PowerSeries.coeff r F₂ = 0 := fun r hr => by
          have : r = 0 := by omega
          subst this; exact h0₂
        rw [coeff_lt_pow_zero h1 k a (by simpa using hlt),
            coeff_lt_pow_zero h2 k a (by simpa using hlt), zero_mul, zero_mul]
      · by_cases hja : j = a
        · rw [hja, Nat.sub_self, h0₁, h0₂, mul_zero, mul_zero]
        · rw [ih a (by omega), hagree (j - a) (by omega)]

private lemma coeff_pow_congr_general {R : Type*} [CommRing R] {U₁ U₂ : PowerSeries R} {m : ℕ}
    (hagree : ∀ j ≤ m, PowerSeries.coeff j U₁ = PowerSeries.coeff j U₂) :
    ∀ (k j : ℕ), j ≤ m → PowerSeries.coeff j (U₁ ^ k) = PowerSeries.coeff j (U₂ ^ k) := by
  intro k
  induction k with
  | zero => intro j _; rw [pow_zero, pow_zero]
  | succ k ih =>
      intro j hj
      rw [pow_succ, pow_succ, PowerSeries.coeff_mul, PowerSeries.coeff_mul,
          Finset.Nat.sum_antidiagonal_eq_sum_range_succ
            (fun a b => PowerSeries.coeff a (U₁ ^ k) * PowerSeries.coeff b U₁),
          Finset.Nat.sum_antidiagonal_eq_sum_range_succ
            (fun a b => PowerSeries.coeff a (U₂ ^ k) * PowerSeries.coeff b U₂)]
      refine Finset.sum_congr rfl fun a ha => ?_
      have haj : a ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
      rw [ih a (by omega), hagree (j - a) (by omega)]

/-- Key perturbation identity: if `F₁, F₂` have `coeff 0 = 0`, `coeff 1 F₁ = 1`, agree below `n ≥ 2`,
and `coeff n F₁ = 0`, then `coeff (p + n - 1) (F₂ ^ p) = coeff (p + n - 1) (F₁ ^ p) + p * coeff n F₂`. -/
private lemma coeff_pow_add_linear {p n : ℕ} (hp : 2 ≤ p) (hn : 2 ≤ n)
    {F₁ F₂ : PowerSeries ℤ}
    (h0₁ : PowerSeries.coeff 0 F₁ = 0) (h1₁ : PowerSeries.coeff 1 F₁ = 1)
    (hagree : ∀ j < n, PowerSeries.coeff j F₁ = PowerSeries.coeff j F₂)
    (hn₁ : PowerSeries.coeff n F₁ = 0) :
    PowerSeries.coeff (p + n - 1) (F₂ ^ p) =
      PowerSeries.coeff (p + n - 1) (F₁ ^ p) + (p : ℤ) * PowerSeries.coeff n F₂ := by
  set R := F₂ - F₁
  have hF2 : F₂ = F₁ + R := by simp [R]
  have hR_lt : ∀ j < n, PowerSeries.coeff j R = 0 := fun j hj => by
    simp [R, hagree j hj]
  have hRn : PowerSeries.coeff n R = PowerSeries.coeff n F₂ := by
    simp [R, hn₁]
  conv_lhs => rw [hF2, add_comm F₁ R]
  rw [add_pow, map_sum]
  have hrange : Finset.range (p + 1) = insert 0 (insert 1 ((Finset.range (p + 1)).erase 0 |>.erase 1)) := by
    ext x; simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_range]; omega
  rw [hrange, Finset.sum_insert (by simp), Finset.sum_insert (by simp)]
  have hrest : ∑ i ∈ ((Finset.range (p + 1)).erase 0).erase 1,
      PowerSeries.coeff (p + n - 1) (R ^ i * F₁ ^ (p - i) * ((Nat.choose p i : ℕ) : PowerSeries ℤ)) = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    simp only [Finset.mem_erase, Finset.mem_range] at hi
    have hi2 : 2 ≤ i := by omega
    rw [show ((Nat.choose p i : ℕ) : PowerSeries ℤ) = PowerSeries.C ((Nat.choose p i : ℕ) : ℤ) by
      rw [map_natCast], mul_comm (R ^ i * F₁ ^ (p - i)), PowerSeries.coeff_C_mul]
    have hmul0 : PowerSeries.coeff (p + n - 1) (R ^ i * F₁ ^ (p - i)) = 0 := by
      rw [PowerSeries.coeff_mul,
          Finset.Nat.sum_antidiagonal_eq_sum_range_succ
            (fun a b => PowerSeries.coeff a (R ^ i) * PowerSeries.coeff b (F₁ ^ (p - i)))]
      refine Finset.sum_eq_zero fun a ha => ?_
      have ha_le : a ≤ p + n - 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
      by_cases hlt : a < i * n
      · rw [coeff_lt_pow_zero hR_lt i a hlt, zero_mul]
      · have hF1_ord : ∀ j < 1, PowerSeries.coeff j F₁ = 0 := fun j hj => by
          have : j = 0 := by omega
          subst this; exact h0₁
        have hlt2 : p + n - 1 - a < (p - i) * 1 := by
          have h1 : i + n ≤ i * n := by nlinarith
          have h2 : i * n ≤ a := not_lt.mp hlt
          have hi_le : i ≤ p := by omega
          omega
        rw [coeff_lt_pow_zero hF1_ord (p - i) (p + n - 1 - a) hlt2, mul_zero]
    rw [hmul0, mul_zero]
  rw [hrest, add_zero]
  simp only [pow_zero, Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one, one_mul, mul_one,
      pow_one, Nat.choose_one_right]
  congr 1
  rw [show ((p : ℕ) : PowerSeries ℤ) = PowerSeries.C (p : ℤ) by rw [map_natCast],
      mul_comm (R * F₁ ^ (p - 1)), PowerSeries.coeff_C_mul]
  congr 1
  rw [PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun a b => PowerSeries.coeff a R * PowerSeries.coeff b (F₁ ^ (p - 1)))]
  rw [Finset.sum_eq_single n]
  · rw [hRn, show p + n - 1 - n = p - 1 by omega, coeff_self_pow_of_order_one h0₁, h1₁, one_pow, mul_one]
  · intro a ha hne
    have ha_le : a ≤ p + n - 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
    by_cases hlt : a < n
    · rw [hR_lt a hlt, zero_mul]
    · have hF1_ord : ∀ j < 1, PowerSeries.coeff j F₁ = 0 := fun j hj => by
        have : j = 0 := by omega
        subst this; exact h0₁
      rw [coeff_lt_pow_zero hF1_ord (p - 1) (p + n - 1 - a) (by omega), mul_zero]
  · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h

/-- Freshman's dream modulo `p` for integer power series:
`(p : ℤ) ∣ (coeff m (compSeries F (X^p + p * X * F^p)) - coeff m (F ^ p))` whenever `coeff 0 F = 0`. -/
private lemma prime_dvd_comp_sub_pow {p : ℕ} (hp : p.Prime)
    (F : PowerSeries ℤ) (m : ℕ) :
    (p : ℤ) ∣
      (PowerSeries.coeff m (compSeries F (PowerSeries.X ^ p + PowerSeries.C (p : ℤ) * PowerSeries.X * F ^ p)) -
        PowerSeries.coeff m (F ^ p)) := by
  have : Fact p.Prime := ⟨hp⟩
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub]
  set φ : ℤ →+* ZMod p := Int.castRingHom (ZMod p)
  set Fp : PowerSeries (ZMod p) := PowerSeries.map φ F
  set U : PowerSeries ℤ := PowerSeries.X ^ p + PowerSeries.C (p : ℤ) * PowerSeries.X * F ^ p
  have hUp : PowerSeries.map φ U = PowerSeries.X ^ p := by
    simp only [U, map_add, map_mul, map_pow, PowerSeries.map_X, PowerSeries.map_C]
    have hp0 : φ (p : ℤ) = 0 := by simp [φ]
    rw [hp0, map_zero, zero_mul, zero_mul, add_zero]
  have hlhs : ((PowerSeries.coeff m (compSeries F U) : ℤ) : ZMod p) =
      if p ∣ m then PowerSeries.coeff (m / p) Fp else 0 := by
    rw [compSeries, PowerSeries.coeff_mk, Int.cast_sum]
    have hterm : ∀ k ∈ Finset.range (m + 1),
        ((PowerSeries.coeff k F * PowerSeries.coeff m (U ^ k) : ℤ) : ZMod p) =
        if m = p * k then PowerSeries.coeff k Fp else 0 := by
      intro k _
      rw [Int.cast_mul]
      have h1 : ((PowerSeries.coeff k F : ℤ) : ZMod p) = PowerSeries.coeff k Fp := by
        simp [Fp, φ]
      have h2 : ((PowerSeries.coeff m (U ^ k) : ℤ) : ZMod p) = PowerSeries.coeff m (PowerSeries.X ^ (p * k)) := by
        have := PowerSeries.coeff_map φ m (U ^ k)
        rw [map_pow, hUp, ← pow_mul] at this
        simpa [φ] using this.symm
      rw [h1, h2, PowerSeries.coeff_X_pow]
      split_ifs <;> simp
    rw [Finset.sum_congr rfl hterm]
    by_cases hdiv : p ∣ m
    · rw [if_pos hdiv]
      obtain ⟨q, rfl⟩ := hdiv
      rw [Nat.mul_div_cancel_left q hp.pos, Finset.sum_eq_single q]
      · simp
      · intro k _ hne; rw [if_neg (fun h => hne (Nat.mul_left_cancel hp.pos h).symm)]
      · intro h; exact absurd (Finset.mem_range.mpr (by nlinarith [hp.pos])) h
    · rw [if_neg hdiv]
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [if_neg (fun h => hdiv ⟨k, h⟩)]
  have hrhs : ((PowerSeries.coeff m (F ^ p) : ℤ) : ZMod p) =
      if p ∣ m then PowerSeries.coeff (m / p) Fp else 0 := by
    have hmap : ((PowerSeries.coeff m (F ^ p) : ℤ) : ZMod p) = PowerSeries.coeff m (Fp ^ p) := by
      have := PowerSeries.coeff_map φ m (F ^ p)
      rw [map_pow] at this
      simpa [Fp, φ] using this.symm
    rw [hmap]
    -- Truncate `Fp` to a polynomial of degree `≤ m`:
    let P : Polynomial (ZMod p) := ∑ j ∈ Finset.range (m + 1), Polynomial.C (PowerSeries.coeff j Fp) * Polynomial.X ^ j
    have hP_agree : ∀ j ≤ m, PowerSeries.coeff j (P : PowerSeries (ZMod p)) = PowerSeries.coeff j Fp := by
      intro j hj
      rw [Polynomial.coeff_coe]
      simp only [P, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
          mul_ite, mul_one, mul_zero]
      rw [Finset.sum_ite_eq, if_pos (Finset.mem_range.mpr (by omega))]
    have hpow_eq : PowerSeries.coeff m (Fp ^ p) = PowerSeries.coeff m ((P : PowerSeries (ZMod p)) ^ p) :=
      coeff_pow_congr_general (fun j hj => (hP_agree j hj).symm) p m (le_refl m)
    rw [hpow_eq, ← Polynomial.coe_pow, Polynomial.coeff_coe]
    have hP_frob : P ^ p = ∑ j ∈ Finset.range (m + 1), Polynomial.C (PowerSeries.coeff j Fp) * Polynomial.X ^ (p * j) := by
      simp only [P]
      rw [← frobenius_def, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [frobenius_def, mul_pow, ← map_pow, ZMod.pow_card, ← pow_mul, mul_comm j p]
    rw [hP_frob, Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero]
    by_cases hdiv : p ∣ m
    · rw [if_pos hdiv]
      obtain ⟨q, rfl⟩ := hdiv
      rw [Nat.mul_div_cancel_left q hp.pos, Finset.sum_eq_single q]
      · simp
      · intro j _ hne; rw [if_neg (fun h => hne (Nat.mul_left_cancel hp.pos h).symm)]
      · intro h; exact absurd (Finset.mem_range.mpr (by nlinarith [hp.pos])) h
    · rw [if_neg hdiv]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [if_neg (fun h => hdiv ⟨j, h⟩)]
  rw [hlhs, hrhs, sub_self]

/-- Recursive integer coefficients `gCoeff p n` solving `G(x)^p = G(x^p + p*x*G(x)^p)`. -/
private noncomputable def gCoeff (p : ℕ) : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 =>
      let Gprev : PowerSeries ℤ := PowerSeries.mk fun j => if j < n + 2 then gCoeff p j else 0
      let Uprev : PowerSeries ℤ := PowerSeries.X ^ p + PowerSeries.C (p : ℤ) * PowerSeries.X * Gprev ^ p
      (PowerSeries.coeff (p + (n + 2) - 1) (compSeries Gprev Uprev) -
        PowerSeries.coeff (p + (n + 2) - 1) (Gprev ^ p)) / (p : ℤ)

theorem main_proof :
    ∀ p : ℕ, p.Prime →
      ∃ G : PowerSeries ℤ,
        PowerSeries.coeff 0 G = 0 ∧
        PowerSeries.coeff 1 G = 1 ∧
        G ^ p = compSeries G (PowerSeries.X ^ p + PowerSeries.C (p : ℤ) * PowerSeries.X * G ^ p) := by
  intro p hp
  let G : PowerSeries ℤ := PowerSeries.mk (gCoeff p)
  set U : PowerSeries ℤ := PowerSeries.X ^ p + PowerSeries.C (p : ℤ) * PowerSeries.X * G ^ p
  have hG0 : PowerSeries.coeff 0 G = 0 := by simp [G, gCoeff]
  have hG1 : PowerSeries.coeff 1 G = 1 := by simp [G, gCoeff]
  have hG_ord : ∀ j < 1, PowerSeries.coeff j G = 0 := fun j hj => by
    have : j = 0 := by omega
    subst this; exact hG0
  have hU_ord : ∀ j < p, PowerSeries.coeff j U = 0 := by
    intro j hj
    simp only [U, map_add, PowerSeries.coeff_X_pow, if_neg (by omega : j ≠ p), zero_add,
        mul_assoc, PowerSeries.coeff_C_mul]
    cases j with
    | zero => rw [PowerSeries.coeff_zero_X_mul, mul_zero]
    | succ j =>
        rw [PowerSeries.coeff_succ_X_mul, coeff_lt_pow_zero hG_ord p j (by omega), mul_zero]
  have hUp_coeff : PowerSeries.coeff p U = 1 := by
    simp only [U, map_add, PowerSeries.coeff_X_pow, ↓reduceIte, mul_assoc, PowerSeries.coeff_C_mul]
    have hX0 : PowerSeries.coeff p (PowerSeries.X * G ^ p) = 0 := by
      have hp1 : p = (p - 1) + 1 := by have := hp.two_le; omega
      conv_lhs => rw [hp1]
      rw [PowerSeries.coeff_succ_X_mul, ← hp1, coeff_lt_pow_zero hG_ord p (p - 1) (by have := hp.pos; omega)]
    rw [hX0, mul_zero, add_zero]
  refine ⟨G, hG0, hG1, ?_⟩
  apply PowerSeries.ext; intro m
  by_cases hmp : m < p
  · rw [coeff_lt_pow_zero hG_ord p m (by simpa using hmp), compSeries, PowerSeries.coeff_mk]
    symm
    refine Finset.sum_eq_zero fun k _ => ?_
    cases k with
    | zero => rw [hG0, zero_mul]
    | succ k => rw [coeff_lt_pow_zero hU_ord (k + 1) m (by nlinarith [hp.pos]), mul_zero]
  · by_cases hmeq : m = p
    · subst hmeq
      rw [coeff_self_pow_of_order_one hG0, hG1, one_pow, compSeries, PowerSeries.coeff_mk]
      symm
      rw [Finset.sum_eq_single 1]
      · rw [hG1, pow_one, hUp_coeff, mul_one]
      · intro k _ hne
        cases k with
        | zero => rw [hG0, zero_mul]
        | succ k =>
            have hk1 : 1 ≤ k := by omega
            rw [coeff_lt_pow_zero hU_ord (k + 1) m (by nlinarith [hp.pos]), mul_zero]
      · intro h; exact absurd (Finset.mem_range.mpr (by have := hp.two_le; omega)) h
    · -- `m > p`: write `m = p + (n + 2) - 1` with `n = m - p - 1`!
      set n := m - p - 1
      have hm_eq : m = p + (n + 2) - 1 := by omega
      rw [hm_eq]
      let Gprev : PowerSeries ℤ := PowerSeries.mk fun j => if j < n + 2 then gCoeff p j else 0
      let Uprev : PowerSeries ℤ := PowerSeries.X ^ p + PowerSeries.C (p : ℤ) * PowerSeries.X * Gprev ^ p
      have hGprev0 : PowerSeries.coeff 0 Gprev = 0 := by simp [Gprev, gCoeff]
      have hGprev1 : PowerSeries.coeff 1 Gprev = 1 := by simp [Gprev, gCoeff]
      have hGprev_n : PowerSeries.coeff (n + 2) Gprev = 0 := by simp [Gprev]
      have hGprev_agree : ∀ j < n + 2, PowerSeries.coeff j Gprev = PowerSeries.coeff j G := fun j hj => by
        simp [Gprev, G, hj]
      have hGprev_ord : ∀ j < 1, PowerSeries.coeff j Gprev = 0 := fun j hj => by
        have : j = 0 := by omega
        subst this; exact hGprev0
      have hUprev_ord : ∀ j < p, PowerSeries.coeff j Uprev = 0 := by
        intro j hj
        simp only [Uprev, map_add, PowerSeries.coeff_X_pow, if_neg (by omega : j ≠ p), zero_add,
            mul_assoc, PowerSeries.coeff_C_mul]
        cases j with
        | zero => rw [PowerSeries.coeff_zero_X_mul, mul_zero]
        | succ j =>
            rw [PowerSeries.coeff_succ_X_mul, coeff_lt_pow_zero hGprev_ord p j (by omega), mul_zero]
      -- `Uprev` and `U` agree at all degrees `≤ p + (n + 2) - 1`!
      have hU_agree : ∀ j ≤ p + (n + 2) - 1, PowerSeries.coeff j Uprev = PowerSeries.coeff j U := by
        intro j hj
        simp only [Uprev, U, map_add, mul_assoc, PowerSeries.coeff_C_mul]
        congr 2
        cases j with
        | zero => rw [PowerSeries.coeff_zero_X_mul, PowerSeries.coeff_zero_X_mul]
        | succ j =>
            rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_succ_X_mul]
            exact coeff_pow_congr_of_order_one hGprev0 hG0 hGprev_agree p j (by omega)
      -- `compSeries Gprev Uprev` and `compSeries G U` agree at `p + (n + 2) - 1`!
      have hcomp_eq : PowerSeries.coeff (p + (n + 2) - 1) (compSeries Gprev Uprev) =
          PowerSeries.coeff (p + (n + 2) - 1) (compSeries G U) := by
        simp only [compSeries, PowerSeries.coeff_mk]
        refine Finset.sum_congr rfl fun k _ => ?_
        by_cases hk : k < n + 2
        · rw [hGprev_agree k hk, coeff_pow_congr_general hU_agree k _ (le_refl _)]
        · have hk2 : n + 2 ≤ k := not_lt.mp hk
          have hlt : p + (n + 2) - 1 < k * p := by
            have h1 : p + (n + 2) - 1 = p + n + 1 := by omega
            rw [h1]; nlinarith [hp.two_le]
          rw [coeff_lt_pow_zero hUprev_ord k _ hlt, coeff_lt_pow_zero hU_ord k _ hlt, mul_zero, mul_zero]
      -- Apply the perturbation identity + Freshman's dream divisibility!
      rw [coeff_pow_add_linear hp.two_le (by omega : 2 ≤ n + 2) hGprev0 hGprev1 hGprev_agree hGprev_n,
          ← hcomp_eq]
      have hGn : PowerSeries.coeff (n + 2) G =
          (PowerSeries.coeff (p + (n + 2) - 1) (compSeries Gprev Uprev) -
            PowerSeries.coeff (p + (n + 2) - 1) (Gprev ^ p)) / (p : ℤ) := by
        simp [G, gCoeff, Gprev, Uprev]
      rw [hGn]
      have hdvd := prime_dvd_comp_sub_pow hp Gprev (p + (n + 2) - 1)
      rw [Int.mul_ediv_cancel' hdvd]
      ring

end OMA.S_oeis_a271931

theorem OMA.solution : type_of% @OMA.S_oeis_a271931.main :=
  OMA.S_oeis_a271931.main_proof
