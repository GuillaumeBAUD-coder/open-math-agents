import OMAStatements.S_oeis_a345652
import Mathlib

namespace OMA.P_oeis_a345652

-- 1. Hurwitz product, power, divided power, and exponential on ℕ → ℤ
private def hmul (f g : ℕ → ℤ) (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), (Nat.choose n k : ℤ) * f k * g (n - k)

private def hpow (f : ℕ → ℤ) : ℕ → ℕ → ℤ
  | 0, n => if n = 0 then 1 else 0
  | m + 1, n => hmul f (hpow f m) n

private def hdivpow (f : ℕ → ℤ) : ℕ → ℕ → ℤ
  | 0, n => if n = 0 then 1 else 0
  | _ + 1, 0 => 0
  | m + 1, n + 1 =>
      ∑ k ∈ Finset.range (n + 1),
        (Nat.choose n k : ℤ) * f (k + 1) * hdivpow f m (n - k)

private def hexp (f : ℕ → ℤ) (n : ℕ) : ℤ :=
  ∑ m ∈ Finset.range (n + 1), hdivpow f m n

private lemma hdivpow_gt (f : ℕ → ℤ) : ∀ m n : ℕ, n < m → hdivpow f m n = 0 := by
  intro m
  induction m with
  | zero => intro n h; omega
  | succ _m ih =>
    intro n h
    cases n with
    | zero => rfl
    | succ n =>
      simp only [hdivpow]
      refine Finset.sum_eq_zero fun k hk => ?_
      have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      rw [ih (n - k) (by omega), mul_zero]

private lemma hdivpow_one (f : ℕ → ℤ) (n : ℕ) (hn : 1 ≤ n) : hdivpow f 1 n = f n := by
  cases n with
  | zero => omega
  | succ n =>
    simp only [hdivpow]
    rw [Finset.sum_eq_single n]
    · simp
    · intro k hk hne
      have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      simp [show n - k ≠ 0 by omega]
    · intro h; exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self n)) h

private lemma hdivpow_self (f : ℕ → ℤ) (m : ℕ) : hdivpow f m m = f 1 ^ m := by
  induction m with
  | zero => simp [hdivpow]
  | succ m ih =>
    simp only [hdivpow]
    rw [Finset.sum_eq_single 0]
    · simp [ih, pow_succ']
    · intro k hk hk0
      have hkm : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      rw [hdivpow_gt f m (m - k) (by omega), mul_zero]
    · intro h; exact absurd (Finset.mem_range.mpr (Nat.succ_pos m)) h

private lemma hexp_zero (f : ℕ → ℤ) : hexp f 0 = 1 := by
  simp [hexp, hdivpow]

private lemma hexp_succ (f : ℕ → ℤ) (n : ℕ) :
    hexp f (n + 1) = hmul (fun k => f (k + 1)) (hexp f) n := by
  simp only [hexp, hmul]
  rw [Finset.sum_range_succ']
  simp only [hdivpow, Nat.succ_ne_zero, ↓reduceIte, add_zero]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [Finset.mul_sum]
  have hsplit : ∑ m ∈ Finset.range (n + 1),
        (Nat.choose n k : ℤ) * f (k + 1) * hdivpow f m (n - k) =
      ∑ m ∈ Finset.range (n - k + 1),
        (Nat.choose n k : ℤ) * f (k + 1) * hdivpow f m (n - k) := by
    symm
    refine Finset.sum_subset (Finset.range_mono (by omega)) fun m _ hm => ?_
    simp only [Finset.mem_range, not_lt] at hm
    rw [hdivpow_gt f m (n - k) (by omega), mul_zero]
  exact hsplit

-- 2. Relate hdivpow and hpow via PowerSeries ℚ egf:
private noncomputable def egf (f : ℕ → ℤ) : PowerSeries ℚ :=
  PowerSeries.mk fun n => (f n : ℚ) / (Nat.factorial n : ℚ)

private lemma egf_mul (f g : ℕ → ℤ) : egf f * egf g = egf (hmul f g) := by
  ext n
  rw [PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (f := fun i j => PowerSeries.coeff i (egf f) * PowerSeries.coeff j (egf g))]
  simp only [egf, PowerSeries.coeff_mk, hmul, Int.cast_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hch : (Nat.choose n k : ℚ) * (Nat.factorial k : ℚ) * (Nat.factorial (n - k) : ℚ) =
      (Nat.factorial n : ℚ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hkn
  have hfk : (Nat.factorial k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  have hfnk : (Nat.factorial (n - k) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (n - k))
  have hfn : (Nat.factorial n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  push_cast
  field_simp [hfk, hfnk, hfn]
  linear_combination (f k : ℚ) * (g (n - k) : ℚ) * hch.symm

private lemma egf_deriv (f : ℕ → ℤ) :
    PowerSeries.derivative ℚ (egf f) = egf (fun n => f (n + 1)) := by
  ext n
  rw [PowerSeries.coeff_derivative]
  simp only [egf, PowerSeries.coeff_mk, Nat.factorial_succ, Nat.cast_mul]
  have hn1 : ((n + 1 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
  have hfn : (Nat.factorial n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  push_cast
  field_simp [hn1, hfn]

private lemma egf_hpow (f : ℕ → ℤ) (m : ℕ) : egf f ^ m = egf (hpow f m) := by
  induction m with
  | zero =>
    ext n; simp only [pow_zero, PowerSeries.coeff_one, egf, PowerSeries.coeff_mk, hpow]
    split_ifs with h <;> simp [h]
  | succ m ih =>
    rw [pow_succ', ih, egf_mul]; rfl

private lemma egf_hdivpow (f : ℕ → ℤ) (hf0 : f 0 = 0) (m : ℕ) :
    (1 / (Nat.factorial m : ℚ)) • egf f ^ m = egf (hdivpow f m) := by
  induction m with
  | zero =>
    ext n
    simp only [Nat.factorial_zero, Nat.cast_one, div_one, one_smul, pow_zero,
      PowerSeries.coeff_one, egf, PowerSeries.coeff_mk, hdivpow]
    split_ifs with h <;> simp [h]
  | succ m ih =>
    apply PowerSeries.ext
    intro n
    cases n with
    | zero =>
      simp only [PowerSeries.coeff_smul, smul_eq_mul, PowerSeries.coeff_zero_eq_constantCoeff,
        map_pow, egf, PowerSeries.constantCoeff_mk, hf0, Int.cast_zero, zero_div,
        zero_pow (Nat.succ_ne_zero m), mul_zero, hdivpow]
    | succ n =>
      have hderiv : PowerSeries.derivative ℚ ((1 / (Nat.factorial (m + 1) : ℚ)) • egf f ^ (m + 1)) =
          PowerSeries.derivative ℚ (egf f) * ((1 / (Nat.factorial m : ℚ)) • egf f ^ m) := by
        have hds : ∀ (c : ℚ) (F : PowerSeries ℚ),
            PowerSeries.derivative ℚ (c • F) = c • PowerSeries.derivative ℚ F := by
          intro c F; ext r; simp only [PowerSeries.coeff_derivative, PowerSeries.coeff_smul, smul_eq_mul]; ring
        rw [hds, PowerSeries.derivative_pow]
        ext r
        simp only [PowerSeries.coeff_smul, smul_eq_mul, Nat.factorial_succ, Nat.cast_mul,
          Nat.add_sub_cancel]
        have h1 : PowerSeries.coeff r (((m + 1 : ℕ) : PowerSeries ℚ) * egf f ^ m * PowerSeries.derivative ℚ (egf f)) =
            ((m + 1 : ℕ) : ℚ) * PowerSeries.coeff r (PowerSeries.derivative ℚ (egf f) * egf f ^ m) := by
          rw [show ((m + 1 : ℕ) : PowerSeries ℚ) * egf f ^ m * PowerSeries.derivative ℚ (egf f) =
            ((m + 1 : ℕ) : PowerSeries ℚ) * (PowerSeries.derivative ℚ (egf f) * egf f ^ m) by ring,
            ← nsmul_eq_mul, map_nsmul, nsmul_eq_mul]
        rw [h1, PowerSeries.coeff_mul, PowerSeries.coeff_mul]
        have hm1 : ((m + 1 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero m)
        have hfm : (Nat.factorial m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)
        simp only [PowerSeries.coeff_smul, smul_eq_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun ij _ => ?_
        field_simp [hm1, hfm]
      have hc := congr_arg (PowerSeries.coeff n) hderiv
      rw [PowerSeries.coeff_derivative, ih, egf_deriv, egf_mul] at hc
      have hn1 : ((n + 1 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
      have hfn : (Nat.factorial n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
      have hc' : PowerSeries.coeff (n + 1) ((1 / (Nat.factorial (m + 1) : ℚ)) • egf f ^ (m + 1)) *
            ((n + 1 : ℕ) : ℚ) =
          (hmul (fun k => f (k + 1)) (hdivpow f m) n : ℚ) / (Nat.factorial n : ℚ) := by
        simpa [egf, PowerSeries.coeff_mk] using hc
      have hrhs : PowerSeries.coeff (n + 1) (egf (hdivpow f (m + 1))) =
          (hmul (fun k => f (k + 1)) (hdivpow f m) n : ℚ) / (Nat.factorial (n + 1) : ℚ) := by
        simp [egf, hdivpow, hmul]
      rw [hrhs, Nat.factorial_succ n, Nat.cast_mul]
      field_simp [hn1, hfn] at hc' ⊢
      linarith

private lemma fact_mul_hdivpow (f : ℕ → ℤ) (hf0 : f 0 = 0) (m n : ℕ) :
    (Nat.factorial m : ℤ) * hdivpow f m n = hpow f m n := by
  have h1 := congr_arg (PowerSeries.coeff n) (egf_hdivpow f hf0 m)
  rw [egf_hpow] at h1
  simp only [PowerSeries.coeff_smul, smul_eq_mul, egf, PowerSeries.coeff_mk] at h1
  have hfm : (Nat.factorial m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)
  have hfn : (Nat.factorial n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hq : ((Nat.factorial m : ℤ) * hdivpow f m n : ℚ) = (hpow f m n : ℚ) := by
    push_cast
    field_simp [hfm, hfn] at h1 ⊢
    linarith
  exact_mod_cast hq

-- 3. For prime p and m >= 2, p ∣ hpow f m p whenever f 0 = 0!
private lemma hpow_zero_of_pos (f : ℕ → ℤ) (hf0 : f 0 = 0) : ∀ m : ℕ, 1 ≤ m → hpow f m 0 = 0 := by
  intro m hm
  cases m with
  | zero => omega
  | succ m => simp [hpow, hmul, hf0]

private lemma prime_dvd_hpow (f : ℕ → ℤ) (hf0 : f 0 = 0) (p : ℕ) (hp : Nat.Prime p) :
    ∀ m : ℕ, 2 ≤ m → (p : ℤ) ∣ hpow f m p := by
  intro m hm
  cases m with
  | zero => omega
  | succ m =>
    simp only [hpow, hmul]
    refine Finset.dvd_sum fun k hk => ?_
    have hkp : k ≤ p := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    by_cases hk0 : k = 0
    · subst hk0; simp [hf0]
    · by_cases hkp' : k = p
      · subst hkp'; simp [hpow_zero_of_pos f hf0 m (by omega)]
      · have hd : p ∣ Nat.choose p k := hp.dvd_choose_self hk0 (by omega)
        exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (Int.natCast_dvd_natCast.mpr hd) _) _

private theorem main_proved :
    ∀ a : ℕ → ℤ,
      a 0 = 1 →
      (let A : PowerSeries ℚ := PowerSeries.mk (fun n => (a n : ℚ) / (Nat.factorial n : ℚ))
       let Eneg : PowerSeries ℚ := PowerSeries.mk (fun n => (-1 : ℚ) ^ n / (Nat.factorial n : ℚ))
       PowerSeries.derivative ℚ A = (-PowerSeries.X * Eneg) * A) →
      ∀ p : ℕ, Nat.Prime p →
        a p ^ 2 ≡ 1 [ZMOD (p : ℤ)] := by
  intro a ha0 hode p hp
  let f : ℕ → ℤ := fun k => if k = 0 then 0 else (-1 : ℤ) ^ (k - 1) * ((k : ℤ) - 1)
  have hf0 : f 0 = 0 := rfl
  have hf1 : f 1 = 0 := by simp [f]
  -- Extract recurrence a (n + 1) = hmul (fun k => f (k + 1)) a n from hode!
  have hrec : ∀ n : ℕ, a (n + 1) = hmul (fun k => f (k + 1)) a n := by
    intro n
    have hX_Eneg : (-PowerSeries.X *
        PowerSeries.mk (fun n => (-1 : ℚ) ^ n / (Nat.factorial n : ℚ))) =
        egf (fun k => f (k + 1)) := by
      ext k
      cases k with
      | zero => simp [egf, f, PowerSeries.coeff_zero_eq_constantCoeff]
      | succ k =>
        rw [neg_mul, map_neg, PowerSeries.coeff_succ_X_mul]
        simp only [egf, PowerSeries.coeff_mk, f, Nat.succ_ne_zero, ↓reduceIte,
          Nat.add_sub_cancel, Nat.factorial_succ, Nat.cast_mul, pow_succ]
        have hk1 : ((k + 1 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)
        have hfk : (Nat.factorial k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
        push_cast
        field_simp [hk1, hfk]
        ring
    have hode' : egf (fun k => a (k + 1)) = egf (hmul (fun k => f (k + 1)) a) := by
      rw [← egf_deriv, ← egf_mul, ← hX_Eneg]
      exact hode
    have hc := congr_arg (PowerSeries.coeff n) hode'
    simp only [egf, PowerSeries.coeff_mk] at hc
    have hfn : (Nat.factorial n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
    have hq : (a (n + 1) : ℚ) = (hmul (fun k => f (k + 1)) a n : ℚ) := (div_left_inj' hfn).mp hc
    exact_mod_cast hq
  -- Prove a = hexp f by induction!
  have ha_eq : ∀ n : ℕ, a n = hexp f n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      cases n with
      | zero => rw [ha0, hexp_zero]
      | succ n =>
        rw [hrec n, hexp_succ]
        simp only [hmul]
        refine Finset.sum_congr rfl fun k hk => ?_
        have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        rw [ih (n - k) (by omega)]
  -- Prove a p ≡ -1 (mod p)!
  have hap : a p ≡ -1 [ZMOD (p : ℤ)] := by
    rw [ha_eq p, Int.modEq_iff_dvd]
    have hsplit : hexp f p = f p + ∑ m ∈ (Finset.range (p + 1)).erase 1, hdivpow f m p := by
      have h1mem : 1 ∈ Finset.range (p + 1) := Finset.mem_range.mpr (by have := hp.two_le; omega)
      rw [hexp, ← Finset.add_sum_erase _ _ h1mem, hdivpow_one f p (by have := hp.two_le; omega)]
    rw [hsplit]
    have hsum_dvd : (p : ℤ) ∣ ∑ m ∈ (Finset.range (p + 1)).erase 1, hdivpow f m p := by
      refine Finset.dvd_sum fun m hm => ?_
      have hm1 : m ≠ 1 := (Finset.mem_erase.mp hm).1
      have hmp : m ≤ p := Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_erase.mp hm).2)
      by_cases hm0 : m = 0
      · subst hm0; simp [hdivpow, hp.ne_zero]
      · by_cases hmeq : m = p
        · subst hmeq
          rw [hdivpow_self, hf1, zero_pow hp.ne_zero]
          exact dvd_zero _
        · have h2m : 2 ≤ m := by omega
          have hd_pow : (p : ℤ) ∣ (Nat.factorial m : ℤ) * hdivpow f m p := by
            rw [fact_mul_hdivpow f hf0 m p]
            exact prime_dvd_hpow f hf0 p hp m h2m
          have hcop : IsCoprime (p : ℤ) (Nat.factorial m : ℤ) :=
            Int.isCoprime_iff_nat_coprime.mpr
              (by simpa using (hp.coprime_iff_not_dvd.mpr
                (mt (hp.dvd_factorial.mp) (by omega : ¬p ≤ m))))
          exact hcop.dvd_of_dvd_mul_left hd_pow
    have hfp : (p : ℤ) ∣ (f p - (-1)) := by
      simp only [f, hp.ne_zero, ↓reduceIte]
      by_cases hp2 : p = 2
      · subst hp2; norm_num
      · have hodd : Odd p := hp.odd_of_ne_two hp2
        have hev : Even (p - 1) := by obtain ⟨r, hr⟩ := hodd; exact ⟨r, by omega⟩
        rw [hev.neg_one_pow, one_mul]
        refine ⟨1, by ring⟩
    have hrew : -1 - (f p + ∑ m ∈ (Finset.range (p + 1)).erase 1, hdivpow f m p) =
        -(f p - (-1)) - ∑ m ∈ (Finset.range (p + 1)).erase 1, hdivpow f m p := by ring
    rw [hrew]
    exact dvd_sub (dvd_neg.mpr hfp) hsum_dvd
  have hsq := hap.pow 2
  simpa using hsq

end OMA.P_oeis_a345652

theorem OMA.solution : type_of% @OMA.S_oeis_a345652.main :=
  OMA.P_oeis_a345652.main_proved
