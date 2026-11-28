import OMAStatements.S_oeis_a386648
import Mathlib

namespace OMA.S_oeis_a386648

private noncomputable def egf (f : ℕ → ℤ) : PowerSeries ℚ :=
  PowerSeries.mk (fun n => (f n : ℚ) / (Nat.factorial n : ℚ))

private def hmul (f g : ℕ → ℤ) (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), (Nat.choose n k : ℤ) * f k * g (n - k)

private lemma egf_mul (f g : ℕ → ℤ) : egf f * egf g = egf (hmul f g) := by
  ext n
  simp only [egf, PowerSeries.coeff_mul, PowerSeries.coeff_mk,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (f := fun i j =>
      ((f i : ℚ) / (Nat.factorial i : ℚ)) * ((g j : ℚ) / (Nat.factorial j : ℚ))) n]
  simp only [hmul, Int.cast_sum, Int.cast_mul, Int.cast_natCast, Finset.sum_div]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hch : (Nat.choose n k : ℚ) * (Nat.factorial k : ℚ) * (Nat.factorial (n - k) : ℚ) =
      (Nat.factorial n : ℚ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hkn
  have hfk : (Nat.factorial k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  have hfnk : (Nat.factorial (n - k) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (n - k))
  have hfn : (Nat.factorial n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  field_simp [hfk, hfnk, hfn]
  rw [← hch]; ring

private lemma egf_add (f g : ℕ → ℤ) : egf f + egf g = egf (fun n => f n + g n) := by
  ext n
  simp only [egf, map_add, PowerSeries.coeff_mk, Int.cast_add, add_div]

private lemma egf_sub (f g : ℕ → ℤ) : egf f - egf g = egf (fun n => f n - g n) := by
  ext n
  simp only [egf, map_sub, PowerSeries.coeff_mk, Int.cast_sub, sub_div]

private lemma egf_X_mul (f : ℕ → ℤ) :
    PowerSeries.X * egf f = egf (fun n => if n = 0 then 0 else (n : ℤ) * f (n - 1)) := by
  ext n
  cases n with
  | zero => simp [egf, PowerSeries.coeff_zero_eq_constantCoeff]
  | succ n =>
    simp only [egf, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mk, Nat.succ_ne_zero,
      ↓reduceIte, Nat.add_sub_cancel, Int.cast_mul, Int.cast_natCast, Nat.factorial_succ,
      Nat.cast_mul]
    have h1 : ((n + 1 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
    have h2 : (Nat.factorial n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
    field_simp [h1, h2]

private lemma egf_deriv (f : ℕ → ℤ) :
    PowerSeries.derivative ℚ (egf f) = egf (fun n => f (n + 1)) := by
  ext n
  simp only [egf, PowerSeries.coeff_derivative, PowerSeries.coeff_mk, Nat.factorial_succ,
    Nat.cast_mul]
  have h1 : ((n + 1 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
  have h2 : (Nat.factorial n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  field_simp [h1, h2]
  push_cast; ring

private lemma egf_inj {f g : ℕ → ℤ} (h : egf f = egf g) : f = g := by
  funext n
  have hc := congr_arg (PowerSeries.coeff n) h
  simp only [egf, PowerSeries.coeff_mk] at hc
  have hfn : (Nat.factorial n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hq : (f n : ℚ) = (g n : ℚ) := (div_left_inj' hfn).mp hc
  exact_mod_cast hq

private lemma egf_smul (c : ℤ) (f : ℕ → ℤ) :
    (c : ℚ) • egf f = egf (fun n => c * f n) := by
  ext n
  simp only [PowerSeries.coeff_smul, smul_eq_mul, egf, PowerSeries.coeff_mk, Int.cast_mul]
  ring

private lemma egf_one : (1 : PowerSeries ℚ) = egf (fun n => if n = 0 then 1 else 0) := by
  ext n; simp only [egf, PowerSeries.coeff_one, PowerSeries.coeff_mk]; split_ifs with h <;> simp [h]

private def hdivpow (f : ℕ → ℤ) : ℕ → ℕ → ℤ
  | 0, n => if n = 0 then 1 else 0
  | _ + 1, 0 => 0
  | m + 1, n + 1 =>
      ∑ k ∈ Finset.range (n + 1), (Nat.choose n k : ℤ) * f (k + 1) * hdivpow f m (n - k)

private lemma egf_hdivpow (f : ℕ → ℤ) (hf0 : f 0 = 0) :
    ∀ m : ℕ, (1 / (Nat.factorial m : ℚ)) • (egf f) ^ m = egf (hdivpow f m) := by
  intro m
  induction m with
  | zero =>
    ext n
    simp only [Nat.factorial_zero, Nat.cast_one, div_one, pow_zero, one_smul, egf,
      PowerSeries.coeff_one, PowerSeries.coeff_mk, hdivpow]
    split_ifs with h <;> simp [h]
  | succ m ih =>
    ext n
    cases n with
    | zero =>
      simp only [PowerSeries.coeff_smul, smul_eq_mul, PowerSeries.coeff_zero_eq_constantCoeff,
        map_pow, egf, PowerSeries.constantCoeff_mk, hf0, Int.cast_zero, Nat.factorial_zero,
        Nat.cast_one, div_one, zero_pow (Nat.succ_ne_zero m), mul_zero, hdivpow]
    | succ n =>
      have hderiv : PowerSeries.derivative ℚ ((1 / (Nat.factorial (m + 1) : ℚ)) • (egf f) ^ (m + 1)) =
          egf (hmul (fun k => f (k + 1)) (hdivpow f m)) := by
        have hsmul : ∀ (c : ℚ) (F : PowerSeries ℚ),
            PowerSeries.derivative ℚ (c • F) = c • PowerSeries.derivative ℚ F := by
          intro c F; ext k
          simp only [PowerSeries.coeff_derivative, PowerSeries.coeff_smul, smul_eq_mul]; ring
        rw [hsmul, PowerSeries.derivative_pow, Nat.add_sub_cancel, ← smul_mul_assoc]
        have hsc : (1 / (Nat.factorial (m + 1) : ℚ)) • (((m + 1 : ℕ) : PowerSeries ℚ) * (egf f) ^ m) =
            (1 / (Nat.factorial m : ℚ)) • (egf f) ^ m := by
          ext k
          rw [PowerSeries.coeff_smul, PowerSeries.coeff_smul, ← nsmul_eq_mul, map_nsmul]
          simp only [smul_eq_mul, nsmul_eq_mul, Nat.factorial_succ, Nat.cast_mul]
          have h1 : ((m + 1 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero m)
          have h2 : (Nat.factorial m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)
          field_simp [h1, h2]
        rw [hsc, ih, egf_deriv, egf_mul,
          show hmul (hdivpow f m) (fun k => f (k + 1)) = hmul (fun k => f (k + 1)) (hdivpow f m) from by
            funext r
            have := congr_arg (PowerSeries.coeff r) (mul_comm (egf (hdivpow f m)) (egf (fun k => f (k + 1))))
            rw [egf_mul, egf_mul] at this
            simp only [egf, PowerSeries.coeff_mk] at this
            have hfr : (Nat.factorial r : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero r)
            have hq : (hmul (hdivpow f m) (fun k => f (k + 1)) r : ℚ) =
                (hmul (fun k => f (k + 1)) (hdivpow f m) r : ℚ) := (div_left_inj' hfr).mp this
            exact_mod_cast hq]
      have hc := congr_arg (PowerSeries.coeff n) hderiv
      rw [PowerSeries.coeff_derivative] at hc
      simp only [egf, PowerSeries.coeff_mk, hmul] at hc
      simp only [egf, PowerSeries.coeff_mk, hdivpow]
      rw [Nat.factorial_succ n, Nat.cast_mul]
      have h1 : ((n + 1 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
      have h2 : (Nat.factorial n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
      have hcast : ((n : ℚ) + 1) = ((n + 1 : ℕ) : ℚ) := by push_cast; ring
      rw [hcast] at hc
      have hc' : PowerSeries.coeff (n + 1) ((1 / (Nat.factorial (m + 1) : ℚ)) •
            (PowerSeries.mk fun n => (f n : ℚ) / (Nat.factorial n : ℚ)) ^ (m + 1)) =
          ((∑ x ∈ Finset.range (n + 1), (Nat.choose n x : ℤ) * f (x + 1) * hdivpow f m (n - x) : ℤ) : ℚ) /
            (((n + 1 : ℕ) : ℚ) * (Nat.factorial n : ℚ)) := by
        rw [eq_div_iff (mul_ne_zero h1 h2), ← mul_assoc, hc, div_mul_cancel₀ _ h2]
      exact hc'

private lemma egf_pow_eq (f : ℕ → ℤ) (hf0 : f 0 = 0) (m : ℕ) :
    (egf f) ^ m = egf (fun k => (Nat.factorial m : ℤ) * hdivpow f m k) := by
  have h := congr_arg ((Nat.factorial m : ℚ) • ·) (egf_hdivpow f hf0 m)
  have hfm : (Nat.factorial m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)
  rw [smul_smul, mul_one_div_cancel hfm, one_smul] at h
  rw [h, show (Nat.factorial m : ℚ) = ((Nat.factorial m : ℤ) : ℚ) by simp, egf_smul]

private lemma hdivpow_eq_zero_of_lt (f : ℕ → ℤ) : ∀ m n : ℕ, n < m → hdivpow f m n = 0 := by
  intro m
  induction m with
  | zero => intro n hn; omega
  | succ m ih =>
    intro n hn
    cases n with
    | zero => rfl
    | succ n =>
      simp only [hdivpow]
      refine Finset.sum_eq_zero fun k hk => ?_
      have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      rw [ih (n - k) (by omega), mul_zero]

private lemma hdivpow_one (f : ℕ → ℤ) (m : ℕ) (hm : 1 ≤ m) : hdivpow f 1 m = f m := by
  cases m with
  | zero => omega
  | succ m =>
    simp only [hdivpow]
    rw [Finset.sum_eq_single m]
    · simp
    · intro j hj hjne
      have : m - j ≠ 0 := by have := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj); omega
      simp [this]
    · intro h; exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self m)) h

private lemma hdivpow_congr_mod {p : ℤ} {f1 f2 : ℕ → ℤ} (h : ∀ k, f1 k % p = f2 k % p) :
    ∀ m n : ℕ, hdivpow f1 m n % p = hdivpow f2 m n % p := by
  intro m
  induction m with
  | zero => intro n; simp [hdivpow]
  | succ m ih =>
    intro n
    cases n with
    | zero => simp [hdivpow]
    | succ n =>
      simp only [hdivpow]
      rw [Finset.sum_int_mod]; conv_rhs => rw [Finset.sum_int_mod]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      conv_lhs => rw [Int.mul_emod, Int.mul_emod (Nat.choose n k : ℤ), h (k + 1), ih (n - k)]
      conv_rhs => rw [Int.mul_emod, Int.mul_emod (Nat.choose n k : ℤ)]

private lemma hmul_congr_mod_le {p : ℤ} {f1 f2 g1 g2 : ℕ → ℤ} (n : ℕ)
    (hf : ∀ k ≤ n, f1 k % p = f2 k % p) (hg : ∀ k ≤ n, g1 k % p = g2 k % p) :
    hmul f1 g1 n % p = hmul f2 g2 n % p := by
  simp only [hmul]
  rw [Finset.sum_int_mod]; conv_rhs => rw [Finset.sum_int_mod]
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  conv_lhs => rw [Int.mul_emod, Int.mul_emod (Nat.choose n k : ℤ), hf k hkn, hg (n - k) (by omega)]
  conv_rhs => rw [Int.mul_emod, Int.mul_emod (Nat.choose n k : ℤ)]

private def hexp (f : ℕ → ℤ) (n : ℕ) : ℤ :=
  ∑ m ∈ Finset.range (n + 1), hdivpow f m n

private lemma hexp_zero (f : ℕ → ℤ) : hexp f 0 = 1 := by simp [hexp, hdivpow]

private lemma hexp_succ (f : ℕ → ℤ) (n : ℕ) :
    hexp f (n + 1) = hmul (fun k => f (k + 1)) (hexp f) n := by
  simp only [hexp, hmul]
  rw [Finset.sum_range_succ']
  simp only [hdivpow, Nat.succ_ne_zero, ↓reduceIte, add_zero]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [← Finset.mul_sum]
  congr 1
  symm
  refine Finset.sum_subset (Finset.range_mono (by omega)) fun m _ hm => ?_
  simp only [Finset.mem_range, not_lt] at hm
  exact hdivpow_eq_zero_of_lt f m (n - k) (by omega)

-- LambertW(-x) Hurwitz sequence w(n) = -n^(n-1) for n >= 1, 0 for n = 0
private def wSeq (n : ℕ) : ℤ := if n = 0 then 0 else -((n : ℤ) ^ (n - 1))

-- Mod 2 analysis of hexp wSeq
private def ew2 (n : ℕ) : ℤ := if n = 0 ∨ n = 1 ∨ Even n then 1 else 0

private lemma wSeq_mod2 (n : ℕ) : wSeq n % 2 = if Odd n then 1 else 0 := by
  have hpow_odd : ∀ (b : ℤ) (e : ℕ), b % 2 = 1 → (b ^ e) % 2 = 1 := by
    intro b e hb
    induction e with
    | zero => norm_num
    | succ m ih => rw [pow_succ, Int.mul_emod, ih, hb]; norm_num
  cases n with
  | zero => simp [wSeq]
  | succ n =>
    simp only [wSeq, Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    by_cases ho : Odd (n + 1)
    · simp only [ho, ↓reduceIte]
      obtain ⟨r, hr⟩ := ho
      have h1 : (((n + 1 : ℕ) : ℤ) ^ n) % 2 = 1 := hpow_odd _ n (by omega)
      omega
    · simp only [ho, ↓reduceIte]
      have hev : Even (n + 1) := Nat.not_odd_iff_even.mp ho
      have hn1 : 1 ≤ n := by obtain ⟨r, hr⟩ := hev; omega
      obtain ⟨r, hr⟩ := hev
      have hbase : ((n + 1 : ℕ) : ℤ) % 2 = 0 := by omega
      have hpow : (((n + 1 : ℕ) : ℤ) ^ n) = ((n + 1 : ℕ) : ℤ) ^ (n - 1) * ((n + 1 : ℕ) : ℤ) := by
        rw [← pow_succ, show n - 1 + 1 = n by omega]
      have h1 : (((n + 1 : ℕ) : ℤ) ^ n) % 2 = 0 := by
        rw [hpow, Int.mul_emod, hbase]; norm_num
      omega

private lemma hmul_exp_exp (c1 c2 : ℤ) (m : ℕ) :
    hmul (fun k => c1 ^ k) (fun k => c2 ^ k) m = (c1 + c2) ^ m := by
  simp only [hmul]
  rw [add_pow]
  refine Finset.sum_congr rfl fun k _ => by ring

private lemma hexp_wSeq_mod2 : ∀ n : ℕ, hexp wSeq n % 2 = ew2 n % 2 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [hexp_zero, ew2]
    | succ n =>
      rw [hexp_succ]
      have hw' : ∀ k ≤ n, wSeq (k + 1) % 2 = (if Even k then 1 else 0) % 2 := by
        intro k _
        rw [wSeq_mod2]
        have : Odd (k + 1) ↔ Even k := by rw [Nat.odd_add_one, Nat.not_odd_iff_even]
        by_cases he : Even k <;> simp [this, he]
      rw [hmul_congr_mod_le n hw' (fun k hk => ih k (by omega))]
      -- Compute hmul (even_ind) ew2 n mod 2:
      -- ew2 k % 2 = (if k = 1 then 1 else 0) + (if Even k then 1 else 0) (mod 2)!
      have hew2_split : ∀ k ≤ n, ew2 k % 2 =
          ((if k = 1 then (1 : ℤ) else 0) + if Even k then 1 else 0) % 2 := by
        intro k _
        simp only [ew2]
        by_cases h0 : k = 0
        · subst h0; simp
        · by_cases h1 : k = 1
          · subst h1; simp
          · simp [h0, h1]
      rw [hmul_congr_mod_le n (fun _ _ => rfl) hew2_split]
      have hadd : hmul (fun k => if Even k then (1 : ℤ) else 0)
            (fun k => (if k = 1 then (1 : ℤ) else 0) + if Even k then 1 else 0) n =
          hmul (fun k => if Even k then (1 : ℤ) else 0) (fun k => if k = 1 then 1 else 0) n +
          hmul (fun k => if Even k then (1 : ℤ) else 0) (fun k => if Even k then 1 else 0) n := by
        simp only [hmul, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun k _ => by ring
      rw [hadd]
      have ht1 : hmul (fun k => if Even k then (1 : ℤ) else 0) (fun k => if k = 1 then 1 else 0) n % 2 =
          if Odd n then 1 else 0 := by
        cases n with
        | zero => simp [hmul]
        | succ m =>
          simp only [hmul]
          rw [Finset.sum_eq_single m]
          · simp only [Nat.add_sub_cancel_left, ↓reduceIte, mul_one, Nat.choose_succ_self_right]
            have : Odd (m + 1) ↔ Even m := by rw [Nat.odd_add_one, Nat.not_odd_iff_even]
            by_cases he : Even m
            · simp only [he, this.mpr he, ↓reduceIte, mul_one]
              obtain ⟨r, rfl⟩ := he; omega
            · simp [he, mt this.mp he]
          · intro k hk hkm
            have : m + 1 - k ≠ 1 := by have := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk); omega
            simp [this]
          · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
      have ht2 : hmul (fun k => if Even k then (1 : ℤ) else 0) (fun k => if Even k then 1 else 0) n % 2 =
          if n = 0 then 1 else 0 := by
        cases n with
        | zero => simp [hmul]
        | succ m =>
          -- In Z: ∑_{k even} C(m+1, k) * [m+1-k even] = if Even (m+1) then 2^m else 0!
          simp only [Nat.succ_ne_zero, ↓reduceIte]
          by_cases hev : Even (m + 1)
          · have heq : hmul (fun k => if Even k then (1 : ℤ) else 0)
                (fun k => if Even k then 1 else 0) (m + 1) =
                ∑ k ∈ Finset.range (m + 2), if Even k then (Nat.choose (m + 1) k : ℤ) else 0 := by
              simp only [hmul]
              refine Finset.sum_congr rfl fun k hk => ?_
              have hkm : k ≤ m + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
              by_cases hke : Even k
              · have hmke : Even (m + 1 - k) := by
                  obtain ⟨a, ha⟩ := hev; obtain ⟨b, hb⟩ := hke; exact ⟨a - b, by omega⟩
                simp [hke, hmke]
              · simp [hke]
            rw [heq]
            have h2sum : 2 * ∑ k ∈ Finset.range (m + 2),
                (if Even k then (Nat.choose (m + 1) k : ℤ) else 0) =
                (1 + 1 : ℤ) ^ (m + 1) + ((-1 : ℤ) + 1) ^ (m + 1) := by
              rw [add_pow, add_pow, ← Finset.sum_add_distrib, Finset.mul_sum]
              refine Finset.sum_congr rfl fun k _ => ?_
              by_cases hke : Even k
              · simp only [hke, ↓reduceIte, one_pow, mul_one, one_mul, hke.neg_one_pow]; ring
              · have hko : Odd k := Nat.not_even_iff_odd.mp hke
                simp only [hke, ↓reduceIte, one_pow, mul_one, one_mul, hko.neg_one_pow]; ring
            simp only [neg_add_cancel, zero_pow (Nat.succ_ne_zero m), add_zero] at h2sum
            have hm1 : 1 ≤ m := by obtain ⟨r, hr⟩ := hev; omega
            have h2m : (1 + 1 : ℤ) ^ (m + 1) = 2 * (2 * (2 : ℤ) ^ (m - 1)) := by
              rw [show (1 + 1 : ℤ) = 2 by norm_num, show m + 1 = (m - 1) + 2 by omega, pow_add]
              ring
            rw [h2m] at h2sum
            have : (∑ k ∈ Finset.range (m + 2), if Even k then (Nat.choose (m + 1) k : ℤ) else 0) =
                2 * (2 : ℤ) ^ (m - 1) := by linarith
            rw [this]; omega
          · have hzero : hmul (fun k => if Even k then (1 : ℤ) else 0)
                (fun k => if Even k then 1 else 0) (m + 1) = 0 := by
              simp only [hmul]
              refine Finset.sum_eq_zero fun k hk => ?_
              have hkm : k ≤ m + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
              by_cases hke : Even k
              · have hmko : ¬Even (m + 1 - k) := by
                  intro h2
                  apply hev
                  obtain ⟨a, ha⟩ := hke; obtain ⟨b, hb⟩ := h2
                  exact ⟨a + b, by omega⟩
                simp [hke, hmko]
              · simp [hke]
            simp [hzero]
      rw [Int.add_emod, ht1, ht2]
      simp only [ew2]
      cases n with
      | zero => decide
      | succ m =>
        have : Odd (m + 1) ↔ Even (m + 1 + 1) := by
          rw [Nat.even_add_one, Nat.not_even_iff_odd]
        by_cases ho : Odd (m + 1)
        · simp [ho, this.mp ho]
        · simp [ho, mt this.mpr ho]

-- Mod 3 analysis: closed-form polynomial expressions in (X, E1, Em1)
private def w3 (k : ℕ) : ℤ :=
  2 * (k : ℤ) + (k : ℤ) * (k - 1) + 2 * (k : ℤ) * (k - 1) * (-1 : ℤ) ^ k

private def ew3 (k : ℕ) : ℤ :=
  (-1 : ℤ) ^ k + (if k = 1 then 2 else 0) - (k : ℤ) * (-1 : ℤ) ^ k +
  (k : ℤ) * (k - 1) + 2 * (k : ℤ) * (k - 1) * (-1 : ℤ) ^ k

private def a3 (k : ℕ) : ℤ :=
  (if k = 0 then 1 else if k = 1 then 2 else if k = 2 then 4 else 0) +
  2 * (-1 : ℤ) ^ k + (k : ℤ) + (k : ℤ) * (k - 1)

private lemma wSeq_mod3 (k : ℕ) : wSeq k % 3 = w3 k % 3 := by
  cases k with
  | zero => simp [wSeq, w3]
  | succ k =>
    simp only [wSeq, w3, Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    have hpow : ∀ b e : ℕ, ((b : ℤ) ^ e) % 3 = ((b % 3 : ℕ) : ℤ) ^ e % 3 := by
      intro b e
      induction e with
      | zero => simp
      | succ e ihe =>
        rw [pow_succ, pow_succ, Int.mul_emod, ihe]
        conv_rhs => rw [Int.mul_emod]
        have : (b : ℤ) % 3 = ((b % 3 : ℕ) : ℤ) % 3 := by omega
        rw [this]
    have hneg1 : ∀ e : ℕ, (-1 : ℤ) ^ e = if Even e then 1 else -1 := by
      intro e
      by_cases he : Even e
      · simp [he, he.neg_one_pow]
      · simp [he, (Nat.not_even_iff_odd.mp he).neg_one_pow]
    have h2p : ∀ e : ℕ, (2 : ℤ) ^ e % 3 = if Even e then 1 else 2 := by
      intro e
      induction e with
      | zero => simp
      | succ e ihe =>
        rw [pow_succ, Int.mul_emod, ihe]
        by_cases he : Even e
        · have ho : ¬Even (e + 1) := by rw [Nat.even_add_one]; simp [he]
          simp [he, ho]
        · have he' : Even (e + 1) := by rw [Nat.even_add_one]; exact he
          simp [he, he']
    obtain ⟨q, hq⟩ : ∃ q, k + 1 = 6 * q ∨ k + 1 = 6 * q + 1 ∨ k + 1 = 6 * q + 2 ∨
        k + 1 = 6 * q + 3 ∨ k + 1 = 6 * q + 4 ∨ k + 1 = 6 * q + 5 := ⟨(k + 1) / 6, by omega⟩
    rcases hq with h | h | h | h | h | h
    · have hk0 : (k + 1) % 3 = 0 := by omega
      have hkne : k ≠ 0 := by omega
      have hev : Even (k + 1) := ⟨3 * q, by omega⟩
      have hp0 : (((k + 1 : ℕ) : ℤ) ^ k) % 3 = 0 := by rw [hpow, hk0]; simp [zero_pow hkne]
      have hL : (-(((k + 1 : ℕ) : ℤ) ^ k)) % 3 = 0 := by omega
      rw [hL, hneg1, if_pos hev]
      have hk3 : ((k + 1 : ℕ) : ℤ) = 6 * (q : ℤ) := by omega
      rw [hk3]; ring_nf; omega
    · have hk1 : (k + 1) % 3 = 1 := by omega
      have hodd : ¬Even (k + 1) := by intro ⟨r, hr⟩; omega
      have hp1 : (((k + 1 : ℕ) : ℤ) ^ k) % 3 = 1 := by rw [hpow, hk1]; simp
      have hL : (-(((k + 1 : ℕ) : ℤ) ^ k)) % 3 = 2 := by omega
      rw [hL, hneg1, if_neg hodd]
      have hk3 : ((k + 1 : ℕ) : ℤ) = 6 * (q : ℤ) + 1 := by omega
      rw [hk3]; ring_nf; omega
    · have hk2 : (k + 1) % 3 = 2 := by omega
      have hev : Even (k + 1) := ⟨3 * q + 1, by omega⟩
      have hko : ¬Even k := by intro ⟨r, hr⟩; omega
      have hp2 : (((k + 1 : ℕ) : ℤ) ^ k) % 3 = 2 := by rw [hpow, hk2]; simpa [hko] using h2p k
      have hL : (-(((k + 1 : ℕ) : ℤ) ^ k)) % 3 = 1 := by omega
      rw [hL, hneg1, if_pos hev]
      have hk3 : ((k + 1 : ℕ) : ℤ) = 6 * (q : ℤ) + 2 := by omega
      rw [hk3]; ring_nf; omega
    · have hk0 : (k + 1) % 3 = 0 := by omega
      have hkne : k ≠ 0 := by omega
      have hodd : ¬Even (k + 1) := by intro ⟨r, hr⟩; omega
      have hp0 : (((k + 1 : ℕ) : ℤ) ^ k) % 3 = 0 := by rw [hpow, hk0]; simp [zero_pow hkne]
      have hL : (-(((k + 1 : ℕ) : ℤ) ^ k)) % 3 = 0 := by omega
      rw [hL, hneg1, if_neg hodd]
      have hk3 : ((k + 1 : ℕ) : ℤ) = 6 * (q : ℤ) + 3 := by omega
      rw [hk3]; ring_nf; omega
    · have hk1 : (k + 1) % 3 = 1 := by omega
      have hev : Even (k + 1) := ⟨3 * q + 2, by omega⟩
      have hp1 : (((k + 1 : ℕ) : ℤ) ^ k) % 3 = 1 := by rw [hpow, hk1]; simp
      have hL : (-(((k + 1 : ℕ) : ℤ) ^ k)) % 3 = 2 := by omega
      rw [hL, hneg1, if_pos hev]
      have hk3 : ((k + 1 : ℕ) : ℤ) = 6 * (q : ℤ) + 4 := by omega
      rw [hk3]; ring_nf; omega
    · have hk2 : (k + 1) % 3 = 2 := by omega
      have hodd : ¬Even (k + 1) := by intro ⟨r, hr⟩; omega
      have hke : Even k := ⟨3 * q + 2, by omega⟩
      have hp2 : (((k + 1 : ℕ) : ℤ) ^ k) % 3 = 1 := by rw [hpow, hk2]; simpa [hke] using h2p k
      have hL : (-(((k + 1 : ℕ) : ℤ) ^ k)) % 3 = 2 := by omega
      rw [hL, hneg1, if_neg hodd]
      have hk3 : ((k + 1 : ℕ) : ℤ) = 6 * (q : ℤ) + 5 := by omega
      rw [hk3]; ring_nf; omega

-- Mod 3 zero predicate on PowerSeries ℚ via egf
private def IsZeroMod3 (F : PowerSeries ℚ) : Prop :=
  ∃ f : ℕ → ℤ, F = egf f ∧ ∀ k : ℕ, f k % 3 = 0

private lemma isZeroMod3_of_egf {f : ℕ → ℤ} (h : ∀ k, f k % 3 = 0) :
    IsZeroMod3 (egf f) := ⟨f, rfl, h⟩

private lemma isZeroMod3_to_egf {f : ℕ → ℤ} (h : IsZeroMod3 (egf f)) :
    ∀ k, f k % 3 = 0 := by
  obtain ⟨g, heq, hg⟩ := h
  have := egf_inj heq
  subst this
  exact hg

private lemma isZeroMod3_add {F G : PowerSeries ℚ} (hF : IsZeroMod3 F) (hG : IsZeroMod3 G) :
    IsZeroMod3 (F + G) := by
  obtain ⟨f, rfl, hf⟩ := hF
  obtain ⟨g, rfl, hg⟩ := hG
  exact ⟨fun k => f k + g k, egf_add f g, fun k => by rw [Int.add_emod, hf k, hg k]; norm_num⟩

private lemma isZeroMod3_sub {F G : PowerSeries ℚ} (hF : IsZeroMod3 F) (hG : IsZeroMod3 G) :
    IsZeroMod3 (F - G) := by
  obtain ⟨f, rfl, hf⟩ := hF
  obtain ⟨g, rfl, hg⟩ := hG
  exact ⟨fun k => f k - g k, egf_sub f g, fun k => by rw [Int.sub_emod, hf k, hg k]; norm_num⟩

private lemma isZeroMod3_smul_egf (c : ℤ) (hc : c % 3 = 0) (f : ℕ → ℤ) :
    IsZeroMod3 ((c : ℚ) • egf f) := by
  refine ⟨fun k => c * f k, egf_smul c f, fun k => by rw [Int.mul_emod, hc]; norm_num⟩

private lemma isZeroMod3_smul_zero (c : ℤ) {F : PowerSeries ℚ} (hF : IsZeroMod3 F) :
    IsZeroMod3 ((c : ℚ) • F) := by
  obtain ⟨f, rfl, hf⟩ := hF
  exact ⟨fun k => c * f k, egf_smul c f, fun k => by rw [Int.mul_emod, hf k]; norm_num⟩

private lemma isZeroMod3_mul_egf {F : PowerSeries ℚ} (hF : IsZeroMod3 F) (g : ℕ → ℤ) :
    IsZeroMod3 (F * egf g) := by
  obtain ⟨f, rfl, hf⟩ := hF
  refine ⟨hmul f g, egf_mul f g, fun n => ?_⟩
  simp only [hmul]
  rw [Finset.sum_int_mod]
  have h0 : ∀ k ∈ Finset.range (n + 1),
      ((Nat.choose n k : ℤ) * f k * g (n - k)) % 3 = 0 := by
    intro k _
    rw [Int.mul_emod, Int.mul_emod (Nat.choose n k : ℤ), hf k]; norm_num
  rw [Finset.sum_eq_zero h0]; norm_num

private lemma isZeroMod3_X_mul {F : PowerSeries ℚ} (hF : IsZeroMod3 F) :
    IsZeroMod3 (PowerSeries.X * F) := by
  obtain ⟨f, rfl, hf⟩ := hF
  refine ⟨fun n => if n = 0 then 0 else (n : ℤ) * f (n - 1), egf_X_mul f, fun n => ?_⟩
  dsimp only
  split_ifs
  · norm_num
  · rw [Int.mul_emod, hf (n - 1)]; norm_num

private lemma isZeroMod3_X3_mul_egf (g : ℕ → ℤ) :
    IsZeroMod3 (PowerSeries.X * (PowerSeries.X * (PowerSeries.X * egf g))) := by
  rw [egf_X_mul, egf_X_mul, egf_X_mul]
  refine isZeroMod3_of_egf fun n => ?_
  by_cases hn : n < 3
  · interval_cases n <;> norm_num
  · simp only [show n ≠ 0 by omega, show n - 1 ≠ 0 by omega, show n - 1 - 1 ≠ 0 by omega, ↓reduceIte]
    have hprod : ((n : ℤ) * (((n - 1 : ℕ) : ℤ) * ((n - 1 - 1 : ℕ) : ℤ))) % 3 = 0 := by
      have h1 : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
      have h2 : ((n - 1 - 1 : ℕ) : ℤ) = (n : ℤ) - 2 := by omega
      rw [h1, h2]
      obtain ⟨q, hq⟩ : ∃ q : ℤ, (n : ℤ) = 3 * q ∨ (n : ℤ) = 3 * q + 1 ∨ (n : ℤ) = 3 * q + 2 :=
        ⟨(n : ℤ) / 3, by omega⟩
      rcases hq with h | h | h <;> (rw [h]; ring_nf; omega)
    rw [show (n : ℤ) * (((n - 1 : ℕ) : ℤ) * (((n - 1 - 1 : ℕ) : ℤ) * g (n - 1 - 1 - 1))) =
      ((n : ℤ) * (((n - 1 : ℕ) : ℤ) * ((n - 1 - 1 : ℕ) : ℤ))) * g (n - 1 - 1 - 1) by ring,
      Int.mul_emod, hprod]
    norm_num

private lemma isZeroMod3_exp_sub (c1 c2 : ℤ) (hc : c1 % 3 = c2 % 3) :
    IsZeroMod3 (egf (fun k => c1 ^ k) - egf (fun k => c2 ^ k)) := by
  rw [egf_sub]
  refine isZeroMod3_of_egf fun k => ?_
  have hpow : c1 ^ k % 3 = c2 ^ k % 3 := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, pow_succ, Int.mul_emod, ih, hc]
      conv_rhs => rw [Int.mul_emod]
  omega

-- Helper: exponential basis E_c = egf (fun k => c^k)
private noncomputable def E (c : ℤ) : PowerSeries ℚ := egf (fun k => c ^ k)

private lemma E_mul (c1 c2 : ℤ) : E c1 * E c2 = E (c1 + c2) := by
  simp only [E, egf_mul]
  congr 1; funext k; exact hmul_exp_exp c1 c2 k

private lemma E_zero : E 0 = 1 := by
  rw [egf_one]; simp only [E]; congr 1; funext k; cases k <;> simp

private lemma egf_w3 :
    egf w3 = (2 : ℚ) • (PowerSeries.X * E 1) + PowerSeries.X * (PowerSeries.X * E 1) +
      (2 : ℚ) • (PowerSeries.X * (PowerSeries.X * E (-1))) := by
  rw [show (2 : ℚ) = ((2 : ℤ) : ℚ) from rfl]
  simp only [E, egf_X_mul, egf_smul, egf_add]
  congr 1; funext k
  cases k with
  | zero => simp [w3]
  | succ k =>
    cases k with
    | zero => simp [w3]
    | succ k =>
      simp only [w3, Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel, one_pow, mul_one]
      have h1 : (-1 : ℤ) ^ k = (-1 : ℤ) ^ (k + 2) := by rw [pow_add]; norm_num
      rw [← h1]; push_cast; ring

private lemma egf_ew3 :
    egf ew3 = E (-1) + (2 : ℚ) • (PowerSeries.X * 1) + PowerSeries.X * E (-1) +
      PowerSeries.X * (PowerSeries.X * E 1) +
      (2 : ℚ) • (PowerSeries.X * (PowerSeries.X * E (-1))) := by
  rw [egf_one, show (2 : ℚ) = ((2 : ℤ) : ℚ) from rfl]
  simp only [E, egf_X_mul, egf_smul, egf_add]
  congr 1; funext k
  cases k with
  | zero => simp [ew3]
  | succ k =>
    cases k with
    | zero => simp [ew3]
    | succ k =>
      simp only [ew3, Nat.succ_ne_zero, show k + 2 ≠ 1 by omega, ↓reduceIte,
        Nat.add_sub_cancel, one_pow, mul_one]
      have h1 : (-1 : ℤ) ^ (k + 1) = -((-1 : ℤ) ^ (k + 2)) := by rw [pow_succ]; ring
      have h2 : (-1 : ℤ) ^ k = (-1 : ℤ) ^ (k + 2) := by rw [pow_add]; norm_num
      rw [h1, h2]; push_cast; ring

private lemma egf_a3 :
    egf a3 = 1 + (2 : ℚ) • (PowerSeries.X * 1) + (2 : ℚ) • (PowerSeries.X * (PowerSeries.X * 1)) +
      (2 : ℚ) • E (-1) + PowerSeries.X * E 1 + PowerSeries.X * (PowerSeries.X * E 1) := by
  rw [egf_one, show (2 : ℚ) = ((2 : ℤ) : ℚ) from rfl]
  simp only [E, egf_X_mul, egf_smul, egf_add]
  congr 1; funext k
  cases k with
  | zero => simp [a3]
  | succ k =>
    cases k with
    | zero => simp [a3]
    | succ k =>
      cases k with
      | zero => simp [a3]
      | succ k =>
        simp only [a3, Nat.succ_ne_zero, show k + 3 ≠ 1 by omega, show k + 3 ≠ 2 by omega,
          ↓reduceIte, Nat.add_sub_cancel, one_pow, mul_one]
        push_cast; ring

-- Prove hexp wSeq k % 3 = ew3 k % 3 for all k!
private lemma ew3_ode_mod3 :
    ∀ k : ℕ, ew3 (k + 1) % 3 = hmul (fun j => w3 (j + 1)) ew3 k % 3 := by
  have hzero : IsZeroMod3 (egf (fun k => ew3 (k + 1) - hmul (fun j => w3 (j + 1)) ew3 k)) := by
    rw [← egf_sub, ← egf_mul, ← egf_deriv, ← egf_deriv]
    -- Compute derivatives of egf ew3 and egf w3 directly!
    have hd_E : ∀ c : ℤ, PowerSeries.derivative ℚ (E c) = (c : ℚ) • E c := by
      intro c; simp only [E, egf_deriv, egf_smul]
      congr 1; funext k; rw [pow_succ]; ring
    have hd_X : PowerSeries.derivative ℚ (PowerSeries.X : PowerSeries ℚ) = 1 :=
      PowerSeries.derivative_X
    have hd_smul : ∀ (c : ℚ) (F : PowerSeries ℚ),
        PowerSeries.derivative ℚ (c • F) = c • PowerSeries.derivative ℚ F := by
      intro c F; ext k; simp only [PowerSeries.coeff_derivative, PowerSeries.coeff_smul, smul_eq_mul]; ring
    have hd_1 : PowerSeries.derivative ℚ (1 : PowerSeries ℚ) = 0 := Derivation.map_one_eq_zero _
    have hsmul_C : ∀ (c : ℚ) (F : PowerSeries ℚ), c • F = PowerSeries.C c * F := by
      intro c F; ext r; simp [PowerSeries.coeff_C_mul]
    have hdw3 : PowerSeries.derivative ℚ (egf w3) =
        (2 : ℚ) • E 1 + (4 : ℚ) • (PowerSeries.X * E 1) + (4 : ℚ) • (PowerSeries.X * E (-1)) +
        PowerSeries.X * (PowerSeries.X * E 1) - (2 : ℚ) • (PowerSeries.X * (PowerSeries.X * E (-1))) := by
      rw [egf_w3]
      simp only [map_add, hd_smul, Derivation.leibniz, hd_X, hd_E]
      simp only [smul_eq_mul, hsmul_C, Int.cast_one, Int.cast_neg, map_one, map_neg, map_ofNat]
      ring
    have hdew3 : PowerSeries.derivative ℚ (egf ew3) =
        (2 : ℚ) • 1 + (2 : ℚ) • (PowerSeries.X * E 1) + (3 : ℚ) • (PowerSeries.X * E (-1)) +
        PowerSeries.X * (PowerSeries.X * E 1) - (2 : ℚ) • (PowerSeries.X * (PowerSeries.X * E (-1))) := by
      rw [egf_ew3]
      simp only [map_add, hd_smul, Derivation.leibniz, hd_X, hd_E, mul_one]
      simp only [smul_eq_mul, hsmul_C, Int.cast_one, Int.cast_neg, map_one, map_neg, map_ofNat]
      ring
    rw [hdew3, hdw3, egf_ew3]
    -- Exact algebraic decomposition into X^1 * (mod 3 zero) + X^2 * (mod 3 zero) + X^3 * egf!
    have hE_id : ∀ F G : PowerSeries ℚ,
        PowerSeries.X * (PowerSeries.X * (PowerSeries.X * F)) + G =
        G + PowerSeries.X * (PowerSeries.X * (PowerSeries.X * F)) := fun F G => add_comm _ _
    set X := (PowerSeries.X : PowerSeries ℚ)
    have hdecomp :
        ((2 : ℚ) • 1 + (2 : ℚ) • (X * E 1) + (3 : ℚ) • (X * E (-1)) +
          X * (X * E 1) - (2 : ℚ) • (X * (X * E (-1)))) -
        ((2 : ℚ) • E 1 + (4 : ℚ) • (X * E 1) + (4 : ℚ) • (X * E (-1)) +
          X * (X * E 1) - (2 : ℚ) • (X * (X * E (-1)))) *
        (E (-1) + (2 : ℚ) • (X * 1) + X * E (-1) + X * (X * E 1) + (2 : ℚ) • (X * (X * E (-1)))) =
        X * ((-4 : ℚ) • (E (-2) - E 1) + (-6 : ℚ) • E 1 + (3 : ℚ) • E (-1) + (-6 : ℚ) • 1) +
        X * (X * ((-2 : ℚ) • (E (-2) - E 1) + (-2 : ℚ) • (E 2 - E (-1)) +
          (-9 : ℚ) • E 1 + (-12 : ℚ) • E (-1) + (-9 : ℚ) • 1)) +
        X * (X * (X * ((-6 : ℚ) • E (-2) + (4 : ℚ) • E (-1) + (-13 : ℚ) • 1 + (-2 : ℚ) • E 1 +
          (-4 : ℚ) • E 2 + X * ((4 : ℚ) • E (-2) - E 2)))) := by
      have h1m1 : E 1 * E (-1) = 1 := by rw [E_mul]; simpa using E_zero
      have h11 : E 1 * E 1 = E 2 := E_mul 1 1
      have hm1m1 : E (-1) * E (-1) = E (-2) := E_mul (-1) (-1)
      simp only [hsmul_C]
      have hCs : PowerSeries.C (2 : ℚ) = 2 ∧ PowerSeries.C (3 : ℚ) = 3 ∧
          PowerSeries.C (4 : ℚ) = 4 ∧ PowerSeries.C (-2 : ℚ) = -2 ∧
          PowerSeries.C (-4 : ℚ) = -4 ∧ PowerSeries.C (-6 : ℚ) = -6 ∧
          PowerSeries.C (-9 : ℚ) = -9 ∧ PowerSeries.C (-12 : ℚ) = -12 ∧
          PowerSeries.C (-13 : ℚ) = -13 := by
        refine ⟨map_ofNat _ 2, map_ofNat _ 3, map_ofNat _ 4, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        · rw [map_neg]; simp only [map_ofNat]
      rw [hCs.1, hCs.2.1, hCs.2.2.1, hCs.2.2.2.1, hCs.2.2.2.2.1, hCs.2.2.2.2.2.1,
        hCs.2.2.2.2.2.2.1, hCs.2.2.2.2.2.2.2.1, hCs.2.2.2.2.2.2.2.2]
      rw [← h11, ← hm1m1]
      have hmul_zero : (E 1 * E (-1) - 1) = 0 := by rw [h1m1, sub_self]
      have hpol :
          ((2 * 1 + 2 * (X * E 1) + 3 * (X * E (-1)) + X * (X * E 1) - 2 * (X * (X * E (-1)))) -
            (2 * E 1 + 4 * (X * E 1) + 4 * (X * E (-1)) + X * (X * E 1) - 2 * (X * (X * E (-1)))) *
            (E (-1) + 2 * (X * 1) + X * E (-1) + X * (X * E 1) + 2 * (X * (X * E (-1))))) -
          (X * (-4 * (E (-1) * E (-1) - E 1) + -6 * E 1 + 3 * E (-1) + -6 * 1) +
            X * (X * (-2 * (E (-1) * E (-1) - E 1) + -2 * (E 1 * E 1 - E (-1)) +
              -9 * E 1 + -12 * E (-1) + -9 * 1)) +
            X * (X * (X * (-6 * (E (-1) * E (-1)) + 4 * E (-1) + -13 * 1 + -2 * E 1 +
              -4 * (E 1 * E 1) + X * (4 * (E (-1) * E (-1)) - E 1 * E 1))))) =
          (E 1 * E (-1) - 1) * (-2 - 6 * X - 9 * X ^ 2 - 13 * X ^ 3) := by ring
      have h0 : (E 1 * E (-1) - 1) * (-2 - 6 * X - 9 * X ^ 2 - 13 * X ^ 3) = 0 := by
        rw [hmul_zero, zero_mul]
      rw [h0] at hpol
      exact sub_eq_zero.mp hpol
    rw [hdecomp]
    refine isZeroMod3_add (isZeroMod3_add ?_ ?_) ?_
    · refine isZeroMod3_X_mul (isZeroMod3_add (isZeroMod3_add (isZeroMod3_add ?_ ?_) ?_) ?_)
      · exact isZeroMod3_smul_zero (-4) (isZeroMod3_exp_sub (-2) 1 (by norm_num))
      · exact isZeroMod3_smul_egf (-6) (by norm_num) _
      · exact isZeroMod3_smul_egf 3 (by norm_num) _
      · rw [egf_one]; exact isZeroMod3_smul_egf (-6) (by norm_num) _
    · refine isZeroMod3_X_mul (isZeroMod3_X_mul
        (isZeroMod3_add (isZeroMod3_add (isZeroMod3_add (isZeroMod3_add ?_ ?_) ?_) ?_) ?_))
      · exact isZeroMod3_smul_zero (-2) (isZeroMod3_exp_sub (-2) 1 (by norm_num))
      · exact isZeroMod3_smul_zero (-2) (isZeroMod3_exp_sub 2 (-1) (by norm_num))
      · exact isZeroMod3_smul_egf (-9) (by norm_num) _
      · exact isZeroMod3_smul_egf (-12) (by norm_num) _
      · rw [egf_one]; exact isZeroMod3_smul_egf (-9) (by norm_num) _
    · have htail_egf : ∃ g : ℕ → ℤ,
          ((-6 : ℚ) • E (-2) + (4 : ℚ) • E (-1) + (-13 : ℚ) • 1 + (-2 : ℚ) • E 1 +
            (-4 : ℚ) • E 2 + X * ((4 : ℚ) • E (-2) - E 2)) = egf g := by
        dsimp only [X]
        rw [egf_one, show (-4 : ℚ) = ((-4 : ℤ) : ℚ) by norm_num,
          show (-6 : ℚ) = ((-6 : ℤ) : ℚ) by norm_num,
          show (-13 : ℚ) = ((-13 : ℤ) : ℚ) by norm_num,
          show (-2 : ℚ) = ((-2 : ℤ) : ℚ) by norm_num,
          show (4 : ℚ) = ((4 : ℤ) : ℚ) by norm_num]
        simp only [E, egf_smul, egf_sub, egf_add, egf_X_mul]
        exact ⟨_, rfl⟩
      obtain ⟨g, hg⟩ := htail_egf
      rw [hg]
      exact isZeroMod3_X3_mul_egf g
  intro k
  have hk := isZeroMod3_to_egf hzero k
  omega

private lemma hexp_wSeq_mod3 : ∀ k : ℕ, hexp wSeq k % 3 = ew3 k % 3 := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    cases k with
    | zero => simp [hexp_zero, ew3]
    | succ k =>
      rw [hexp_succ, hmul_congr_mod_le k (fun j _ => wSeq_mod3 (j + 1)) (fun j hj => ih j (by omega)),
        ← ew3_ode_mod3 k]

-- Main mod 3 algebraic identity: a3 + w3 * a3^2 + ew3 - 1 == 0 (mod 3)
private lemma a3_eq_mod3 :
    ∀ k : ℕ, (a3 k + hmul w3 (hmul a3 a3) k + ew3 k - if k = 0 then 1 else 0) % 3 = 0 := by
  have hzero : IsZeroMod3 (egf (fun k => a3 k + hmul w3 (hmul a3 a3) k + ew3 k - if k = 0 then 1 else 0)) := by
    rw [← egf_sub, ← egf_add, ← egf_add, ← egf_mul, ← egf_mul, ← egf_one, egf_a3, egf_w3, egf_ew3]
    set X := (PowerSeries.X : PowerSeries ℚ)
    have hsmul_C : ∀ (c : ℚ) (F : PowerSeries ℚ), c • F = PowerSeries.C c * F := by
      intro c F; ext r; simp [PowerSeries.coeff_C_mul]
    have h1m1 : E 1 * E (-1) = 1 := by rw [E_mul]; simpa using E_zero
    have h11 : E 1 * E 1 = E 2 := E_mul 1 1
    have hm1m1 : E (-1) * E (-1) = E (-2) := E_mul (-1) (-1)
    have hm1m2 : E (-1) * E (-2) = E (-3) := E_mul (-1) (-2)
    have h12 : E 1 * E 2 = E 3 := E_mul 1 2
    have hdecomp :
        (1 + (2 : ℚ) • (X * 1) + (2 : ℚ) • (X * (X * 1)) + (2 : ℚ) • E (-1) + X * E 1 + X * (X * E 1)) +
        ((2 : ℚ) • (X * E 1) + X * (X * E 1) + (2 : ℚ) • (X * (X * E (-1)))) *
          ((1 + (2 : ℚ) • (X * 1) + (2 : ℚ) • (X * (X * 1)) + (2 : ℚ) • E (-1) + X * E 1 + X * (X * E 1)) *
           (1 + (2 : ℚ) • (X * 1) + (2 : ℚ) • (X * (X * 1)) + (2 : ℚ) • E (-1) + X * E 1 + X * (X * E 1))) +
        (E (-1) + (2 : ℚ) • (X * 1) + X * E (-1) + X * (X * E 1) + (2 : ℚ) • (X * (X * E (-1)))) - 1 =
        (3 : ℚ) • E (-1) +
        X * ((9 : ℚ) • E (-1) + (12 : ℚ) • 1 + (3 : ℚ) • E 1) +
        X * (X * ((8 : ℚ) • (E (-3) - 1) + (8 : ℚ) • (E (-2) - E 1) + (4 : ℚ) • (E 2 - E (-1)) +
          (30 : ℚ) • 1 + (27 : ℚ) • E 1 + (12 : ℚ) • E (-1))) +
        X * (X * (X * (
          ((16 : ℚ) • E (-2) + (16 : ℚ) • E (-1) + (28 : ℚ) • 1 + (32 : ℚ) • E 1 + (14 : ℚ) • E 2 + (2 : ℚ) • E 3) +
          X * ((16 : ℚ) • E (-2) + (24 : ℚ) • E (-1) + (20 : ℚ) • 1 + (30 : ℚ) • E 1 + (22 : ℚ) • E 2 + (5 : ℚ) • E 3) +
          X * (X * ((16 : ℚ) • E (-1) + (16 : ℚ) • 1 + (20 : ℚ) • E 1 + (16 : ℚ) • E 2 + (4 : ℚ) • E 3)) +
          X * (X * (X * ((8 : ℚ) • E (-1) + (8 : ℚ) • 1 + (6 : ℚ) • E 1 + (4 : ℚ) • E 2 + E 3)))))) := by
      simp only [hsmul_C]
      have hCs : ∀ n : ℕ, PowerSeries.C (n : ℚ) = (n : PowerSeries ℚ) := fun n => map_natCast _ n
      simp only [show (2 : ℚ) = ((2 : ℕ) : ℚ) from rfl, show (3 : ℚ) = ((3 : ℕ) : ℚ) from rfl,
        show (4 : ℚ) = ((4 : ℕ) : ℚ) from rfl, show (5 : ℚ) = ((5 : ℕ) : ℚ) from rfl,
        show (6 : ℚ) = ((6 : ℕ) : ℚ) from rfl, show (8 : ℚ) = ((8 : ℕ) : ℚ) from rfl,
        show (9 : ℚ) = ((9 : ℕ) : ℚ) from rfl, show (12 : ℚ) = ((12 : ℕ) : ℚ) from rfl,
        show (14 : ℚ) = ((14 : ℕ) : ℚ) from rfl, show (16 : ℚ) = ((16 : ℕ) : ℚ) from rfl,
        show (20 : ℚ) = ((20 : ℕ) : ℚ) from rfl, show (22 : ℚ) = ((22 : ℕ) : ℚ) from rfl,
        show (24 : ℚ) = ((24 : ℕ) : ℚ) from rfl, show (27 : ℚ) = ((27 : ℕ) : ℚ) from rfl,
        show (28 : ℚ) = ((28 : ℕ) : ℚ) from rfl, show (30 : ℚ) = ((30 : ℕ) : ℚ) from rfl,
        show (32 : ℚ) = ((32 : ℕ) : ℚ) from rfl, hCs]
      rw [← h12, ← hm1m2, ← h11, ← hm1m1]
      -- Use E 1 * E (-1) = 1 by substituting!
      have hsub0 : E 1 * E (-1) - 1 = 0 := by rw [h1m1, sub_self]
      -- Check: LHS - RHS is divisible by (E 1 * E (-1) - 1)!
      -- Wait: simplify using ring after replacing all E 1 * E (-1) by 1 via linear_combination!
      linear_combination
        (2 * E 1 * X ^ 6 + 4 * E 1 * X ^ 5 + 6 * E 1 * X ^ 4 + 12 * E 1 * X ^ 3 + 8 * E 1 * X ^ 2 +
         8 * E (-1) * X ^ 4 + 8 * E (-1) * X ^ 3 + 4 * E (-1) * X ^ 2 + 8 * E (-1) * X +
         8 * X ^ 6 + 16 * X ^ 5 + 20 * X ^ 4 + 28 * X ^ 3 + 20 * X ^ 2 + 8 * X) * hsub0
    rw [hdecomp]
    refine isZeroMod3_add (isZeroMod3_add (isZeroMod3_add ?_ ?_) ?_) ?_
    · exact isZeroMod3_smul_egf 3 (by norm_num) _
    · refine isZeroMod3_X_mul (isZeroMod3_add (isZeroMod3_add ?_ ?_) ?_)
      · exact isZeroMod3_smul_egf 9 (by norm_num) _
      · rw [egf_one]; exact isZeroMod3_smul_egf 12 (by norm_num) _
      · exact isZeroMod3_smul_egf 3 (by norm_num) _
    · refine isZeroMod3_X_mul (isZeroMod3_X_mul
        (isZeroMod3_add (isZeroMod3_add (isZeroMod3_add (isZeroMod3_add (isZeroMod3_add ?_ ?_) ?_) ?_) ?_) ?_))
      · rw [← E_zero]
        exact isZeroMod3_smul_zero 8 (isZeroMod3_exp_sub (-3) 0 (by norm_num))
      · exact isZeroMod3_smul_zero 8 (isZeroMod3_exp_sub (-2) 1 (by norm_num))
      · exact isZeroMod3_smul_zero 4 (isZeroMod3_exp_sub 2 (-1) (by norm_num))
      · rw [egf_one]; exact isZeroMod3_smul_egf 30 (by norm_num) _
      · exact isZeroMod3_smul_egf 27 (by norm_num) _
      · exact isZeroMod3_smul_egf 12 (by norm_num) _
    · have htail_egf : ∃ g : ℕ → ℤ,
          (((16 : ℚ) • E (-2) + (16 : ℚ) • E (-1) + (28 : ℚ) • 1 + (32 : ℚ) • E 1 + (14 : ℚ) • E 2 + (2 : ℚ) • E 3) +
          X * ((16 : ℚ) • E (-2) + (24 : ℚ) • E (-1) + (20 : ℚ) • 1 + (30 : ℚ) • E 1 + (22 : ℚ) • E 2 + (5 : ℚ) • E 3) +
          X * (X * ((16 : ℚ) • E (-1) + (16 : ℚ) • 1 + (20 : ℚ) • E 1 + (16 : ℚ) • E 2 + (4 : ℚ) • E 3)) +
          X * (X * (X * ((8 : ℚ) • E (-1) + (8 : ℚ) • 1 + (6 : ℚ) • E 1 + (4 : ℚ) • E 2 + E 3)))) = egf g := by
        dsimp only [X]
        rw [egf_one]
        simp only [E, show (2 : ℚ) = ((2 : ℤ) : ℚ) by norm_num,
          show (4 : ℚ) = ((4 : ℤ) : ℚ) by norm_num,
          show (5 : ℚ) = ((5 : ℤ) : ℚ) by norm_num,
          show (6 : ℚ) = ((6 : ℤ) : ℚ) by norm_num,
          show (8 : ℚ) = ((8 : ℤ) : ℚ) by norm_num,
          show (14 : ℚ) = ((14 : ℤ) : ℚ) by norm_num,
          show (16 : ℚ) = ((16 : ℤ) : ℚ) by norm_num,
          show (20 : ℚ) = ((20 : ℤ) : ℚ) by norm_num,
          show (22 : ℚ) = ((22 : ℤ) : ℚ) by norm_num,
          show (24 : ℚ) = ((24 : ℤ) : ℚ) by norm_num,
          show (28 : ℚ) = ((28 : ℤ) : ℚ) by norm_num,
          show (30 : ℚ) = ((30 : ℤ) : ℚ) by norm_num,
          show (32 : ℚ) = ((32 : ℤ) : ℚ) by norm_num,
          egf_smul, egf_add, egf_X_mul]
        exact ⟨_, rfl⟩
      obtain ⟨g, hg⟩ := htail_egf
      rw [hg]
      exact isZeroMod3_X3_mul_egf g
  exact isZeroMod3_to_egf hzero

private theorem main_proved :
    ∀ a : ℕ → ℤ,
      a 0 = 0 →
      (∀ k : ℕ,
        let A : PowerSeries ℚ := PowerSeries.mk (fun n => (a n : ℚ) / (Nat.factorial n : ℚ))
        let W : PowerSeries ℚ :=
          PowerSeries.mk (fun n => if n = 0 then 0 else -(((n : ℤ) ^ (n - 1) : ℤ) : ℚ) / (Nat.factorial n : ℚ))
        ∑ n ∈ Finset.range (k + 1),
          (1 / (Nat.factorial n : ℚ)) *
            PowerSeries.coeff k ((A ^ n + W) ^ n) =
        if k = 0 then 1 else 0) →
      ∀ n : ℕ, 6 < n →
        a n % 6 =
          if n % 6 = 1 then 2
          else if n % 6 = 2 then 3
          else if n % 6 = 3 then 4
          else if n % 6 = 4 then 3
          else if n % 6 = 5 then 2
          else 5 := by
  intro a ha0 heq
  have hW_eq : PowerSeries.mk (fun n =>
      if n = 0 then (0 : ℚ) else -(((n : ℤ) ^ (n - 1) : ℤ) : ℚ) / (Nat.factorial n : ℚ)) = egf wSeq := by
    ext n; simp only [egf, wSeq, PowerSeries.coeff_mk]
    split_ifs with h <;> simp [h]
  let b : ℕ → ℕ → ℤ := fun n k => (Nat.factorial n : ℤ) * hdivpow a n k + wSeq k
  have hsum_int : ∀ k : ℕ,
      (∑ n ∈ Finset.range (k + 1), hdivpow (b n) n k) = if k = 0 then 1 else 0 := by
    intro k
    have hk := heq k
    have hterm : ∀ n : ℕ,
        (1 / (Nat.factorial n : ℚ)) *
          PowerSeries.coeff k ((egf a ^ n + egf wSeq) ^ n) =
        (hdivpow (b n) n k : ℚ) / (Nat.factorial k : ℚ) := by
      intro n
      cases n with
      | zero =>
        simp only [Nat.factorial_zero, Nat.cast_one, div_one, pow_zero, one_mul,
          PowerSeries.coeff_one, hdivpow]
        split_ifs with h <;> simp [h]
      | succ n =>
        have hadd : egf a ^ (n + 1) + egf wSeq = egf (b (n + 1)) := by
          rw [egf_pow_eq a ha0 (n + 1), egf_add]
        have hb0 : b (n + 1) 0 = 0 := by simp [b, hdivpow, wSeq]
        have hdp := congr_arg (PowerSeries.coeff k) (egf_hdivpow (b (n + 1)) hb0 (n + 1))
        simp only [PowerSeries.coeff_smul, smul_eq_mul, egf, PowerSeries.coeff_mk] at hdp
        rw [hadd]; exact hdp
    have hk' : (∑ n ∈ Finset.range (k + 1), (hdivpow (b n) n k : ℚ)) / (Nat.factorial k : ℚ) =
        if k = 0 then 1 else 0 := by
      rw [Finset.sum_div]
      rw [hW_eq] at hk
      dsimp only [egf] at hterm hk
      simpa only [hterm] using hk
    have hfk : (Nat.factorial k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
    have hq : ((∑ n ∈ Finset.range (k + 1), hdivpow (b n) n k : ℤ) : ℚ) =
        ((if k = 0 then (1 : ℤ) else 0 : ℤ) : ℚ) := by
      rw [Int.cast_sum]
      split_ifs at hk' ⊢ with hkz
      · subst hkz
        simp only [Nat.factorial_zero, Nat.cast_one, div_one] at hk'
        simpa using hk'
      · exact (div_eq_zero_iff.mp hk').resolve_right hfk
    exact_mod_cast hq
  -- 1) Mod 2: a k % 2 = ew2 k % 2 for all k >= 1
  have ha_mod2 : ∀ k : ℕ, 1 ≤ k → a k % 2 = ew2 k % 2 := by
    intro k hk1
    have hsum := congr_arg (· % 2) (hsum_int k)
    simp only [show k ≠ 0 by omega, ↓reduceIte, Int.zero_emod] at hsum
    rw [Finset.sum_int_mod] at hsum
    have hterm2 : ∀ n ∈ Finset.range (k + 1),
        hdivpow (b n) n k % 2 =
        (if n = 1 then a k + wSeq k else hdivpow wSeq n k) % 2 := by
      intro n _
      rcases n with _ | _ | n
      · simp [hdivpow]
      · simp [hdivpow_one _ k hk1, b, Nat.factorial]
      · simp only [show n + 2 ≠ 1 by omega, ↓reduceIte]
        refine hdivpow_congr_mod (fun j => ?_) (n + 2) k
        simp only [b]
        have h2dvd : 2 ∣ Nat.factorial (n + 2) := Nat.dvd_factorial (by omega) (by omega)
        obtain ⟨q, hq⟩ := h2dvd
        have : (Nat.factorial (n + 2) : ℤ) * hdivpow a (n + 2) j =
            2 * ((q : ℤ) * hdivpow a (n + 2) j) := by push_cast [hq]; ring
        rw [this]; omega
    rw [Finset.sum_congr rfl hterm2] at hsum
    have h1_mem : 1 ∈ Finset.range (k + 1) := Finset.mem_range.mpr (by omega)
    have hsplit : (∑ n ∈ Finset.range (k + 1),
          (if n = 1 then a k + wSeq k else hdivpow wSeq n k) % 2) % 2 =
        (a k + hexp wSeq k) % 2 := by
      rw [← Finset.sum_int_mod, ← Finset.add_sum_erase _ _ h1_mem]
      simp only [↓reduceIte]
      have herase : ∑ x ∈ (Finset.range (k + 1)).erase 1,
            (if x = 1 then a k + wSeq k else hdivpow wSeq x k) =
          hexp wSeq k - wSeq k := by
        have hhexp : hexp wSeq k = hdivpow wSeq 1 k +
            ∑ x ∈ (Finset.range (k + 1)).erase 1, hdivpow wSeq x k :=
          (Finset.add_sum_erase _ _ h1_mem).symm
        rw [hdivpow_one wSeq k hk1] at hhexp
        have hcongr : ∑ x ∈ (Finset.range (k + 1)).erase 1,
              (if x = 1 then a k + wSeq k else hdivpow wSeq x k) =
            ∑ x ∈ (Finset.range (k + 1)).erase 1, hdivpow wSeq x k := by
          refine Finset.sum_congr rfl fun x hx => ?_
          simp [(Finset.mem_erase.mp hx).1]
        rw [hcongr]; linarith
      rw [herase]; ring_nf
    rw [hsplit, Int.add_emod, hexp_wSeq_mod2 k] at hsum
    omega
  -- 2) Mod 3: a k % 3 = a3 k % 3 for all k
  have hb_n2 : ∀ k : ℕ, 1 ≤ k →
      hdivpow (b 2) 2 k % 3 = (hmul wSeq (hmul a a) k + hdivpow wSeq 2 k) % 3 := by
    intro k hk1
    have h2 : (1 / (Nat.factorial 2 : ℚ)) • (egf a ^ 2 + egf wSeq) ^ 2 =
        egf (fun j => 12 * hdivpow a 4 j + hmul wSeq (hmul a a) j + hdivpow wSeq 2 j) := by
      have hexp' : (1 / (Nat.factorial 2 : ℚ)) • (egf a ^ 2 + egf wSeq) ^ 2 =
          (12 : ℚ) • ((1 / (Nat.factorial 4 : ℚ)) • egf a ^ 4) +
          egf wSeq * (egf a * egf a) +
          (1 / (Nat.factorial 2 : ℚ)) • egf wSeq ^ 2 := by
        ext j
        simp only [PowerSeries.coeff_smul, smul_eq_mul, map_add]
        have hring : (egf a ^ 2 + egf wSeq) ^ 2 =
            egf a ^ 4 + (2 : ℚ) • (egf wSeq * (egf a * egf a)) + egf wSeq ^ 2 := by
          have : (2 : ℚ) • (egf wSeq * (egf a * egf a)) =
              2 * (egf wSeq * (egf a * egf a)) := by ext r; simp [two_mul]
          rw [this]; ring
        rw [hring]
        simp only [map_add, PowerSeries.coeff_smul, smul_eq_mul]
        norm_num [Nat.factorial]
        ring
      rw [hexp', egf_hdivpow a ha0 4, egf_mul, egf_mul, egf_hdivpow wSeq (by simp [wSeq]) 2,
        show (12 : ℚ) = ((12 : ℤ) : ℚ) from rfl, egf_smul, egf_add, egf_add]
    have hadd : egf a ^ 2 + egf wSeq = egf (b 2) := by
      rw [egf_pow_eq a ha0 2, egf_add]
    have hb0 : b 2 0 = 0 := by simp [b, hdivpow, wSeq]
    have hdp := egf_hdivpow (b 2) hb0 2
    rw [← hadd, h2] at hdp
    have hval := congr_fun (egf_inj hdp.symm) k
    rw [hval]
    rw [show 12 * hdivpow a 4 k + hmul wSeq (hmul a a) k + hdivpow wSeq 2 k =
      3 * (4 * hdivpow a 4 k) + (hmul wSeq (hmul a a) k + hdivpow wSeq 2 k) by ring]
    omega
  have ha_mod3 : ∀ k : ℕ, a k % 3 = a3 k % 3 := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      cases k with
      | zero => simp [ha0, a3]
      | succ k =>
        have hsum := congr_arg (· % 3) (hsum_int (k + 1))
        simp only [Nat.succ_ne_zero, ↓reduceIte, Int.zero_emod] at hsum
        rw [Finset.sum_int_mod] at hsum
        have hterm3 : ∀ n ∈ Finset.range (k + 2),
            hdivpow (b n) n (k + 1) % 3 =
            (if n = 1 then a (k + 1) + wSeq (k + 1)
             else if n = 2 then hmul wSeq (hmul a a) (k + 1) + hdivpow wSeq 2 (k + 1)
             else hdivpow wSeq n (k + 1)) % 3 := by
          intro n _
          rcases n with _ | _ | _ | n
          · simp [hdivpow]
          · simp [hdivpow_one _ (k + 1) (by omega), b, Nat.factorial]
          · simp only [show (2 : ℕ) ≠ 1 by omega, ↓reduceIte]
            exact hb_n2 (k + 1) (by omega)
          · simp only [show n + 3 ≠ 1 by omega, show n + 3 ≠ 2 by omega, ↓reduceIte]
            refine hdivpow_congr_mod (fun j => ?_) (n + 3) (k + 1)
            simp only [b]
            have h3dvd : 3 ∣ Nat.factorial (n + 3) := Nat.dvd_factorial (by omega) (by omega)
            obtain ⟨q, hq⟩ := h3dvd
            have : (Nat.factorial (n + 3) : ℤ) * hdivpow a (n + 3) j =
                3 * ((q : ℤ) * hdivpow a (n + 3) j) := by push_cast [hq]; ring
            rw [this]; omega
        rw [Finset.sum_congr rfl hterm3] at hsum
        have hred : (∑ n ∈ Finset.range (k + 2),
              (if n = 1 then a (k + 1) + wSeq (k + 1)
               else if n = 2 then hmul wSeq (hmul a a) (k + 1) + hdivpow wSeq 2 (k + 1)
               else hdivpow wSeq n (k + 1)) % 3) % 3 =
            (a (k + 1) + hmul wSeq (hmul a a) (k + 1) + hexp wSeq (k + 1)) % 3 := by
          rw [← Finset.sum_int_mod]
          have h1_mem : 1 ∈ Finset.range (k + 2) := Finset.mem_range.mpr (by omega)
          have hrew : (∑ n ∈ Finset.range (k + 2),
                if n = 1 then a (k + 1) + wSeq (k + 1)
                else if n = 2 then hmul wSeq (hmul a a) (k + 1) + hdivpow wSeq 2 (k + 1)
                else hdivpow wSeq n (k + 1)) =
              a (k + 1) + (if k = 0 then 0 else hmul wSeq (hmul a a) (k + 1)) + hexp wSeq (k + 1) := by
            have hdiff : ∀ n ∈ Finset.range (k + 2),
                (if n = 1 then a (k + 1) + wSeq (k + 1)
                 else if n = 2 then hmul wSeq (hmul a a) (k + 1) + hdivpow wSeq 2 (k + 1)
                 else hdivpow wSeq n (k + 1)) =
                hdivpow wSeq n (k + 1) +
                (if n = 1 then a (k + 1) else if n = 2 then hmul wSeq (hmul a a) (k + 1) else 0) := by
              intro n _
              by_cases hn1 : n = 1
              · subst hn1; simp [hdivpow_one wSeq (k + 1) (by omega)]; ring
              · by_cases hn2 : n = 2
                · subst hn2; simp; ring
                · simp [hn1, hn2]
            rw [Finset.sum_congr rfl hdiff, Finset.sum_add_distrib]
            change hexp wSeq (k + 1) + _ = _
            by_cases hk0 : k = 0
            · subst hk0; simp [Finset.sum_range_succ]; ring
            · have h2_mem : 2 ∈ (Finset.range (k + 2)).erase 1 :=
                Finset.mem_erase.mpr ⟨by omega, Finset.mem_range.mpr (by omega)⟩
              rw [← Finset.add_sum_erase _ _ h1_mem, ← Finset.add_sum_erase _ _ h2_mem]
              simp only [↓reduceIte, show (2 : ℕ) ≠ 1 by omega, hk0]
              have hrest : ∑ x ∈ ((Finset.range (k + 2)).erase 1).erase 2,
                    (if x = 1 then a (k + 1) else if x = 2 then hmul wSeq (hmul a a) (k + 1) else 0) = 0 := by
                refine Finset.sum_eq_zero fun x hx => ?_
                have hx2 := (Finset.mem_erase.mp hx).1
                have hx1 := (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).1
                simp [hx1, hx2]
              rw [hrest]; ring
          rw [hrew]
          by_cases hk0 : k = 0
          · subst hk0
            have h0 : hmul wSeq (hmul a a) 1 = 0 := by
              simp [hmul, Finset.sum_range_succ, wSeq, ha0]
            simp [h0]
          · simp [hk0]
        rw [hred] at hsum
        -- Notice hmul wSeq (hmul a a) (k + 1) only depends on a j for j <= k since wSeq 0 = 0!
        have hwa2 : hmul wSeq (hmul a a) (k + 1) % 3 = hmul w3 (hmul a3 a3) (k + 1) % 3 := by
          rw [hmul, hmul]
          rw [Finset.sum_int_mod]; conv_rhs => rw [Finset.sum_int_mod]
          congr 1
          refine Finset.sum_congr rfl fun j hj => ?_
          have hjk : j ≤ k + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
          by_cases hj0 : j = 0
          · subst hj0; simp [wSeq, w3]
          · have hlt : k + 1 - j < k + 1 := by omega
            have haa : hmul a a (k + 1 - j) % 3 = hmul a3 a3 (k + 1 - j) % 3 :=
              hmul_congr_mod_le (k + 1 - j) (fun r hr => ih r (by omega)) (fun r hr => ih r (by omega))
            conv_lhs => rw [Int.mul_emod, Int.mul_emod (Nat.choose (k + 1) j : ℤ), wSeq_mod3 j, haa]
            conv_rhs => rw [Int.mul_emod, Int.mul_emod (Nat.choose (k + 1) j : ℤ)]
        have heq3 := a3_eq_mod3 (k + 1)
        simp only [Nat.succ_ne_zero, ↓reduceIte, sub_zero] at heq3
        have hsum3 : (a (k + 1) % 3 + hmul wSeq (hmul a a) (k + 1) % 3 + hexp wSeq (k + 1) % 3) % 3 = 0 := by
          omega
        rw [hwa2, hexp_wSeq_mod3 (k + 1)] at hsum3
        omega
  -- 3) Combine mod 2 and mod 3 for n > 6!
  intro n hn
  have h2 := ha_mod2 n (by omega)
  have h3 := ha_mod3 n
  have hn0 : n ≠ 0 := by omega
  have hn1 : n ≠ 1 := by omega
  have hn2 : n ≠ 2 := by omega
  simp only [ew2, hn0, hn1, false_or] at h2
  simp only [a3, hn0, hn1, hn2, ↓reduceIte, zero_add] at h3
  obtain ⟨q, hq⟩ : ∃ q, n = 6 * q ∨ n = 6 * q + 1 ∨ n = 6 * q + 2 ∨
      n = 6 * q + 3 ∨ n = 6 * q + 4 ∨ n = 6 * q + 5 := ⟨n / 6, by omega⟩
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
  · have hev : Even (6 * q) := ⟨3 * q, by omega⟩
    simp only [hev, ↓reduceIte, hev.neg_one_pow] at h2 h3
    have hmul6 : ((6 * q : ℕ) : ℤ) * ((6 * q : ℕ) - 1) = 3 * (2 * (q : ℤ) * (6 * (q : ℤ) - 1)) := by
      push_cast; ring
    rw [hmul6] at h3
    have hmod : (6 * q) % 6 = 0 := by omega
    simp only [hmod, OfNat.zero_ne_ofNat, ↓reduceIte]; omega
  · have hodd : Odd (6 * q + 1) := ⟨3 * q, by omega⟩
    have hnev : ¬Even (6 * q + 1) := Nat.not_even_iff_odd.mpr hodd
    simp only [hnev, ↓reduceIte, hodd.neg_one_pow] at h2 h3
    have hmul6 : ((6 * q + 1 : ℕ) : ℤ) * ((6 * q + 1 : ℕ) - 1) =
        3 * ((6 * (q : ℤ) + 1) * (2 * (q : ℤ))) := by push_cast; ring
    rw [hmul6] at h3
    have hmod : (6 * q + 1) % 6 = 1 := by omega
    simp only [hmod, ↓reduceIte]; omega
  · have hev : Even (6 * q + 2) := ⟨3 * q + 1, by omega⟩
    simp only [hev, ↓reduceIte, hev.neg_one_pow] at h2 h3
    have hmul6 : ((6 * q + 2 : ℕ) : ℤ) * ((6 * q + 2 : ℕ) - 1) =
        3 * (12 * (q : ℤ) ^ 2 + 6 * (q : ℤ)) + 2 := by push_cast; ring
    rw [hmul6] at h3
    have hmod : (6 * q + 2) % 6 = 2 := by omega
    simp only [hmod, OfNat.ofNat_ne_one, ↓reduceIte]; omega
  · have hodd : Odd (6 * q + 3) := ⟨3 * q + 1, by omega⟩
    have hnev : ¬Even (6 * q + 3) := Nat.not_even_iff_odd.mpr hodd
    simp only [hnev, ↓reduceIte, hodd.neg_one_pow] at h2 h3
    have hmul6 : ((6 * q + 3 : ℕ) : ℤ) * ((6 * q + 3 : ℕ) - 1) =
        3 * ((2 * (q : ℤ) + 1) * (6 * (q : ℤ) + 2)) := by push_cast; ring
    rw [hmul6] at h3
    have hmod : (6 * q + 3) % 6 = 3 := by omega
    simp only [hmod, ↓reduceIte]; omega
  · have hev : Even (6 * q + 4) := ⟨3 * q + 2, by omega⟩
    simp only [hev, ↓reduceIte, hev.neg_one_pow] at h2 h3
    have hmul6 : ((6 * q + 4 : ℕ) : ℤ) * ((6 * q + 4 : ℕ) - 1) =
        3 * ((6 * (q : ℤ) + 4) * (2 * (q : ℤ) + 1)) := by push_cast; ring
    rw [hmul6] at h3
    have hmod : (6 * q + 4) % 6 = 4 := by omega
    simp only [hmod, ↓reduceIte]; omega
  · have hodd : Odd (6 * q + 5) := ⟨3 * q + 2, by omega⟩
    have hnev : ¬Even (6 * q + 5) := Nat.not_even_iff_odd.mpr hodd
    simp only [hnev, ↓reduceIte, hodd.neg_one_pow] at h2 h3
    have hmul6 : ((6 * q + 5 : ℕ) : ℤ) * ((6 * q + 5 : ℕ) - 1) =
        3 * (12 * (q : ℤ) ^ 2 + 18 * (q : ℤ) + 6) + 2 := by push_cast; ring
    rw [hmul6] at h3
    have hmod : (6 * q + 5) % 6 = 5 := by omega
    simp only [hmod, ↓reduceIte]; omega

end OMA.S_oeis_a386648

theorem OMA.solution : type_of% @OMA.S_oeis_a386648.main :=
  OMA.S_oeis_a386648.main_proved
