import OMAStatements.S_oeis_a396806
import Mathlib

-- Original proof by @Volkopat.

namespace OMA.S_oeis_a396806

private def egf (f : ℕ → ℤ) : PowerSeries ℚ :=
  PowerSeries.mk fun n => (f n : ℚ) / (Nat.factorial n : ℚ)

private def hdivpow (g : ℕ → ℤ) : ℕ → ℕ → ℤ
  | 0, n => if n = 0 then 1 else 0
  | _ + 1, 0 => 0
  | k + 1, n + 1 =>
    ∑ j ∈ Finset.range (n + 1), (Nat.choose n j : ℤ) * g (j + 1) * hdivpow g k (n - j)

private def hcomp (f g : ℕ → ℤ) (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), f k * hdivpow g k n

private lemma egf_injective {f g : ℕ → ℤ} (h : egf f = egf g) : f = g := by
  ext n
  have hn := congr_arg (PowerSeries.coeff n) h
  simp only [egf, PowerSeries.coeff_mk] at hn
  have hfac : (Nat.factorial n : ℚ) ≠ 0 := by positivity
  have hq : (f n : ℚ) = (g n : ℚ) := (div_left_inj' hfac).mp hn
  exact_mod_cast hq

private lemma egf_deriv (f : ℕ → ℤ) :
    PowerSeries.derivative (R := ℚ) (egf f) = egf (fun n => f (n + 1)) := by
  ext n
  rw [PowerSeries.coeff_derivative, egf, PowerSeries.coeff_mk, egf, PowerSeries.coeff_mk]
  rw [Nat.factorial_succ]
  push_cast
  have h1 : (n : ℚ) + 1 ≠ 0 := by positivity
  have h2 : (Nat.factorial n : ℚ) ≠ 0 := by positivity
  field_simp

private lemma egf_mul (f g : ℕ → ℤ) :
    egf f * egf g = egf (fun n => ∑ j ∈ Finset.range (n + 1),
      (Nat.choose n j : ℤ) * f j * g (n - j)) := by
  ext n
  rw [PowerSeries.coeff_mul]
  change ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n,
    PowerSeries.coeff x.1 (egf f) * PowerSeries.coeff x.2 (egf g) = _
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => PowerSeries.coeff i (egf f) * PowerSeries.coeff j (egf g)) n]
  simp only [egf, PowerSeries.coeff_mk, Int.cast_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hch := Nat.choose_mul_factorial_mul_factorial hjn
  have hchQ : (Nat.choose n j : ℚ) * (Nat.factorial j : ℚ) * (Nat.factorial (n - j) : ℚ) =
      (Nat.factorial n : ℚ) := by exact_mod_cast hch
  have hfj : (Nat.factorial j : ℚ) ≠ 0 := by positivity
  have hfnj : (Nat.factorial (n - j) : ℚ) ≠ 0 := by positivity
  have hfn : (Nat.factorial n : ℚ) ≠ 0 := by positivity
  push_cast
  field_simp
  linear_combination -(f j : ℚ) * (g (n - j) : ℚ) * hchQ

private lemma hdivpow_zero_of_lt (g : ℕ → ℤ) : ∀ k n, n < k → hdivpow g k n = 0 := by
  intro k
  induction k with
  | zero => intro n hn; omega
  | succ k ih =>
    intro n hn
    cases n with
    | zero => rfl
    | succ m =>
      simp only [hdivpow]
      refine Finset.sum_eq_zero fun j hj => ?_
      have hjm : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      rw [ih (m - j) (by omega), mul_zero]

private lemma egf_hdivpow (g : ℕ → ℤ) (hg0 : g 0 = 0) :
    ∀ k : ℕ, egf (hdivpow g k) = PowerSeries.C ((Nat.factorial k : ℚ)⁻¹) * (egf g) ^ k := by
  intro k
  induction k with
  | zero =>
    ext n
    cases n <;> simp [egf, hdivpow, PowerSeries.coeff_one]
  | succ k ih =>
    have hderiv : PowerSeries.derivative (R := ℚ) (egf (hdivpow g (k + 1))) =
        PowerSeries.derivative (R := ℚ) (PowerSeries.C ((Nat.factorial (k + 1) : ℚ)⁻¹) * (egf g) ^ (k + 1)) := by
      rw [egf_deriv]
      have h1 : egf (fun n => hdivpow g (k + 1) (n + 1)) =
          egf (fun n => g (n + 1)) * egf (hdivpow g k) := by
        rw [egf_mul]
        rfl
      rw [h1, ih, ← egf_deriv]
      rw [Derivation.leibniz, PowerSeries.derivative_C, smul_zero, add_zero,
        Derivation.leibniz_pow]
      simp only [Nat.add_sub_cancel, nsmul_eq_mul, smul_eq_mul]
      rw [show ((k + 1 : ℕ) : PowerSeries ℚ) = PowerSeries.C ((k + 1 : ℕ) : ℚ) by ext m; simp]
      have hfac : PowerSeries.C ((Nat.factorial (k + 1) : ℚ)⁻¹) *
          PowerSeries.C ((k + 1 : ℕ) : ℚ) = PowerSeries.C ((Nat.factorial k : ℚ)⁻¹) := by
        rw [← map_mul]; congr 1
        rw [Nat.factorial_succ]; push_cast
        have h1 : (k : ℚ) + 1 ≠ 0 := by positivity
        have h2 : (Nat.factorial k : ℚ) ≠ 0 := by positivity
        field_simp
      calc PowerSeries.derivative (R := ℚ) (egf g) *
            (PowerSeries.C ((Nat.factorial k : ℚ)⁻¹) * egf g ^ k)
          = PowerSeries.C ((Nat.factorial k : ℚ)⁻¹) *
              (egf g ^ k * PowerSeries.derivative (R := ℚ) (egf g)) := by ring
        _ = PowerSeries.C ((Nat.factorial (k + 1) : ℚ)⁻¹) *
              (PowerSeries.C ((k + 1 : ℕ) : ℚ) *
                (egf g ^ k * PowerSeries.derivative (R := ℚ) (egf g))) := by
            rw [← hfac]; ring
    ext n
    cases n with
    | zero =>
      simp [egf, hdivpow, hg0, zero_pow (Nat.succ_ne_zero k)]
    | succ m =>
      have h := congr_arg (PowerSeries.coeff m) hderiv
      rw [PowerSeries.coeff_derivative, PowerSeries.coeff_derivative] at h
      have hne : ((m : ℚ) + 1) ≠ 0 := by positivity
      exact mul_right_cancel₀ hne h

private lemma egf_hasSubst (g : ℕ → ℤ) (hg0 : g 0 = 0) :
    PowerSeries.HasSubst (egf g) := by
  refine PowerSeries.HasSubst.of_constantCoeff_zero ?_
  change PowerSeries.constantCoeff (egf g) = 0
  rw [← PowerSeries.coeff_zero_eq_constantCoeff, egf, PowerSeries.coeff_mk, hg0]
  simp

private lemma subst_egf (f g : ℕ → ℤ) (hg0 : g 0 = 0) :
    PowerSeries.subst (egf g) (egf f) = egf (hcomp f g) := by
  have hs := egf_hasSubst g hg0
  ext n
  rw [PowerSeries.coeff_subst' hs]
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.range (n + 1))]
  · simp only [egf, PowerSeries.coeff_mk, hcomp, Int.cast_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hk := congr_arg (PowerSeries.coeff n) (egf_hdivpow g hg0 k)
    rw [PowerSeries.coeff_C_mul, egf, PowerSeries.coeff_mk] at hk
    rw [smul_eq_mul]
    calc (f k : ℚ) / (Nat.factorial k : ℚ) * PowerSeries.coeff n (egf g ^ k)
        = (f k : ℚ) * ((Nat.factorial k : ℚ)⁻¹ * PowerSeries.coeff n (egf g ^ k)) := by ring
      _ = (f k : ℚ) * ((hdivpow g k n : ℚ) / (Nat.factorial n : ℚ)) := by rw [← hk]
      _ = ((f k * hdivpow g k n : ℤ) : ℚ) / (Nat.factorial n : ℚ) := by push_cast; ring
  · intro k hk
    simp only [Function.mem_support, ne_eq] at hk
    by_contra hnot
    simp only [Finset.mem_coe, Finset.mem_range, not_lt] at hnot
    have hk0 := congr_arg (PowerSeries.coeff n) (egf_hdivpow g hg0 k)
    rw [PowerSeries.coeff_C_mul, egf, PowerSeries.coeff_mk,
      hdivpow_zero_of_lt g k n (by omega), Int.cast_zero, zero_div] at hk0
    have hfac : (Nat.factorial k : ℚ)⁻¹ ≠ 0 := by positivity
    have hpow0 : PowerSeries.coeff n (egf g ^ k) = 0 :=
      (mul_eq_zero.mp hk0.symm).resolve_left hfac
    exact hk (by rw [hpow0, smul_zero])

private lemma exp_eq_egf_one : PowerSeries.exp ℚ = egf (fun _ => 1) := by
  ext n
  rw [PowerSeries.coeff_exp, egf, PowerSeries.coeff_mk, Algebra.algebraMap_self,
    RingHom.id_apply, Int.cast_one]

private lemma X_mul_egf (f : ℕ → ℤ) :
    PowerSeries.X * egf f = egf (fun n => if n = 0 then 0 else (n : ℤ) * f (n - 1)) := by
  ext n
  cases n with
  | zero => simp [egf]
  | succ m =>
    rw [PowerSeries.coeff_succ_X_mul, egf, PowerSeries.coeff_mk, egf, PowerSeries.coeff_mk]
    simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel, Nat.factorial_succ]
    push_cast
    have h1 : (m : ℚ) + 1 ≠ 0 := by positivity
    have h2 : (Nat.factorial m : ℚ) ≠ 0 := by positivity
    field_simp

-- Congruence mod 2 on sequences ℕ → ℤ
private lemma hdivpow_congr_mod2 {g1 g2 : ℕ → ℤ} {N : ℕ}
    (hg : ∀ m ≤ N, g1 m % 2 = g2 m % 2) :
    ∀ k n, n ≤ N → hdivpow g1 k n % 2 = hdivpow g2 k n % 2 := by
  intro k
  induction k with
  | zero => intro n _; rfl
  | succ k ih =>
    intro n hn
    cases n with
    | zero => rfl
    | succ m =>
      simp only [hdivpow]
      exact Int.ModEq.sum fun j hj =>
        Int.ModEq.mul (Int.ModEq.mul_left _ (hg (j + 1) (by have := Finset.mem_range.mp hj; omega)))
          (ih (m - j) (by omega))
private lemma hcomp_congr_mod2 {f1 f2 g1 g2 : ℕ → ℤ} {N : ℕ}
    (hf : ∀ m ≤ N, f1 m % 2 = f2 m % 2)
    (hg : ∀ m ≤ N, g1 m % 2 = g2 m % 2) :
    ∀ n ≤ N, hcomp f1 g1 n % 2 = hcomp f2 g2 n % 2 := by
  intro n hn
  simp only [hcomp]
  exact Int.ModEq.sum fun k hk =>
    Int.ModEq.mul (hf k (by have := Finset.mem_range.mp hk; omega)) (hdivpow_congr_mod2 hg k n hn)
private lemma hcomp_zero {f g : ℕ → ℤ} (hf0 : f 0 = 0) : hcomp f g 0 = 0 := by
  simp [hcomp, hdivpow, hf0]

private def f0 (n : ℕ) : ℤ := (n : ℤ)

private def idSeq (n : ℕ) : ℤ := if n = 1 then 1 else 0

private lemma egf_f0 : egf f0 = PowerSeries.X * PowerSeries.exp ℚ := by
  rw [exp_eq_egf_one, X_mul_egf]
  congr 1; ext n
  cases n <;> simp [f0]

private lemma egf_idSeq : egf idSeq = PowerSeries.X := by
  ext n
  match n with
  | 0 => simp [egf, idSeq]
  | 1 => simp [egf, idSeq]
  | k + 2 => simp [egf, idSeq, PowerSeries.coeff_X]

private lemma hcomp_idSeq_left (g : ℕ → ℤ) (hg0 : g 0 = 0) : hcomp idSeq g = g := by
  apply egf_injective
  rw [← subst_egf idSeq g hg0, egf_idSeq, PowerSeries.subst_X (egf_hasSubst g hg0)]

private lemma hcomp_idSeq_right (f : ℕ → ℤ) : hcomp f idSeq = f := by
  apply egf_injective
  rw [← subst_egf f idSeq (by simp [idSeq]), egf_idSeq, PowerSeries.X_subst]

private lemma hdivpow_f0 (k n : ℕ) :
    hdivpow f0 k n = (Nat.choose n k : ℤ) * (k : ℤ) ^ (n - k) := by
  have heq : egf (hdivpow f0 k) =
      egf (fun m => (Nat.choose m k : ℤ) * (k : ℤ) ^ (m - k)) := by
    rw [egf_hdivpow f0 rfl, egf_f0, mul_pow]
    have hexp_pow : (PowerSeries.exp ℚ) ^ k = egf (fun m => (k : ℤ) ^ m) := by
      induction k with
      | zero => ext m; cases m <;> simp [egf, PowerSeries.coeff_one]
      | succ j ih =>
        rw [pow_succ, ih, exp_eq_egf_one, egf_mul]
        congr 1
        funext m
        rw [Nat.cast_succ, add_pow]
        simp only [one_pow, mul_one]
        exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
    rw [hexp_pow]
    ext m
    rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul']
    simp only [egf, PowerSeries.coeff_mk]
    split_ifs with hkm
    · have hch := Nat.choose_mul_factorial_mul_factorial hkm
      have hchQ : (Nat.choose m k : ℚ) * (Nat.factorial k : ℚ) * (Nat.factorial (m - k) : ℚ) =
          (Nat.factorial m : ℚ) := by exact_mod_cast hch
      have hfk : (Nat.factorial k : ℚ) ≠ 0 := by positivity
      have hfmk : (Nat.factorial (m - k) : ℚ) ≠ 0 := by positivity
      have hfm : (Nat.factorial m : ℚ) ≠ 0 := by positivity
      push_cast
      field_simp
      linear_combination -(k : ℚ) ^ (m - k) * hchQ
    · simp only [Nat.choose_eq_zero_of_lt (by omega : m < k),
        Nat.cast_zero, zero_mul, Int.cast_zero, zero_div, mul_zero]
  exact congr_fun (egf_injective heq) n

private lemma sum_mul_choose (n : ℕ) (hn : 1 ≤ n) :
    ∑ k ∈ Finset.range (n + 1), k * Nat.choose n k = n * 2 ^ (n - 1) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  rw [Finset.sum_range_succ']
  simp only [Nat.add_sub_cancel, zero_mul, add_zero]
  have h (k : ℕ) : (k + 1) * Nat.choose (m + 1) (k + 1) = (m + 1) * Nat.choose m k := by
    rw [Nat.mul_comm (k + 1), ← Nat.add_one_mul_choose_eq]
  simp_rw [h, ← Finset.mul_sum, Nat.sum_range_choose]

private lemma hcomp_f0_f0_mod2 (n : ℕ) :
    hcomp f0 f0 n % 2 = idSeq n % 2 := by
  simp only [hcomp, f0, hdivpow_f0]
  have hterm : ∀ k ∈ Finset.range (n + 1),
      ((k : ℤ) * ((Nat.choose n k : ℤ) * (k : ℤ) ^ (n - k))) % 2 =
      ((k * Nat.choose n k : ℕ) : ℤ) % 2 := by
    intro k _
    have hpow : ((k : ℤ) * (k : ℤ) ^ (n - k)) % 2 = (k : ℤ) % 2 := by
      have hpar : ∀ e : ℕ, ((k : ℤ) ^ (e + 1)) % 2 = (k : ℤ) % 2 := by
        intro e
        induction e with
        | zero => simp
        | succ e' ihe =>
          rw [pow_succ, Int.mul_emod, ihe]
          rcases Int.emod_two_eq_zero_or_one (k : ℤ) with h | h <;> simp [h]
      rw [← pow_succ']
      exact hpar (n - k)
    calc ((k : ℤ) * ((Nat.choose n k : ℤ) * (k : ℤ) ^ (n - k))) % 2
        = ((Nat.choose n k : ℤ) * ((k : ℤ) * (k : ℤ) ^ (n - k))) % 2 := by ring_nf
      _ = ((Nat.choose n k : ℤ) % 2 * (((k : ℤ) * (k : ℤ) ^ (n - k)) % 2)) % 2 := Int.mul_emod _ _ _
      _ = ((Nat.choose n k : ℤ) % 2 * ((k : ℤ) % 2)) % 2 := by rw [hpow]
      _ = ((Nat.choose n k : ℤ) * (k : ℤ)) % 2 := (Int.mul_emod _ _ _).symm
      _ = ((k * Nat.choose n k : ℕ) : ℤ) % 2 := by push_cast; ring_nf
  rw [Finset.sum_int_mod, Finset.sum_congr rfl hterm, ← Finset.sum_int_mod]
  rw [← Nat.cast_sum]
  rcases n with _ | _ | m
  · simp [idSeq]
  · simp [idSeq, Finset.sum_range_succ]
  · rw [sum_mul_choose (m + 2) (by omega)]
    simp only [idSeq, show m + 2 ≠ 1 by omega, ↓reduceIte, Int.zero_emod]
    have h2 : 2 ∣ (m + 2) * 2 ^ (m + 2 - 1) := by
      rw [show m + 2 - 1 = m + 1 by omega, pow_succ]
      exact ⟨(m + 2) * 2 ^ m, by ring⟩
    rcases h2 with ⟨q, hq⟩
    rw [hq]; push_cast; omega

end OMA.S_oeis_a396806

open OMA.S_oeis_a396806 in
theorem OMA.solution : type_of% @OMA.S_oeis_a396806.main := by
  intro a A hA ha0 heq
  change A = egf a at hA
  let B (k : ℕ) := (fun f : ℕ → ℤ => hcomp f a)^[k] a
  have step (k : ℕ) : B (k + 1) = hcomp (B k) a := Function.iterate_succ_apply' _ k _
  have hz (k : ℕ) : B k 0 = 0 := by
    induction k with
    | zero => exact ha0
    | succ k ih => rw [step, hcomp_zero ih]
  have transport (k : ℕ) : (PowerSeries.subst (egf a))^[k] (egf a) = egf (B k) := by
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', ih, subst_egf _ _ ha0, step]
  have h : egf a = PowerSeries.X * PowerSeries.subst (egf (B 5)) (PowerSeries.exp ℚ) := by
    rw [← transport 5, ← hA]
    exact heq
  rw [exp_eq_egf_one, subst_egf _ _ (hz 5), X_mul_egf] at h
  have hrec := egf_injective h
  have hmod2 : ∀ n : ℕ, a n % 2 = f0 n % 2 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp [ha0, f0]
      · have hprev : ∀ m ≤ n - 1, a m % 2 = f0 m % 2 := fun m hm => ih m (by omega)
        have toId {b : ℕ → ℤ} (hb : ∀ m ≤ n - 1, b m % 2 = f0 m % 2) :
            ∀ m ≤ n - 1, hcomp b a m % 2 = idSeq m % 2 := fun m hm =>
          (hcomp_congr_mod2 hb hprev m hm).trans (hcomp_f0_f0_mod2 m)
        have toF {b : ℕ → ℤ} (hb : ∀ m ≤ n - 1, b m % 2 = idSeq m % 2) :
            ∀ m ≤ n - 1, hcomp b a m % 2 = f0 m % 2 := fun m hm => by
          simpa only [hcomp_idSeq_left f0 rfl] using hcomp_congr_mod2 hb hprev m hm
        have hB : ∀ m ≤ n - 1, B 5 m % 2 = idSeq m % 2 :=
          toId (toF (toId (toF (toId hprev))))
        have hexp1 : hcomp (fun _ => 1) (B 5) (n - 1) % 2 = 1 := by
          have := hcomp_congr_mod2 (f1 := fun _ => 1) (f2 := fun _ => 1)
            (fun _ _ => rfl) hB (n - 1) le_rfl
          rwa [hcomp_idSeq_right] at this
        rw [congrFun hrec n, if_neg hn.ne', Int.mul_emod, hexp1, mul_one, Int.emod_emod]
        rfl
  intro n _
  have hm := hmod2 n
  simp only [f0] at hm
  rw [Int.odd_iff, Nat.odd_iff]
  omega
