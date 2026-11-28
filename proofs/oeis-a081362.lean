import OMAStatements.S_oeis_a081362
import Mathlib

open Filter Topology
namespace A081362Proof

noncomputable def fac (m : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk (fun j => if m ∣ j then (-1 : ℤ) ^ (j / m) else 0)

noncomputable def partialSeries (N : ℕ) : PowerSeries ℤ :=
  ∏ m ∈ Finset.Icc 1 N, fac m

noncomputable def c (N k : ℕ) : ℝ := (PowerSeries.coeff k (partialSeries N) : ℤ)

lemma fac_cancel {m : ℕ} (hm : 0 < m) : fac m * (1 + PowerSeries.X ^ m) = 1 := by
  ext k
  rw [mul_add, mul_one, map_add, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_one]
  simp only [fac, PowerSeries.coeff_mk]
  by_cases h : m ≤ k
  · rw [if_pos h, if_neg (by omega : k ≠ 0)]
    obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le h
    simp only [Nat.add_sub_cancel_left, Nat.dvd_add_right (dvd_refl m)]
    by_cases hd : m ∣ l
    · simp [hd, Nat.add_comm m l, Nat.add_div_right _ hm, pow_succ]
    · simp [hd]
  · rw [if_neg h, add_zero]
    by_cases hk : k = 0
    · simp [hk]
    · simp [hk, Nat.not_dvd_of_pos_of_lt (by omega : 0 < k) (by omega : k < m)]

lemma partial_cancel (N : ℕ) :
    partialSeries (N+1) * (1 + PowerSeries.X ^ (N+1)) = partialSeries N := by
  have e : Finset.Icc 1 (N+1) = insert (N+1) (Finset.Icc 1 N) :=
    (Finset.insert_Icc_right_eq_Icc_succ (by omega : 1 ≤ N+1)).symm
  rw [partialSeries, e, Finset.prod_insert (by simp), mul_comm (fac _), mul_assoc,
    fac_cancel (by omega), mul_one]
  rfl

lemma recurr (N k : ℕ) : c (N+1) k + (if N+1 ≤ k then c (N+1) (k-(N+1)) else 0) = c N k := by
  have h := congrArg (PowerSeries.coeff k) (partial_cancel N)
  rw [mul_add, mul_one, map_add, PowerSeries.coeff_mul_X_pow'] at h
  unfold c
  split_ifs at * <;> exact_mod_cast h

lemma stab {k N : ℕ} (h : k ≤ N) : c N k = c k k := by
  induction N, h using Nat.le_induction with
  | base => rfl
  | succ N h ih => have e := recurr N k
                   rw [if_neg (by omega), add_zero, ih] at e
                   exact e

lemma c_zero (k : ℕ) : c 0 k = if k = 0 then 1 else 0 := by
  simp [c, partialSeries, PowerSeries.coeff_one, apply_ite]

lemma boundAux (N k : ℕ) : |c N k| ≤ (2:ℝ)^(N+k) := by
  induction N generalizing k with
  | zero =>
    rw [c_zero]
    split_ifs with h
    · simp [h]
    · simp
  | succ N outer =>
    induction k using Nat.strong_induction_on with
    | h k inner =>
      have e := recurr N k
      have hpow : (2:ℝ)^(N+1+k) = 2^(N+k)*2 := by
        rw [show N+1+k = N+k+1 by omega, pow_succ]
      rw [hpow]
      by_cases hk : N+1 ≤ k
      · rw [if_pos hk] at e
        have d : k - (N+1) < k := by omega
        have hsmall := inner _ d
        have hp : (2:ℝ)^(N+1+(k-(N+1))) ≤ 2^(N+k) := by
          apply pow_le_pow_right₀ (by norm_num)
          omega
        rw [show c (N+1) k = c N k - c (N+1) (k-(N+1)) by linarith [e]]
        linarith [abs_sub (c N k) (c (N+1) (k-(N+1))), outer k]
      · rw [if_neg hk, add_zero] at e
        rw [e]
        linarith [outer k, pow_nonneg (by norm_num : (0:ℝ) ≤ 2) (N+k)]

lemma bound (N k : ℕ) : |c N k| ≤ (4:ℝ)^k := by
  have hh : (4:ℝ)^k = (2:ℝ)^(k+k) := by rw [pow_add, ← mul_pow]; norm_num
  rw [hh]
  by_cases hk : k ≤ N
  · rw [stab hk]
    exact boundAux k k
  · exact (boundAux N k).trans (pow_le_pow_right₀ (by norm_num) (by omega))

lemma summ (N : ℕ) {q : ℝ} (h0 : 0 ≤ q) (h4 : 4*q < 1) :
    Summable (fun k => c N k * q^k) := by
  apply (summable_geometric_of_lt_one (by positivity : 0 ≤ 4*q) h4).of_norm_bounded
  intro k
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg h0 _), mul_pow]
  exact mul_le_mul_of_nonneg_right (bound N k) (pow_nonneg h0 _)

lemma sum_recurr (N : ℕ) {q : ℝ} (h0 : 0 ≤ q) (h4 : 4*q < 1) :
    (∑' k, c (N+1) k * q^k) * (1 + q^(N+1)) = ∑' k, c N k * q^k := by
  let m := N+1
  let f (k : ℕ) := (if m ≤ k then c m (k-m) else 0) * q^k
  have hi : Function.Injective (fun k : ℕ => k+m) := by intro i j h; exact Nat.add_right_cancel h
  have hs : HasSum f ((∑' k, c m k * q^k) * q^m) := by
    apply (hi.hasSum_iff (fun k hk => ?_)).mp
    · simpa [Function.comp_def, f, pow_add, ← mul_assoc] using ((summ m h0 h4).hasSum.mul_right (q^m))
    · have h : ¬ m ≤ k := by
        intro h
        exact hk ⟨k-m, by dsimp; omega⟩
      simp [f, h]
  rw [mul_add, mul_one, ← hs.tsum_eq, ← (summ m h0 h4).tsum_add hs.summable]
  apply tsum_congr
  intro k
  simpa only [f, m, ← add_mul] using congrArg (fun t : ℝ => t * q^k) (recurr N k)

lemma sum_formula (N : ℕ) {q : ℝ} (h0 : 0 ≤ q) (h4 : 4*q < 1) :
    (∑' k, c N k * q^k) = ∏ n ∈ Finset.range N, (1+q^(n+1))⁻¹ := by
  induction N with
  | zero => simp [c_zero, ite_mul]
  | succ N ih =>
    have e := sum_recurr N h0 h4
    rw [ih] at e
    rw [Finset.prod_range_succ, ← div_eq_mul_inv]
    exact (eq_div_iff (by positivity)).mpr e

lemma transfer {q : ℝ} (h0 : 0 ≤ q) (h4 : 4*q < 1) :
    (∑' k, c k k * q^k) = ∏' n : ℕ, (1+q^(n+1))⁻¹ := by
  have hp : Summable (fun n : ℕ => q^(n+1)) := by
    simpa [pow_succ] using (summable_geometric_of_lt_one h0 (by linarith : q < 1)).mul_right q
  have hl := Real.hasProd_of_hasSum_log (f := fun n : ℕ => 1+q^(n+1))
    (fun n => by positivity) (Real.summable_log_one_add_of_summable hp).hasSum
  have ht := (hl.inv₀ (Real.exp_pos _).ne').multipliable.hasProd.tendsto_prod_nat
  have hlim : Tendsto (fun N => ∑' k, c N k * q^k) atTop (𝓝 (∑' k, c k k * q^k)) := by
    apply tendsto_tsum_of_dominated_convergence (summable_geometric_of_lt_one (by positivity : 0 ≤ 4*q) h4)
    · intro k
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop k] with N hN using by rw [stab hN]
    · apply Eventually.of_forall
      intro N k
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg h0 _), mul_pow]
      exact mul_le_mul_of_nonneg_right (bound N k) (pow_nonneg h0 _)
  simpa only [sum_formula _ h0 h4] using tendsto_nhds_unique (by simpa only [sum_formula _ h0 h4] using hlim) ht

lemma series_product :
    (∑' k : ℕ, (OMA.S_oeis_a081362.a k : ℝ) / Real.exp ((k:ℝ)*Real.pi)) =
    ∏' n : ℕ, (1+Real.exp (-Real.pi)^(n+1))⁻¹ := by
  have h4 : 4 * Real.exp (-Real.pi) < 1 := by
    rw [Real.exp_neg, ← div_eq_mul_inv, div_lt_one (Real.exp_pos _)]
    linarith [Real.add_one_lt_exp (ne_of_gt Real.pi_pos), Real.pi_gt_three]
  convert transfer (Real.exp_pos (-Real.pi)).le h4 using 1
  apply tsum_congr
  intro k
  simp only [c, partialSeries, fac, OMA.S_oeis_a081362.a, Real.exp_neg, Real.exp_nat_mul,
    div_eq_mul_inv, inv_pow]

end A081362Proof

namespace A081362Work

noncomputable def eulerF (q : ℂ) := ∏' n : ℕ, (1 - q ^ (n+1))

private lemma subprod {q : ℂ} (hq : ‖q‖ < 1) (i : ℕ → ℕ) (hi : Function.Injective i) :
    Multipliable fun k => 1 - q ^ (i k + 1) := by
  apply multipliable_one_add_of_summable (f := fun k => -q ^ (i k + 1))
  have h := ((summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one (norm_nonneg q) hq)).comp_injective hi
  simpa [Function.comp_def] using h

private lemma euler_split (q : ℂ) (hq : ‖q‖ < 1) :
    (∏' k : ℕ, (1 - q ^ (2*k+1))) * eulerF (q^2) = eulerF q := by
  have he := subprod hq (fun k => 2*k) (by intro a b h; dsimp at h; omega)
  have ho := subprod hq (fun k => 2*k+1) (by intro a b h; dsimp at h; omega)
  have h := tprod_even_mul_odd (f := fun n : ℕ => 1 - q ^ (n+1)) he ho
  simpa only [eulerF, ← pow_mul, Nat.mul_add, Nat.mul_one, Nat.add_assoc] using h

lemma euler_parity (q : ℂ) (hq : ‖q‖ < 1) :
    eulerF q * eulerF (-q) * eulerF (q^4) = eulerF (q^2) ^ 3 := by
  have hneg : ‖-q‖ < 1 := by simpa
  have hsq : ‖q^2‖ < 1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hq (by decide)
  have ha := euler_split q hq
  have hb := euler_split (-q) hneg
  have hc := euler_split (q^2) hsq
  have hc4 : (q^2)^2 = q^4 := by ring
  rw [hc4] at hc
  rw [neg_sq] at hb
  have hopen := subprod hq (fun k => 2*k) (by intro a b h; dsimp at h; omega)
  have hnegn := subprod hneg (fun k => 2*k) (by intro a b h; dsimp at h; omega)
  have hodd : (∏' k : ℕ, (1-q^(2*k+1))) * (∏' k : ℕ, (1-(-q)^(2*k+1))) =
      ∏' k : ℕ, (1 - (q^2)^(2*k+1)) := by
    rw [← hopen.tprod_mul hnegn]
    apply tprod_congr
    intro k
    rw [(show Odd (2*k+1) from ⟨k, rfl⟩).neg_pow]
    rw [← pow_mul, Nat.mul_comm 2 (2*k+1), pow_mul]
    ring
  rw [← ha, ← hb]
  calc
    _ = ((∏' k : ℕ, (1-q^(2*k+1))) * (∏' k : ℕ, (1-(-q)^(2*k+1)))) * eulerF (q^4) * eulerF (q^2)^2 := by ring
    _ = _ := by rw [hodd, hc]; ring

end A081362Work

namespace A081362Work

lemma realEulerProd (q : ℝ) (hq0 : 0 ≤ q) (hq : q < 1) :
    HasProd (fun n : ℕ => 1 - q^(n+1)) ‖eulerF (q:ℂ)‖ := by
  have hp : Summable (fun n : ℕ => q^(n+1)) := by
    simpa [pow_succ] using (summable_geometric_of_lt_one hq0 hq).mul_right q
  have hpos : ∀ n : ℕ, 0 < 1-q^(n+1) := fun n => sub_pos.mpr (pow_lt_one₀ hq0 hq (by omega))
  have hl : Summable (fun n : ℕ => Real.log (1-q^(n+1))) := by
    simpa [sub_eq_add_neg] using Real.summable_log_one_add_of_summable hp.neg
  have hr := Real.hasProd_of_hasSum_log hpos hl.hasSum
  have hc := hr.map Complex.ofRealHom.toMonoidHom Complex.continuous_ofReal
  have he : eulerF (q:ℂ) = (Real.exp (∑' n : ℕ, Real.log (1-q^(n+1))) : ℂ) := by
    simpa [eulerF, Function.comp_def] using hc.tprod_eq
  simpa [he, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hr

lemma euler_plus_real (q : ℝ) (hq0 : 0 ≤ q) (hq : q < 1) :
    ‖eulerF (q:ℂ)‖ = (∏' n : ℕ, (1 + q ^ (n+1))⁻¹) * ‖eulerF ((q:ℂ)^2)‖ := by
  have hp : Summable (fun n : ℕ => q^(n+1)) := by
    simpa [pow_succ] using (summable_geometric_of_lt_one hq0 hq).mul_right q
  have hl := Real.hasProd_of_hasSum_log (f := fun n : ℕ => 1+q^(n+1))
    (fun n => by positivity) (Real.summable_log_one_add_of_summable hp).hasSum
  have hi := (hl.inv₀ (Real.exp_pos _).ne').multipliable.hasProd
  have hb := hi.mul (realEulerProd (q^2) (sq_nonneg q) (pow_lt_one₀ hq0 hq (by decide)))
  rw [Complex.ofReal_pow] at hb
  apply (realEulerProd q hq0 hq).unique
  apply hb.congr_fun
  intro n
  have hn : 1+q^(n+1) ≠ 0 := by positivity
  rw [← pow_mul, mul_comm 2 (n+1), pow_mul]
  field_simp
  ring
end A081362Work

open Complex ModularForm UpperHalfPlane SlashInvariantForm MatrixGroups

namespace A081362Work

private lemma normCsqrt (z : ℂ) : ‖Complex.sqrt z‖ = ‖z‖ ^ (1 / 2 : ℝ) := by
  simpa [Complex.sqrt] using Complex.norm_cpow_real z (1/2)

private lemma etaNormS (z : ℂ) (hz : 0 < z.im) :
    ‖eta (-1 / z)‖ = ‖z‖ ^ (1 / 2 : ℝ) * ‖eta z‖ := by
  have he : ModularForm.eta (-1 / z) = (Complex.sqrt Complex.I)⁻¹ * (Complex.sqrt z * ModularForm.eta z) :=
    eta_comp_eq_csqrt_I_inv hz
  rw [he]
  simp [normCsqrt]

lemma eta_half_imag : ‖eta (Complex.I / 2)‖ =
    (2 : ℝ) ^ (1 / 2 : ℝ) * ‖eta (2 * Complex.I)‖ := by
  have h := etaNormS (2 * Complex.I) (by norm_num)
  have he : -1 / (2 * Complex.I) = Complex.I / 2 := by
    apply Complex.ext <;> norm_num [Complex.div_re, Complex.div_im, Complex.normSq_apply]
  simpa [he, norm_mul] using h

private lemma etaNormT (z : UpperHalfPlane) : ‖eta ((z : ℂ) + 1)‖ = ‖eta z‖ := by
  have he : Function.Periodic.qParam 1 ((z : ℂ) + 1) = Function.Periodic.qParam 1 z := by
    simp [Function.Periodic.qParam, mul_add, Complex.exp_add]
  simp only [ModularForm.eta, norm_mul, Function.Periodic.norm_qParam, Complex.add_im,
    Complex.one_im, add_zero, eta_q, he]

lemma eta_half_shift : ‖eta ((1 + Complex.I) / 2)‖ =
    (2 : ℝ) ^ (1 / 4 : ℝ) * ‖eta Complex.I‖ := by
  let z : UpperHalfPlane := ⟨-1 + Complex.I, by norm_num⟩
  have ht := etaNormT z
  change ‖eta (-1 + Complex.I + 1)‖ = ‖eta (-1 + Complex.I)‖ at ht
  rw [show -1 + Complex.I + 1 = Complex.I by ring] at ht
  have h := etaNormS (-1 + Complex.I) (by norm_num)
  have he : -1 / (-1 + Complex.I) = (1 + Complex.I) / 2 := by
    apply Complex.ext <;> norm_num [Complex.div_re, Complex.div_im, Complex.normSq_apply]
  have hn : ‖-1 + Complex.I‖ = (2 : ℝ) ^ (1/2 : ℝ) := by
    rw [Complex.norm_def, ← Real.sqrt_eq_rpow]
    norm_num [Complex.normSq_apply]
  rw [he, hn, ← ht, ← Real.rpow_mul (by norm_num), show (1 / 2 : ℝ) * (1 / 2) = 1 / 4 by norm_num] at h
  exact h

end A081362Work

namespace A081362Work



private lemma etaEulerAux (z : ℂ) : ‖ModularForm.eta z‖ =
    Real.exp (-2 * Real.pi * z.im / 24) * ‖eulerF (Function.Periodic.qParam 1 z)‖ := by
  rw [ModularForm.eta, norm_mul, Function.Periodic.norm_qParam]
  rfl

lemma euler_special_ratio
    (hp : let q : ℂ := (Real.exp (-Real.pi) : ℝ)
          eulerF q * eulerF (-q) * eulerF (q ^ 4) = eulerF (q ^ 2) ^ 3) :
    let q : ℂ := (Real.exp (-Real.pi) : ℝ)
    ‖eulerF (q^2)‖ ≠ 0 ∧ ‖eulerF q‖ = Real.exp (-(1/24 : ℝ) * Real.pi) * 2 ^ (1/8 : ℝ) * ‖eulerF (q^2)‖ := by
  let q : ℂ := (Real.exp (-Real.pi) : ℝ)
  let b := Real.exp (-(1/24 : ℝ) * Real.pi)
  let u := (2 : ℝ) ^ (1/8 : ℝ)
  change ‖eulerF (q^2)‖ ≠ 0 ∧ ‖eulerF q‖ = b * u * ‖eulerF (q^2)‖
  change eulerF q * eulerF (-q) * eulerF (q^4) = eulerF (q^2)^3 at hp
  have qh : Function.Periodic.qParam 1 (Complex.I / 2) = q := by
    simp only [Function.Periodic.qParam, ofReal_one, div_one, q, ofReal_exp, ofReal_neg]
    congr 1
    ring_nf
    simp
  have qs : Function.Periodic.qParam 1 ((1 + Complex.I) / 2) = -q := by
    simp only [Function.Periodic.qParam, ofReal_one, div_one, q, ofReal_exp, ofReal_neg]
    rw [show 2 * (Real.pi : ℂ) * Complex.I * ((1+Complex.I)/2) =
      (Real.pi : ℂ) * Complex.I + -(Real.pi : ℂ) by ring_nf; simp; ring,
      Complex.exp_add, Complex.exp_pi_mul_I]
    ring
  have qi : Function.Periodic.qParam 1 Complex.I = q^2 := by
    simp only [Function.Periodic.qParam, ofReal_one, div_one, q, ofReal_exp, ofReal_neg,
      ← Complex.exp_nat_mul]
    congr 1
    ring_nf
    simp
  have qt : Function.Periodic.qParam 1 (2 * Complex.I) = q^4 := by
    simp only [Function.Periodic.qParam, ofReal_one, div_one, q, ofReal_exp, ofReal_neg,
      ← Complex.exp_nat_mul]
    congr 1
    ring_nf
    simp
  have hh : ‖ModularForm.eta (Complex.I/2)‖ = b * ‖eulerF q‖ := by
    rw [etaEulerAux, qh]
    congr 2
    norm_num [Complex.div_im, Complex.normSq_apply] <;> ring
  have hs : ‖ModularForm.eta ((1+Complex.I)/2)‖ = b * ‖eulerF (-q)‖ := by
    rw [etaEulerAux, qs]
    congr 2
    norm_num [Complex.div_im, Complex.normSq_apply] <;> ring
  have hi : ‖ModularForm.eta Complex.I‖ = b^2 * ‖eulerF (q^2)‖ := by
    rw [etaEulerAux, qi]
    congr 1
    simp only [b, ← Real.exp_nat_mul, Complex.I_im]
    congr 1
    push_cast
    ring
  have ht : ‖ModularForm.eta (2*Complex.I)‖ = b^4 * ‖eulerF (q^4)‖ := by
    rw [etaEulerAux, qt]
    congr 1
    simp only [b, ← Real.exp_nat_mul, Complex.mul_im, Complex.I_im, Complex.I_re]
    congr 1
    norm_num <;> ring
  have hp' := congrArg norm hp
  simp only [norm_mul, norm_pow] at hp'
  have hid : ‖ModularForm.eta (Complex.I / 2)‖ *
      ‖ModularForm.eta ((1 + Complex.I) / 2)‖ * ‖ModularForm.eta (2 * Complex.I)‖ =
      ‖ModularForm.eta Complex.I‖ ^ 3 := by
    rw [hh, hs, ht, hi]
    linear_combination b^6 * hp'
  have p2 : u^2 = (2 : ℝ)^(1/4 : ℝ) := by
    unfold u
    rw [← Real.rpow_mul_natCast (by norm_num : 0 ≤ (2 : ℝ))]
    norm_num [u]
  have p4 : u^4 = (2 : ℝ)^(1/2 : ℝ) := by
    unfold u
    rw [← Real.rpow_mul_natCast (by norm_num : 0 ≤ (2 : ℝ))]
    norm_num [u]
  have s1 := eta_half_imag
  have s2 := eta_half_shift
  rw [← p4] at s1
  rw [← p2] at s2
  have hI : 0 < ‖ModularForm.eta Complex.I‖ := norm_pos_iff.mpr (ModularForm.eta_ne_zero (by simp))
  have hu : 0 < u := by unfold u; positivity
  rw [s2] at hid
  have prod : ‖ModularForm.eta (Complex.I / 2)‖ * u^2 * ‖ModularForm.eta (2 * Complex.I)‖ =
      ‖ModularForm.eta Complex.I‖^2 := by
    apply mul_right_cancel₀ hI.ne'
    linear_combination hid
  have sq : ‖ModularForm.eta (Complex.I / 2)‖^2 = (u * ‖ModularForm.eta Complex.I‖)^2 := by
    linear_combination ‖ModularForm.eta (Complex.I/2)‖ * s1 + u^2 * prod
  have he := (pow_left_inj₀ (norm_nonneg _) (mul_nonneg hu.le (norm_nonneg _)) (by decide : (2:ℕ) ≠ 0)).mp sq
  constructor
  · intro hzero
    rw [hi, hzero, mul_zero] at hI
    exact (lt_irrefl _ hI)
  rw [hh, hi] at he
  apply mul_left_cancel₀ (show b ≠ 0 from (Real.exp_pos _).ne')
  linear_combination he

end A081362Work

theorem OMA.solution : type_of% @OMA.S_oeis_a081362.main := by
  rw [A081362Proof.series_product]
  let q := Real.exp (-Real.pi)
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq : q < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr Real.pi_pos)
  have hqc : ‖(q:ℂ)‖ < 1 := by simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hq0]
  have hs := A081362Work.euler_special_ratio (A081362Work.euler_parity (q:ℂ) hqc)
  have hr := A081362Work.euler_plus_real q hq0 hq
  exact mul_right_cancel₀ hs.1 (hr.symm.trans hs.2)
