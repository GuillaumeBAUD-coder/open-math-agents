import FormalConjectures.ErdosProblems.«704»
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Erdős Problem 704

We formalize Raigorodskii's ternary-vector lower bound for the chromatic number
of Euclidean space. The polynomial evaluations over a prime field give
linearly independent vectors for each color, and a weighted count bounds
the number of reduced monomials. A Chebyshev factorial estimate provides
the prime interval for the truncated numerical constant. The logarithmic
endpoint comparisons use a finite series with a proved remainder bound.

Reference: A. M. Raigorodskii, *On the chromatic number of a space*,
<https://doi.org/10.1070/RM2000v055n02ABEH000281>.
-/

open Finset Filter Real Asymptotics
open ArithmeticFunction (vonMangoldt vonMangoldt_nonneg vonMangoldt_sum)
open scoped Topology Chebyshev

namespace OMA

private noncomputable def F (t : ℝ) : ℝ := t*log t-t

private theorem log_factorial_error (n : ℕ) :
    |log (n.factorial:ℝ) - F n| ≤ log (2*(n:ℝ)) + 1 := by
  cases n with
  | zero => simp [F]
  | succ n =>
    have hpos : 0 < ((n+1:ℕ):ℝ) := by positivity
    have hlog : 0 ≤ log (2*((n+1:ℕ):ℝ)) := log_nonneg (by norm_cast; omega)
    have ha := Stirling.log_stirlingSeq'_antitone (show 0 ≤ n by omega)
    simp only [Function.comp_apply] at ha
    rw [Stirling.stirlingSeq_one, log_div (by positivity) (by positivity), log_exp, log_sqrt (by norm_num)] at ha
    have hb := Stirling.log_stirlingSeq_bounded_by_constant n
    rw [Stirling.log_stirlingSeq_formula, log_div hpos.ne' (exp_pos 1).ne', log_exp] at ha hb
    have hh : 0 ≤ log (2:ℝ) := log_nonneg (by norm_num)
    have hh' := log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
    rw [abs_le]
    constructor <;> unfold F <;> nlinarith

private theorem log_factorial_approx {n : ℕ} {t M : ℝ} (hn : 1 ≤ n)
    (ht : (n:ℝ) ≤ t) (hnear : t ≤ n+1) (hM : t ≤ M) :
    |log (n.factorial:ℝ) - F t| ≤ 2 * log (2*M) + 2 := by
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have ht' : (1:ℝ) ≤ t := hn'.trans ht
  have hl : 0 ≤ log t := log_nonneg ht'
  have hl' : log t ≤ log (2*M) := log_le_log (by positivity) (by linarith)
  have hs : log (t/n) ≤ t/n-1 := log_le_sub_one_of_pos (by positivity)
  have hs' : (n:ℝ)*log (t/n) ≤ t-n := by
    have he := mul_le_mul_of_nonneg_left hs (show (0:ℝ) ≤ n by positivity)
    have hm : (n:ℝ)*(t/n-1) = t-n := by field_simp
    rw [hm] at he
    linarith
  have he : F t - F n ≤ log t := by
    rw [log_div (by positivity) (by positivity)] at hs'
    dsimp [F]
    nlinarith [mul_le_mul_of_nonneg_right (show t-(n:ℝ) ≤ 1 by linarith) hl]
  have he' : -(1:ℝ) ≤ F t - F n := by
    have hlm : 0 ≤ log (n:ℝ) := log_nonneg hn'
    have hlog := log_le_log (show 0 < (n:ℝ) by positivity) ht
    have ha := mul_le_mul ht hlog hlm (show 0 ≤ t by positivity)
    dsimp [F]
    linarith
  have hfn := abs_le.mp (log_factorial_error n)
  have hlogn : log (2*(n:ℝ)) ≤ log (2*M) := log_le_log (by positivity) (by linarith)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

private theorem log_factorial_sum (n : ℕ) :
    log (n.factorial:ℝ) = ∑ d ∈ Icc 1 n, ((n/d:ℕ):ℝ) * vonMangoldt d := by
  classical
  induction n with
  | zero => simp
  | succ n ih =>
    let S := Icc 1 (n+1)
    have hS : S = insert (n+1) (Icc 1 n) := by
      ext d
      simp [S]
      omega
    have hz : (∑ d ∈ S, ((n/d:ℕ):ℝ) * vonMangoldt d) = log (n.factorial:ℝ) := by
      rw [hS, sum_insert (by simp : n+1 ∉ Icc 1 n), Nat.div_eq_of_lt (Nat.lt_succ_self n)]
      simp [← ih]
    have hd : S.filter (fun d => d ∣ n+1) = (n+1).divisors := by
      ext d
      simp only [S, mem_filter, mem_Icc, Nat.mem_divisors]
      exact ⟨fun h => ⟨h.2, by omega⟩, fun h =>
        ⟨⟨Nat.pos_of_dvd_of_pos h.1 (by omega), Nat.le_of_dvd (by omega) h.1⟩, h.1⟩⟩
    have hs : (∑ d ∈ S, if d ∣ n+1 then vonMangoldt d else 0) = log (n+1:ℕ) := by
      rw [← sum_filter, hd, vonMangoldt_sum]
    rw [Nat.factorial_succ, Nat.cast_mul, log_mul (by positivity) (by positivity), ← hz, ← hs,
      ← sum_add_distrib]
    apply sum_congr rfl
    intro d hd'
    by_cases he : d ∣ n+1
    · rw [Nat.succ_div_of_dvd he]
      simp [he]
      ring
    · rw [Nat.succ_div_of_not_dvd he]
      simp [he]

private noncomputable def combo (n : ℕ) : ℝ :=
  log (n.factorial:ℝ) + log ((n/30:ℕ).factorial:ℝ) -
    log ((n/2:ℕ).factorial:ℝ) - log ((n/3:ℕ).factorial:ℝ) - log ((n/5:ℕ).factorial:ℝ)

private def coef (q : ℕ) : ℤ :=
  (q:ℤ) + ((q/30:ℕ):ℤ) - ((q/2:ℕ):ℤ) - ((q/3:ℕ):ℤ) - ((q/5:ℕ):ℤ)

private theorem coef_bounds (q : ℕ) :
    0 ≤ coef q ∧ coef q ≤ 1 ∧ (1 ≤ q → q ≤ 5 → coef q = 1) := by
  have hmod := Nat.mod_lt q (by decide : 0 < 30)
  have hper : coef q = coef (q % 30) := by
    have h := Nat.mod_add_div q 30
    unfold coef
    omega
  constructor
  · rw [hper]
    interval_cases h : q%30 <;> norm_num [coef]
  constructor
  · rw [hper]
    interval_cases h : q%30 <;> norm_num [coef]
  · intro hq hq'
    interval_cases q <;> norm_num [coef]

private theorem combo_sum (n : ℕ) :
    combo n = ∑ d ∈ Icc 1 n, (coef (n/d):ℝ) * vonMangoldt d := by
  have h (k : ℕ) (hk : 0 < k) : log ((n/k:ℕ).factorial:ℝ) =
      ∑ d ∈ Icc 1 n, (((n/d/k:ℕ):ℝ) * vonMangoldt d) := by
    rw [log_factorial_sum]
    have hs : Icc 1 (n/k) ⊆ Icc 1 n := Icc_subset_Icc_right (Nat.div_le_self _ _)
    rw [sum_subset hs]
    · apply sum_congr rfl
      intro d _
      rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, mul_comm k d]
    · intro d hd hd'
      have hlt : n/k < d := by simp only [mem_Icc] at hd hd'; omega
      rw [Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul,
        Nat.div_eq_of_lt hlt, Nat.cast_zero, zero_mul]
  have h1 := h 1 (by decide)
  simp only [Nat.div_one] at h1
  unfold combo
  rw [h1, h 30 (by decide), h 2 (by decide), h 3 (by decide), h 5 (by decide)]
  simp_rw [← sum_add_distrib, ← sum_sub_distrib, coef, Int.cast_sub, Int.cast_add,
    Int.cast_natCast]
  apply sum_congr rfl
  intro d _
  ring

private theorem combo_bounds (n : ℕ) :
    combo n ≤ ψ (n:ℝ) ∧ ψ (n:ℝ) ≤ combo n + ψ ((n/6:ℕ):ℝ) := by
  rw [combo_sum, Chebyshev.psi_eq_sum_Icc, Chebyshev.psi_eq_sum_Icc]
  simp only [Nat.floor_natCast]
  have hI (m : ℕ) :
      (∑ d ∈ Icc 0 m, vonMangoldt d) = ∑ d ∈ Icc 1 m, vonMangoldt d := by
    have he : Icc 0 m = insert 0 (Icc 1 m) := by ext d; simp; omega
    rw [he, sum_insert (by simp : 0 ∉ Icc 1 m)]
    simp
  rw [hI, hI]
  constructor
  · apply sum_le_sum
    intro d _
    have hd : (coef (n/d):ℝ) ≤ 1 := by exact_mod_cast (coef_bounds (n/d)).2.1
    simpa using mul_le_mul_of_nonneg_right hd (vonMangoldt_nonneg (n := d))
  · have hsub : Icc 1 (n/6) ⊆ Icc 1 n := Icc_subset_Icc_right (Nat.div_le_self _ _)
    have hpsi :
        (∑ d ∈ Icc 1 (n/6), vonMangoldt d) =
          ∑ d ∈ Icc 1 n, if d ≤ n/6 then vonMangoldt d else 0 := by
      rw [← sum_filter]
      congr 1
      ext d
      simp only [mem_Icc, mem_filter]
      have h := Nat.div_le_self n 6
      omega
    rw [hpsi, ← sum_add_distrib]
    apply sum_le_sum
    intro d hd
    have hd1 := (mem_Icc.mp hd).1
    have hd2 := (mem_Icc.mp hd).2
    by_cases hle : d ≤ n/6
    · have hd' : 0 ≤ (coef (n/d):ℝ) := by exact_mod_cast (coef_bounds (n/d)).1
      have hp := mul_nonneg hd' (vonMangoldt_nonneg (n := d))
      simp [hle]
      linarith
    · have hq₁ : 1 ≤ n/d := (Nat.le_div_iff_mul_le (by omega)).2 (by simpa)
      have hq₂ : n/d ≤ 5 := by
        have h₁ : n < d*6 := (Nat.div_lt_iff_lt_mul (by norm_num)).mp (by omega : n/6 < d)
        exact Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul (by omega)).2 (by simpa [mul_comm] using h₁))
      simp [hle, (coef_bounds (n/d)).2.2 hq₁ hq₂]

private noncomputable def chebC : ℝ :=
  log 2 / 2 + log 3 / 3 + log 5 / 5 - log 30 / 30

private theorem lt_chebC : log 2 < chebC := by
  have h23 : log (2:ℝ) < log 3 := log_lt_log (by norm_num) (by norm_num)
  have h45 : log (4:ℝ) < log 5 := log_lt_log (by norm_num) (by norm_num)
  have h4 : log (4:ℝ) = 2*log 2 := by rw [show (4:ℝ) = 2^2 by norm_num, log_pow]; norm_num
  have h30 : log (30:ℝ) = log 2 + log 3 + log 5 := by
    rw [show (30:ℝ) = 2*3*5 by norm_num, log_mul (by norm_num) (by norm_num),
      log_mul (by norm_num) (by norm_num)]
  unfold chebC
  linarith [log_pos (by norm_num : (1:ℝ) < 2)]

private theorem combo_approx {t : ℝ} (ht : 30 ≤ t) :
    |combo ⌊t⌋₊ - chebC*t| ≤ 10*log (2*t)+10 := by
  have h (d : ℕ) (hd : 1 ≤ d) (hd' : d ≤ 30) :
      |log ((⌊t⌋₊/d:ℕ).factorial:ℝ) - F (t/d)| ≤ 2*log (2*t)+2 := by
    have hd0 : (0:ℝ) < d := by exact_mod_cast (show 0 < d by omega)
    have hd1 : (1:ℝ) ≤ d := by exact_mod_cast hd
    have hd30 : (d:ℝ) ≤ 30 := by exact_mod_cast hd'
    have htd : 1 ≤ t/d := (le_div_iff₀ hd0).2 (by simpa using hd30.trans ht)
    rw [← Nat.floor_div_natCast]
    exact log_factorial_approx (Nat.le_floor (show ((1:ℕ):ℝ) ≤ t/d by simpa using htd)) (Nat.floor_le (by linarith))
      (Nat.lt_floor_add_one (t/d)).le (div_le_self (by linarith) hd1)
  have h1 := abs_le.mp (h 1 (by decide) (by decide))
  have h2 := abs_le.mp (h 2 (by decide) (by decide))
  have h3 := abs_le.mp (h 3 (by decide) (by decide))
  have h5 := abs_le.mp (h 5 (by decide) (by decide))
  have h30 := abs_le.mp (h 30 (by decide) (by decide))
  simp only [Nat.div_one, Nat.cast_one, div_one] at h1
  norm_num only [Nat.cast_ofNat] at h2 h3 h5 h30
  have heq : F t + F (t/30) - F (t/2) - F (t/3) - F (t/5) = chebC*t := by
    unfold F chebC
    rw [log_div (by linarith : t ≠ 0) (by norm_num : (30:ℝ) ≠ 0),
      log_div (by linarith : t ≠ 0) (by norm_num : (2:ℝ) ≠ 0),
      log_div (by linarith : t ≠ 0) (by norm_num : (3:ℝ) ≠ 0),
      log_div (by linarith : t ≠ 0) (by norm_num : (5:ℝ) ≠ 0)]
    ring
  unfold combo
  rw [← heq, abs_le]
  exact ⟨by linarith [h1.1, h30.1, h2.2, h3.2, h5.2],
    by linarith [h1.2, h30.2, h2.1, h3.1, h5.1]⟩

private theorem small_error {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in atTop, 50*(log (2*x)+1)+4*√x*log x ≤ δ*x := by
  have hl : log =o[atTop] sqrt := by
    rw [show sqrt = fun x => x ^ (1/2:ℝ) from funext sqrt_eq_rpow]
    exact isLittleO_log_rpow_atTop (by norm_num)
  have hbl := hl.bound (c := δ/200) (by positivity)
  filter_upwards [hbl, eventually_ge_atTop (1:ℝ), eventually_ge_atTop (200/δ)]
    with x hx hx1 hx2
  have hp : 0 < x := by linarith
  have hroot : 1 ≤ √x := (le_sqrt (by norm_num) hp.le).2 (by linarith)
  have hlog : 0 ≤ log x := log_nonneg hx1
  have hlog2 : log (2:ℝ) ≤ 1 := by linarith [log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)]
  simp only [Real.norm_eq_abs, abs_of_nonneg hlog, abs_of_nonneg (sqrt_nonneg _)] at hx
  have hmul := mul_le_mul_of_nonneg_left hx (sqrt_nonneg x)
  have he : √x * log x ≤ δ*x/200 := by
    nlinarith [sq_sqrt hp.le]
  have hle : log x ≤ √x*log x := by nlinarith
  have hlarge : 200 ≤ δ*x := by
    have := (div_le_iff₀ hδ).mp hx2
    simpa [mul_comm] using this
  rw [log_mul (by norm_num) hp.ne']
  linarith

private theorem combo_strips (x : ℝ) :
    ψ x - ψ (x / 6) + ψ (x / 7) - ψ (x / 10) ≤ combo ⌊x⌋₊ := by
  let n := ⌊x⌋₊
  have hs (m : ℕ) (hm : 1 ≤ m) :
      ψ (x / (m : ℝ)) =
        ∑ d ∈ Icc 1 n, if d ≤ n / m then vonMangoldt d else 0 := by
    rw [Chebyshev.psi_eq_sum_Icc, Nat.floor_div_natCast, ← sum_filter]
    have hzero : Icc 0 (n / m) = insert 0 (Icc 1 (n / m)) := by
      ext d
      by_cases hd : d = 0
      · subst d
        simp
      · simp [hd, show 1 ≤ d by omega]
    have hfilter : (Icc 1 n).filter (fun d ↦ d ≤ n / m) = Icc 1 (n / m) := by
      ext d
      simp only [mem_filter, mem_Icc]
      have := Nat.div_le_self n m
      omega
    change ∑ d ∈ Icc 0 (n / m), vonMangoldt d = _
    rw [hzero, sum_insert (by simp), hfilter]
    simp
  have hs1 := hs 1 (by norm_num)
  simp only [Nat.cast_one, div_one, Nat.div_one] at hs1
  have hs6 := hs 6 (by norm_num)
  have hs7 := hs 7 (by norm_num)
  have hs10 := hs 10 (by norm_num)
  norm_num only [Nat.cast_ofNat] at hs6 hs7 hs10
  rw [hs1, hs6, hs7, hs10, combo_sum]
  rw [← sum_sub_distrib, ← sum_add_distrib, ← sum_sub_distrib]
  apply sum_le_sum
  intro d hd
  change _ ≤ (coef (n / d) : ℝ) * vonMangoldt d
  obtain ⟨hd1, hd2⟩ := mem_Icc.mp hd
  have hd0 : 0 < d := by omega
  have hcut (m : ℕ) (hm : 0 < m) : d ≤ n / m ↔ m ≤ n / d := by
    rw [Nat.le_div_iff_mul_le hm, Nat.le_div_iff_mul_le hd0, mul_comm d m]
  have hq1 : 1 ≤ n / d := (Nat.le_div_iff_mul_le hd0).mpr (by simpa)
  have hnonneg := (coef_bounds (n / d)).1
  have hv := vonMangoldt_nonneg (n := d)
  simp only [if_pos hd2, hcut 6 (by norm_num), hcut 7 (by norm_num), hcut 10 (by norm_num)]
  rcases le_or_gt 6 (n / d) with h6 | h6
  · rcases le_or_gt 7 (n / d) with h7 | h7
    · rcases le_or_gt 10 (n / d) with h10 | h10
      · simp only [h6, h7, h10, if_true, sub_self, zero_add]
        positivity
      · have hc : coef (n / d) = 1 := by
          interval_cases hq : n / d <;> norm_num [coef]
        simp [h6, h7, h10.not_ge, hc]
    · simp only [h6, h7.not_ge, if_true, if_false, sub_self, zero_add]
      have h10 : ¬ 10 ≤ n / d := by omega
      simp only [h10, if_false, sub_zero]
      positivity
  · have h7 : ¬ 7 ≤ n / d := by omega
    have h10 : ¬ 10 ≤ n / d := by omega
    simp [h6.not_ge, h7, h10, (coef_bounds (n / d)).2.2 hq1 (by omega)]

private theorem narrow_prime_interval :
    ∀ᶠ N : ℝ in atTop, ∃ p : ℕ, p.Prime ∧ (451/2000 : ℝ)*N < p ∧
      (p:ℝ) ≤ (1319/5000 : ℝ)*N := by
  have hC : 0 < chebC := (log_pos (by norm_num : (1:ℝ)<2)).trans lt_chebC
  let δ := chebC / 10000
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hpsi_low : ∀ᶠ x : ℝ in atTop, (9999/10000 : ℝ) * chebC * x ≤ ψ x := by
    filter_upwards [small_error hδ, eventually_ge_atTop (30:ℝ)] with x he hx
    have ha := (abs_le.mp (combo_approx hx)).1
    have hb := (combo_bounds ⌊x⌋₊).1
    rw [← Chebyshev.psi_eq_psi_coe_floor] at hb
    have hs : 0 ≤ √x * log x := mul_nonneg (sqrt_nonneg _) (log_nonneg (by linarith))
    have hl : 0 ≤ log (2*x) := log_nonneg (by linarith)
    dsimp [δ] at he
    linarith
  have step {u v : ℝ}
      (hu : ∀ᶠ x : ℝ in atTop, ψ x ≤ u * chebC * x)
      (hv : 10001/10000 + (4/15 : ℝ)*u - (9999/10000)/7 ≤ v) :
      ∀ᶠ x : ℝ in atTop, ψ x ≤ v * chebC * x := by
    have hscale (q : ℝ) (hq : 0 < q) :
        Tendsto (fun x : ℝ ↦ x / q) atTop atTop :=
      by
        simp only [div_eq_mul_inv]
        simpa only [id_eq, mul_comm] using
          ((tendsto_const_mul_atTop_of_pos (inv_pos.mpr hq)).2
            (tendsto_id : Tendsto (id : ℝ → ℝ) atTop atTop))
    filter_upwards [small_error hδ, eventually_ge_atTop (30:ℝ),
      (hscale 6 (by norm_num)).eventually hu, (hscale 10 (by norm_num)).eventually hu,
      (hscale 7 (by norm_num)).eventually hpsi_low] with x he hx h6 h10 h7
    have ha := (abs_le.mp (combo_approx hx)).2
    have hb := combo_strips x
    have hs : 0 ≤ √x * log x := mul_nonneg (sqrt_nonneg _) (log_nonneg (by linarith))
    have hl : 0 ≤ log (2*x) := log_nonneg (by linarith)
    have hv' := mul_le_mul_of_nonneg_right hv (show 0 ≤ chebC*x by positivity)
    dsimp [δ] at he
    linarith
  have hpsi_up : ∀ᶠ x : ℝ in atTop, ψ x ≤ (11692/10000 : ℝ) * chebC * x := by
    have hstart : ∀ᶠ x : ℝ in atTop, ψ x ≤ (2:ℝ) * chebC * x := by
      have hd : 0 < chebC - log 2 := sub_pos.mpr lt_chebC
      filter_upwards [eventually_ge_atTop (1:ℝ), small_error hd] with x hx he
      have hb := Chebyshev.psi_le hx
      rw [show (4:ℝ) = 2^2 by norm_num, log_pow] at hb
      norm_num only [Nat.cast_ofNat] at hb
      have hs : 0 ≤ √x * log x := mul_nonneg (sqrt_nonneg _) (log_nonneg hx)
      have hl : 0 ≤ log (2*x) := log_nonneg (by linarith)
      linarith
    apply step (u := 11694/10000) _ (by norm_num)
    apply step (u := 11704/10000) _ (by norm_num)
    apply step (u := 11740/10000) _ (by norm_num)
    apply step (u := 11860/10000) _ (by norm_num)
    apply step (u := 12290/10000) _ (by norm_num)
    apply step (u := 13910/10000) _ (by norm_num)
    apply step (u := 2) hstart (by norm_num)
  let a : ℝ := 451/2000
  let b : ℝ := 1319/5000
  have hbpos : 0 < b := by norm_num [b]
  have hapos : 0 < a := by norm_num [a]
  have hm (t : ℝ) (ht : 0 < t) :
      Tendsto (fun x : ℝ ↦ t * x) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos ht).2 tendsto_id
  filter_upwards [(hm a hapos).eventually hpsi_up, (hm b hbpos).eventually hpsi_low,
    (hm b hbpos).eventually (small_error hδ), eventually_ge_atTop (30/b)] with N hu hl he hN
  have hNpos : 0 < N := by
    have : 0 < 30 / b := by positivity
    linarith
  have hNb : 30 ≤ b * N := by
    have := (div_le_iff₀ hbpos).mp hN
    linarith
  have hpθ := Chebyshev.psi_sub_theta_le (x := b*N) (by linarith)
  have hθp := Chebyshev.theta_le_psi (a*N)
  have hlog : 0 ≤ log (2*(b*N)) := log_nonneg (by linarith)
  have hd : θ (a*N) < θ (b*N) := by
    dsimp only [δ] at he
    have hc : 0 < chebC * N := mul_pos hC hNpos
    dsimp [a, b] at hu hl he hpθ hθp hlog ⊢
    linarith
  change ∃ p : ℕ, p.Prime ∧ a*N < p ∧ (p:ℝ) ≤ b*N
  by_contra! hnone
  have he : Nat.primesLE ⌊a*N⌋₊ = Nat.primesLE ⌊b*N⌋₊ := by
    ext p
    simp only [Nat.mem_primesLE]
    constructor
    · exact fun h ↦ ⟨h.1.trans (Nat.floor_mono (by
        exact mul_le_mul_of_nonneg_right (by norm_num [a,b]) hNpos.le)), h.2⟩
    · intro h
      have hp := (Nat.le_floor_iff (by positivity : 0 ≤ b*N)).mp h.1
      exact ⟨Nat.le_floor (le_of_not_gt (fun hh ↦ (hnone p h.2 hh).not_ge hp)), h.2⟩
  rw [Chebyshev.theta_eq_theta_coe_floor (a*N), Chebyshev.theta_eq_theta_coe_floor (b*N),
    Chebyshev.theta_eq_sum_primesLE_log, Chebyshev.theta_eq_sum_primesLE_log, he] at hd
  exact (lt_irrefl _) hd

end OMA

/- The ternary Frankl–Wilson construction for unit distance graphs. -/

open Finset Real MvPolynomial
open scoped EuclideanGeometry

namespace OMA

private abbrev Ternary (n : ℕ) := Fin n → Fin 3

private def zval (v : Fin 3) : ℤ := (v.val : ℤ) - 1

private def posSet {n : ℕ} (v : Ternary n) : Finset (Fin n) :=
  univ.filter fun i ↦ v i = 2

private def negSet {n : ℕ} (v : Ternary n) : Finset (Fin n) :=
  univ.filter fun i ↦ v i = 0

private def slice (n a b : ℕ) : Finset (Ternary n) :=
  univ.filter fun v ↦ (posSet v).card = a ∧ (negSet v).card = b

private def gap {n : ℕ} (a b : ℕ) (v w : Ternary n) : ℤ :=
  (a : ℤ) + b - ∑ i, zval (v i) * zval (w i)

private theorem square_sum {n a b : ℕ} {v : Ternary n} (hv : v ∈ slice n a b) :
    ∑ i, zval (v i) ^ 2 = (a : ℤ) + b := by
  have h := (mem_filter.mp hv).2
  calc
    _ = ∑ i : Fin n, ((if v i = 2 then (1 : ℤ) else 0) +
        (if v i = 0 then (1 : ℤ) else 0)) := by
      apply sum_congr rfl
      intro i _
      generalize v i = j
      fin_cases j <;> decide
    _ = _ := by
      rw [sum_add_distrib, ← sum_filter, ← sum_filter, sum_const, sum_const]
      change (posSet v).card • (1 : ℤ) + (negSet v).card • (1 : ℤ) = _
      simp [h.1, h.2]

private theorem diff_square_sum {n a b : ℕ} {v w : Ternary n} (hv : v ∈ slice n a b)
    (hw : w ∈ slice n a b) :
    ∑ i, (zval (v i) - zval (w i)) ^ 2 = 2 * gap a b v w := by
  calc
    _ = ∑ i : Fin n,
        ((zval (v i))^2 + (zval (w i))^2 - 2 * zval (v i) * zval (w i)) := by
      apply sum_congr rfl
      intro i _
      ring
    _ = _ := by
      simp_rw [mul_assoc]
      rw [sum_sub_distrib, sum_add_distrib, ← mul_sum, square_sum hv, square_sum hw, gap]
      ring

private theorem gap_pos {n a b : ℕ} {v w : Ternary n} (hv : v ∈ slice n a b)
    (hw : w ∈ slice n a b) (hne : v ≠ w) : 0 < gap a b v w := by
  have hd : ∃ i, v i ≠ w i := by
    by_contra! h
    exact hne (funext h)
  obtain ⟨i, hi⟩ := hd
  have hz : zval (v i) - zval (w i) ≠ 0 := by
    intro h
    apply hi
    apply Fin.ext
    dsimp [zval] at h
    omega
  have h := (Finset.single_le_sum (f := fun j ↦ (zval (v j) - zval (w j))^2)
    (fun j _ ↦ sq_nonneg _) (mem_univ i))
  rw [diff_square_sum hv hw] at h
  nlinarith [sq_pos_of_ne_zero hz]

private theorem gap_le {n a b : ℕ} {v w : Ternary n} (hv : v ∈ slice n a b)
    (hw : w ∈ slice n a b) : gap a b v w ≤ (a : ℤ) + 3 * b := by
  have hV := (mem_filter.mp hv).2.2
  have hW := (mem_filter.mp hw).2.2
  have h : -(2 : ℤ) * b ≤ ∑ i, zval (v i) * zval (w i) := calc
    _ = ∑ i : Fin n, ((if v i = 0 then (-1 : ℤ) else 0) +
        (if w i = 0 then (-1 : ℤ) else 0)) := by
      rw [sum_add_distrib, ← sum_filter, ← sum_filter, sum_const, sum_const]
      change -(2 : ℤ) * b = (negSet v).card • (-1 : ℤ) + (negSet w).card • (-1 : ℤ)
      simp [hV, hW]
      ring
    _ ≤ _ := by
      apply sum_le_sum
      intro i _
      generalize v i = j
      generalize w i = k
      fin_cases j <;> fin_cases k <;> decide
  unfold gap
  linarith

private noncomputable def point {n : ℕ} (p : ℕ) (v : Ternary n) :
    EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i ↦ (zval (v i) : ℝ) / √(2*(p : ℝ)))

private theorem gap_adj {n a b p : ℕ} (hp : 0 < p) {v w : Ternary n}
    (hv : v ∈ slice n a b) (hw : w ∈ slice n a b) (hgap : gap a b v w = p) :
    (Erdos704.unitDistanceGraph n).Adj (point p v) (point p w) := by
  have hpR : 0 < 2 * (p : ℝ) := by positivity
  have he : dist (point p v) (point p w) ^ 2 = 1 := by
    rw [PiLp.dist_sq_eq_of_L2]
    calc
      _ = (∑ i : Fin n, ((zval (v i) : ℝ) - (zval (w i) : ℝ)) ^ 2) / (2 * (p : ℝ)) := by
        rw [Finset.sum_div]
        apply sum_congr rfl
        intro i _
        rw [Real.dist_eq, sq_abs]
        change ((zval (v i) : ℝ) / √(2*(p : ℝ)) -
          (zval (w i) : ℝ) / √(2*(p : ℝ)))^2 = _
        rw [← sub_div, div_pow, sq_sqrt hpR.le]
      _ = 1 := by
        have hh : (∑ i : Fin n, ((zval (v i) : ℝ) - (zval (w i) : ℝ)) ^ 2) =
            2 * (p : ℝ) := by
          have hi : (∑ i, (zval (v i) - zval (w i)) ^ 2) = (2 : ℤ) * (p : ℤ) :=
            (diff_square_sum hv hw).trans (by rw [hgap])
          exact_mod_cast hi
        rw [hh, div_self hpR.ne']
  change dist (point p v) (point p w) = 1
  nlinarith [dist_nonneg (x := point p v) (y := point p w)]

private def shorten (t : ℕ) : Fin 3 :=
  if t = 0 then 0 else if t % 2 = 0 then 2 else 1

private theorem shorten_le (t : ℕ) : (shorten t).val ≤ t := by
  unfold shorten
  split_ifs <;> simp_all <;> omega

private theorem pow_shorten {p : ℕ} (r : Fin 3) (j : ℕ) :
    (zval r : ZMod p) ^ j = (zval r : ZMod p) ^ (shorten j).val := by
  fin_cases r
  · have hv : zval (0 : Fin 3) = -1 := by decide
    rw [show zval (Fin.mk 0 (by decide)) = -1 from hv]
    push_cast
    have h (i : ℕ) : (-1 : ZMod p) ^ i = (-1 : ZMod p) ^ (i % 2) := by
      conv_lhs => rw [← Nat.mod_add_div i 2, pow_add, pow_mul]
      simp
    by_cases j0 : j = 0
    · subst j
      rfl
    · by_cases hj : j % 2 = 0
      · rw [h]
        simp [shorten, j0, hj]
      · have hj1 : j % 2 = 1 := by omega
        rw [h]
        simp [shorten, j0, hj1]
  · have hv : zval (1 : Fin 3) = 0 := by decide
    rw [show zval (Fin.mk 1 (by decide)) = 0 from hv]
    push_cast
    by_cases h : j = 0
    · subst j
      simp [shorten]
    · by_cases hj : j % 2 = 0 <;> simp [shorten, h, hj, zero_pow]
  · have hv : zval (2 : Fin 3) = 1 := by decide
    rw [show zval (Fin.mk 2 (by decide)) = 1 from hv]
    simp

private def monomials (n d : ℕ) : Finset (Ternary n) :=
  univ.filter fun e ↦ ∑ i, (e i).val ≤ d

private theorem family_bound {n a b p : ℕ} (hp : p.Prime)
    (hpab : a+3*b < 2*p) (S : Finset (Ternary n)) (hS : S ⊆ slice n a b)
    (hgap : ∀ v ∈ S, ∀ w ∈ S, gap a b v w ≠ p) :
    S.card ≤ (monomials n (p-1)).card := by
  classical
  let _ : Fact p.Prime := ⟨hp⟩
  let val (x : Ternary n) (i : Fin n) : ZMod p := zval (x i)
  let L (x : Ternary n) : MvPolynomial (Fin n) (ZMod p) :=
    C ((a : ZMod p) + b) - ∑ i : Fin n, C (val x i) * X i
  let P (x : Ternary n) := 1 - L x ^ (p - 1)
  have hL (x : Ternary n) : (L x).totalDegree ≤ 1 := by
    unfold L
    refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
    · rw [totalDegree_C]
      omega
    · refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun i _ ↦ ?_)
      exact (totalDegree_mul _ _).trans (by simp)
  have hP (x : Ternary n) : (P x).totalDegree ≤ p-1 := by
    dsimp [P]
    apply (totalDegree_sub _ _).trans
    refine max_le (by simp) ((totalDegree_pow _ _).trans ?_)
    have h := Nat.mul_le_mul_right (p-1) (hL x)
    simpa [mul_comm] using h
  have evalP (x y : Ternary n) :
      (MvPolynomial.eval (val y)) (P x) = 1 - (gap a b x y : ZMod p) ^ (p-1) := by
    simp only [P, L, map_sub, map_one, map_pow, eval_C, map_sum, map_mul, eval_X,
      gap, Int.cast_sub, Int.cast_add, Int.cast_natCast, Int.cast_sum, Int.cast_mul]
    rfl
  let E (e : Ternary n) (y : S) : ZMod p :=
    ∏ i, val y.val i ^ (e i).val
  let B := (monomials n (p-1)).image E
  let W := Submodule.span (ZMod p) (B : Set (S → ZMod p))
  let f (x : S) (y : S) := (MvPolynomial.eval (val y.val)) (P x.val)
  have hW (x : S) : f x ∈ W := by
    have hterm (m : Fin n →₀ ℕ) (hm : m ∈ (P x.val).support) :
        (fun y : S ↦ ∏ i, val y.val i ^ m i) ∈ W := by
      let e : Ternary n := fun i ↦ shorten (m i)
      have he : e ∈ monomials n (p-1) := by
        refine mem_filter.mpr ⟨mem_univ _, ?_⟩
        refine (sum_le_sum fun i _ ↦ shorten_le (m i)).trans ?_
        rw [← Finsupp.sum_fintype m (fun _ e ↦ e) (fun _ ↦ rfl)]
        exact (le_totalDegree hm).trans (hP x.val)
      have hEq : (fun y : S ↦ ∏ i, val y.val i ^ m i) = E e := by
        funext y
        exact prod_congr rfl (fun i _ ↦ pow_shorten (y.val i) (m i))
      rw [hEq]
      exact Submodule.subset_span (mem_image.mpr ⟨e, he, rfl⟩)
    have heq : f x =
        ∑ m ∈ (P x.val).support,
          (P x.val).coeff m • (fun y : S ↦ ∏ i, val y.val i ^ m i) := by
      funext y
      rw [show f x y = MvPolynomial.eval (val y.val) (P x.val) from rfl, MvPolynomial.eval_eq']
      simp
    rw [heq]
    exact Submodule.sum_mem W fun m hm ↦ Submodule.smul_mem W _ (hterm m hm)
  have hdelta (x y : S) : f x y = if x = y then 1 else 0 := by
    change MvPolynomial.eval (val y.val) (P x.val) = _
    rw [evalP]
    by_cases heq : x = y
    · subst y
      have h := square_sum (hS x.property)
      simp_rw [pow_two] at h
      simp [gap, h, Nat.sub_ne_zero_of_lt hp.one_lt]
    · have hp1 : 0 < gap a b x.val y.val :=
        gap_pos (hS x.property) (hS y.property) (fun h ↦ heq (Subtype.ext h))
      have hp2 : gap a b x.val y.val < 2*(p : ℤ) := (gap_le (hS x.property) (hS y.property)).trans_lt
        (by exact_mod_cast hpab)
      have hneP : gap a b x.val y.val ≠ (p:ℤ) := hgap _ x.property _ y.property
      have hne : (gap a b x.val y.val : ZMod p) ≠ 0 := by
        intro hzero
        obtain ⟨z, hz⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hzero
        have hp0 : (0:ℤ) < p := by exact_mod_cast hp.pos
        have h0 : 0 < z := by nlinarith
        have h2 : z < 2 := by nlinarith
        have hz1 : z = 1 := by omega
        exact hneP (by simpa [hz1] using hz)
      simp [heq, ZMod.pow_card_sub_one_eq_one hne]
  have hf : f = Pi.basisFun (ZMod p) S := by
    funext x y
    rw [hdelta]
    simp [Pi.basisFun_apply, Pi.single_apply, eq_comm]
  let fw (x : S) : W := ⟨f x, hW x⟩
  have hind : LinearIndependent (ZMod p) fw := by
    apply LinearIndependent.of_comp W.subtype
    change LinearIndependent (ZMod p) f
    rw [hf]
    exact (Pi.basisFun _ _).linearIndependent
  have hc := (hind.fintype_card_le_finrank.trans
    (finrank_span_finset_le_card (R := ZMod p) B)).trans (card_image_le (s := monomials n (p-1)) (f := E))
  simpa using hc

private theorem color_ternary {n a b p k : ℕ} (hp : p.Prime) (hbound : a+3*b < 2*p)
    (h : (Erdos704.unitDistanceGraph n).Colorable k) :
    (slice n a b).card ≤ k * (monomials n (p-1)).card := by
  classical
  obtain ⟨c⟩ := h
  let U := slice n a b
  let col (v : Ternary n) := c (point p v)
  rw [show U.card = ∑ i : Fin k, (U.filter fun v ↦ col v = i).card from
      card_eq_sum_card_fiberwise (fun _ _ ↦ mem_univ _)]
  calc
    _ ≤ ∑ _ : Fin k, (monomials n (p-1)).card := by
      apply sum_le_sum
      intro i _
      apply family_bound hp hbound
      · exact filter_subset _ _
      · intro x hx y hy hxy
        exact c.map_rel (gap_adj hp.pos (mem_filter.mp hx).1 (mem_filter.mp hy).1 hxy)
          ((mem_filter.mp hx).2.trans (mem_filter.mp hy).2.symm)
    _ = _ := by simp

end OMA

namespace OMA

private theorem slice_card (n a b : ℕ) :
    (slice n a b).card = n.choose a * (n-a).choose b := by
  classical
  let U : Finset (Fin n) := univ
  let D := (U.powersetCard a).sigma (fun A ↦ (U \ A).powersetCard b)
  let encode (AB : Σ _ : Finset (Fin n), Finset (Fin n)) : Ternary n :=
    fun i ↦ if i ∈ AB.1 then 2 else if i ∈ AB.2 then 0 else 1
  have hpos (AB : Σ _ : Finset (Fin n), Finset (Fin n)) :
      posSet (encode AB) = AB.1 := by
    ext i
    by_cases hA : i ∈ AB.1 <;> by_cases hB : i ∈ AB.2 <;> simp [posSet, encode, hA, hB]
  have hneg (AB : Σ _ : Finset (Fin n), Finset (Fin n)) (hAB : AB ∈ D) :
      negSet (encode AB) = AB.2 := by
    have hdis : AB.2 ⊆ U \ AB.1 :=
      (mem_powersetCard.mp (mem_sigma.mp hAB).2).1
    ext i
    simp only [negSet, mem_filter, mem_univ, true_and, encode]
    by_cases hi : i ∈ AB.1
    · have : i ∉ AB.2 := fun h ↦ (mem_sdiff.mp (hdis h)).2 hi
      simp [hi, this]
    · by_cases hj : i ∈ AB.2 <;> simp [hi, hj]
  have hImage : D.image encode = slice n a b := by
    ext v
    simp only [mem_image]
    constructor
    · rintro ⟨AB, hAB, rfl⟩
      have hm := mem_sigma.mp hAB
      refine mem_filter.mpr ⟨mem_univ _, ?_⟩
      rw [hpos, hneg _ hAB]
      exact ⟨(mem_powersetCard.mp hm.1).2, (mem_powersetCard.mp hm.2).2⟩
    · intro hv
      have hv' := (mem_filter.mp hv).2
      refine ⟨⟨posSet v, negSet v⟩, ?_, ?_⟩
      · refine mem_sigma.mpr ⟨mem_powersetCard.mpr ⟨subset_univ _, hv'.1⟩,
          mem_powersetCard.mpr ⟨?_, hv'.2⟩⟩
        intro i hi
        simp only [negSet, mem_filter, mem_univ, true_and] at hi
        simp [U, posSet, hi]
      · funext i
        change (if i ∈ posSet v then 2 else if i ∈ negSet v then 0 else 1) = v i
        simp only [posSet, negSet, mem_filter, mem_univ, true_and]
        generalize v i = t
        fin_cases t <;> decide
  rw [← hImage, card_image_of_injOn]
  · rw [card_sigma]
    have hab : ∑ A ∈ U.powersetCard a, ((U \ A).powersetCard b).card =
        ∑ _A ∈ U.powersetCard a, (n-a).choose b := by
      apply sum_congr rfl
      intro A hA
      have hA' := mem_powersetCard.mp hA
      rw [card_powersetCard, card_sdiff_of_subset hA'.1, hA'.2]
      simp [U]
    rw [hab, sum_const, nsmul_eq_mul, card_powersetCard]
    simp [U]
  · intro AB hAB CD hCD he
    have h1 := congrArg posSet he
    have h2 := congrArg negSet he
    rw [hpos, hpos] at h1
    rw [hneg _ hAB, hneg _ hCD] at h2
    cases AB
    cases CD
    cases h1
    cases h2
    rfl

private theorem monomials_bound (n d : ℕ) {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1) :
    ((monomials n d).card : ℝ) * t ^ d ≤ (1+t+t^2)^n := by
  classical
  calc
    _ = ∑ _e ∈ monomials n d, t ^ d := by rw [sum_const, nsmul_eq_mul]
    _ ≤ ∑ e ∈ monomials n d, t ^ (∑ i, (e i).val) := by
      apply sum_le_sum
      intro e he
      exact pow_le_pow_of_le_one ht.le ht' (mem_filter.mp he).2
    _ ≤ ∑ e : Ternary n, t ^ (∑ i, (e i).val) :=
      sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ ↦ by positivity)
    _ = ∏ i : Fin n, ∑ j : Fin 3, t ^ j.val := by
      simp_rw [← Finset.prod_pow_eq_pow_sum]
      rw [Fintype.prod_sum]
    _ = _ := by
      simp only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, Nat.reduceAdd,
        pow_zero, pow_one, Fin.sum_univ_zero, add_zero, prod_const, card_fin, add_assoc]

end OMA

/- An entropy estimate for ternary vectors with a restricted monomial degree. -/

open Real Set

namespace OMA

private noncomputable def rpos (x : ℝ) : ℝ := x / 2 + 699 / 4000
private noncomputable def rneg (x : ℝ) : ℝ := x / 2 - 233 / 4000
private noncomputable def rzero (x : ℝ) : ℝ := 1 - rpos x - rneg x

private noncomputable def entropyDiff (t x : ℝ) : ℝ :=
  -(rpos x * log (rpos x)) - rneg x * log (rneg x) - rzero x * log (rzero x) +
    x * log t - log (1+t+t^2)

private theorem entropyDiff_concave (t : ℝ) :
    ConcaveOn ℝ (Icc (451/2000:ℝ) (1319/5000)) (entropyDiff t) := by
  refine ⟨convex_Icc _ _, ?_⟩
  intro x hx y hy a b ha hb hab
  have hpos (z : ℝ) (hz : z ∈ Icc (451/2000:ℝ) (1319/5000)) : 0 ≤ rpos z := by
    dsimp [rpos]
    linarith [hz.1]
  have hneg (z : ℝ) (hz : z ∈ Icc (451/2000:ℝ) (1319/5000)) : 0 ≤ rneg z := by
    dsimp [rneg]
    linarith [hz.1]
  have hzero (z : ℝ) (hz : z ∈ Icc (451/2000:ℝ) (1319/5000)) : 0 ≤ rzero z := by
    dsimp [rzero, rpos, rneg]
    linarith [hz.2]
  have hcomb (f : ℝ → ℝ) (hf : f (a*x+b*y) = a*f x+b*f y)
      (hfx : 0 ≤ f x) (hfy : 0 ≤ f y) :
      f (a*x+b*y) * log (f (a*x+b*y)) ≤
        a*(f x*log (f x))+b*(f y*log (f y)) := by
    rw [hf]
    exact convexOn_mul_log.2 hfx hfy ha hb hab
  have ha1 : rpos (a*x+b*y) = a*rpos x+b*rpos y := by unfold rpos; linear_combination -(699/4000)*hab
  have hb1 : rneg (a*x+b*y) = a*rneg x+b*rneg y := by unfold rneg; linear_combination (233/4000)*hab
  have hc1 : rzero (a*x+b*y) = a*rzero x+b*rzero y := by unfold rzero rpos rneg; linear_combination -(1767/2000)*hab
  have hp := hcomb rpos ha1 (hpos x hx) (hpos y hy)
  have hn := hcomb rneg hb1 (hneg x hx) (hneg y hy)
  have hz := hcomb rzero hc1 (hzero x hx) (hzero y hy)
  simp only [smul_eq_mul, entropyDiff]
  nlinarith [congrArg (fun s : ℝ ↦ s * log (1+t+t^2)) hab]

private noncomputable def logSeries (q : ℝ) (k : ℕ) : ℝ :=
  let y := q * 2^k
  let z := (y-1)/(y+1)
  2 * ∑ i ∈ Finset.range 10, z^(2*i+1)/(2*i+1)

private theorem log_cert {q l u : ℝ} {k : ℕ}
    (h1 : 1 ≤ q * 2^k) (h2 : q * 2^k ≤ 2)
    (hl : l ≤ logSeries q k - k * 0.6931471808)
    (hu : logSeries q k + 1/10^9 - k * 0.6931471803 ≤ u) :
    l ≤ log q ∧ log q ≤ u := by
  let y := q * (2:ℝ)^k
  have hy0 : 0 < y := by dsimp [y]; linarith
  have hq : 0 < q := pos_of_mul_pos_left hy0 (by positivity)
  let z := (y-1)/(y+1)
  have hz : 0 ≤ z := div_nonneg (by linarith) (by linarith)
  have hz3 : z ≤ 1/3 := by
    dsimp [z]
    apply (div_le_iff₀ (by linarith : 0 < y+1)).mpr
    linarith
  have hz1 : z < 1 := by linarith
  have hEq : (1+z)/(1-z) = y := by
    have hzNe : 1-z ≠ 0 := by linarith
    apply (div_eq_iff hzNe).mpr
    dsimp [z]
    field_simp
    ring
  have hl' := sum_range_le_log_div hz hz1 10
  have hu' := log_div_le_sum_range_add hz hz1 10
  rw [hEq] at hl' hu'
  have hlog : log y = log q + (k:ℝ)*log 2 := by
    dsimp [y]
    rw [log_mul hq.ne' (by positivity), log_pow]
  have htt : z^(2*10+1) / (1-z^2) ≤ (1/3:ℝ)^21/(1-(1/3:ℝ)^2) := by
    have hzz : z^2 ≤ (1/3:ℝ)^2 := pow_le_pow_left₀ hz hz3 2
    exact div_le_div₀ (by positivity) (pow_le_pow_left₀ hz hz3 _) (by norm_num) (by linarith)
  have ht : 2 * (z^(2*10+1) / (1-z^2)) ≤ 1/10^9 :=
    (mul_le_mul_of_nonneg_left htt (by norm_num)).trans (by norm_num)
  have hk : (0:ℝ) ≤ k := by positivity
  have hs : logSeries q k = 2 * ∑ i ∈ Finset.range 10, z^(2*i+1)/(2*i+1) := rfl
  constructor
  · linarith [mul_le_mul_of_nonneg_left log_two_lt_d9.le hk]
  · linarith [mul_le_mul_of_nonneg_left log_two_gt_d9.le hk]

private theorem numlog_1 : (21430458/100000000:ℝ) ≤ log (1239/1000) ∧
    log (1239/1000) ≤ 21430463/100000000 := by
  apply log_cert (k := 0) <;> norm_num [logSeries, Finset.sum_range_succ]

private theorem numlog_2 : (-124653244/100000000:ℝ) ≤ log (23/80) ∧
    log (23/80) ≤ -124653239/100000000 := by
  apply log_cert (k := 2) <;> norm_num [logSeries, Finset.sum_range_succ]

private theorem numlog_3 : (-290955460/100000000:ℝ) ≤ log (109/2000) ∧
    log (109/2000) ≤ -290955455/100000000 := by
  apply log_cert (k := 5) <;> norm_num [logSeries, Finset.sum_range_succ]

private theorem numlog_4 : (-41855037/100000000:ℝ) ≤ log (329/500) ∧
    log (329/500) ≤ -41855032/100000000 := by
  apply log_cert (k := 1) <;> norm_num [logSeries, Finset.sum_range_succ]

private theorem numlog_5 : (-160943794/100000000:ℝ) ≤ log (1/5) ∧
    log (1/5) ≤ -160943789/100000000 := by
  apply log_cert (k := 3) <;> norm_num [logSeries, Finset.sum_range_succ]

private theorem numlog_6 : (21511135/100000000:ℝ) ≤ log (31/25) ∧
    log (31/25) ≤ 21511140/100000000 := by
  apply log_cert (k := 0) <;> norm_num [logSeries, Finset.sum_range_succ]

private theorem numlog_7 : (-124219404/100000000:ℝ) ≤ log (231/800) ∧
    log (231/800) ≤ -124219399/100000000 := by
  apply log_cert (k := 2) <;> norm_num [logSeries, Finset.sum_range_succ]

private theorem numlog_8 : (-288687789/100000000:ℝ) ≤ log (223/4000) ∧
    log (223/4000) ≤ -288687784/100000000 := by
  apply log_cert (k := 5) <;> norm_num [logSeries, Finset.sum_range_succ]

private theorem numlog_9 : (-42235700/100000000:ℝ) ≤ log (1311/2000) ∧
    log (1311/2000) ≤ -42235695/100000000 := by
  apply log_cert (k := 1) <;> norm_num [logSeries, Finset.sum_range_succ]

private theorem numlog_10 : (-157021722/100000000:ℝ) ≤ log (26/125) ∧
    log (26/125) ≤ -157021717/100000000 := by
  apply log_cert (k := 3) <;> norm_num [logSeries, Finset.sum_range_succ]

private theorem numlog_11 : (22415422/100000000:ℝ) ≤ log (19551/15625) ∧
    log (19551/15625) ≤ 22415427/100000000 := by
  apply log_cert (k := 0) <;> norm_num [logSeries, Finset.sum_range_succ]

private theorem numlog_12 : (-121824080/100000000:ℝ) ≤ log (1183/4000) ∧
    log (1183/4000) ≤ -121824075/100000000 := by
  apply log_cert (k := 2) <;> norm_num [logSeries, Finset.sum_range_succ]

private theorem numlog_13 : (-276859673/100000000:ℝ) ≤ log (251/4000) ∧
    log (251/4000) ≤ -276859668/100000000 := by
  apply log_cert (k := 4) <;> norm_num [logSeries, Finset.sum_range_succ]

private theorem numlog_14 : (-44394612/100000000:ℝ) ≤ log (1283/2000) ∧
    log (1283/2000) ≤ -44394607/100000000 := by
  apply log_cert (k := 1) <;> norm_num [logSeries, Finset.sum_range_succ]

private theorem numlog_15 : (-151868357/100000000:ℝ) ≤ log (219/1000) ∧
    log (219/1000) ≤ -151868352/100000000 := by
  apply log_cert (k := 3) <;> norm_num [logSeries, Finset.sum_range_succ]

private theorem numlog_16 : (23662109/100000000:ℝ) ≤ log (1266961/1000000) ∧
    log (1266961/1000000) ≤ 23662114/100000000 := by
  apply log_cert (k := 0) <;> norm_num [logSeries, Finset.sum_range_succ]

private theorem numlog_17 : (-119484792/100000000:ℝ) ≤ log (1211/4000) ∧
    log (1211/4000) ≤ -119484787/100000000 := by
  apply log_cert (k := 2) <;> norm_num [logSeries, Finset.sum_range_succ]

private theorem numlog_18 : (-266283788/100000000:ℝ) ≤ log (279/4000) ∧
    log (279/4000) ≤ -266283783/100000000 := by
  apply log_cert (k := 4) <;> norm_num [logSeries, Finset.sum_range_succ]

private theorem numlog_19 : (-46601163/100000000:ℝ) ≤ log (251/400) ∧
    log (251/400) ≤ -46601158/100000000 := by
  apply log_cert (k := 1) <;> norm_num [logSeries, Finset.sum_range_succ]

private theorem numlog_20 : (-147840968/100000000:ℝ) ≤ log (57/250) ∧
    log (57/250) ≤ -147840963/100000000 := by
  apply log_cert (k := 3) <;> norm_num [logSeries, Finset.sum_range_succ]

private theorem numlog_21 : (24684755/100000000:ℝ) ≤ log (79999/62500) ∧
    log (79999/62500) ≤ 24684760/100000000 := by
  apply log_cert (k := 0) <;> norm_num [logSeries, Finset.sum_range_succ]

private theorem numlog_22 : (-118662419/100000000:ℝ) ≤ log (1221/4000) ∧
    log (1221/4000) ≤ -118662414/100000000 := by
  apply log_cert (k := 2) <;> norm_num [logSeries, Finset.sum_range_succ]

private theorem numlog_23 : (-262762298/100000000:ℝ) ≤ log (289/4000) ∧
    log (289/4000) ≤ -262762293/100000000 := by
  apply log_cert (k := 4) <;> norm_num [logSeries, Finset.sum_range_succ]

private theorem numlog_24 : (-47401168/100000000:ℝ) ≤ log (249/400) ∧
    log (249/400) ≤ -47401163/100000000 := by
  apply log_cert (k := 1) <;> norm_num [logSeries, Finset.sum_range_succ]

private theorem numlog_25 : (-146231187/100000000:ℝ) ≤ log (2317/10000) ∧
    log (2317/10000) ≤ -146231182/100000000 := by
  apply log_cert (k := 3) <;> norm_num [logSeries, Finset.sum_range_succ]

private theorem numlog_26 : (25105817/100000000:ℝ) ≤ log (128538489/100000000) ∧
    log (128538489/100000000) ≤ 25105822/100000000 := by
  apply log_cert (k := 0) <;> norm_num [logSeries, Finset.sum_range_succ]

private theorem numlog_27 : (-118204827/100000000:ℝ) ≤ log (6133/20000) ∧
    log (6133/20000) ≤ -118204822/100000000 := by
  apply log_cert (k := 2) <;> norm_num [logSeries, Finset.sum_range_succ]

private theorem numlog_28 : (-260843116/100000000:ℝ) ≤ log (1473/20000) ∧
    log (1473/20000) ≤ -260843111/100000000 := by
  apply log_cert (k := 4) <;> norm_num [logSeries, Finset.sum_range_succ]

private theorem numlog_29 : (-47851981/100000000:ℝ) ≤ log (6197/10000) ∧
    log (6197/10000) ≤ -47851976/100000000 := by
  apply log_cert (k := 1) <;> norm_num [logSeries, Finset.sum_range_succ]

private theorem endpoint_0 : log (1239/1000:ℝ) <
    entropyDiff (1/5) (4510/20000) := by
  have h0 := numlog_1.2
  have h1 := numlog_2.2
  have h2 := numlog_3.2
  have h3 := numlog_4.2
  have h4 := numlog_5.1
  have h5 := numlog_6.2
  norm_num [entropyDiff, rpos, rneg, rzero] at *
  linarith

private theorem endpoint_1 : log (1239/1000:ℝ) <
    entropyDiff (1/5) (4560/20000) := by
  have h0 := numlog_1.2
  have h1 := numlog_7.2
  have h2 := numlog_8.2
  have h3 := numlog_9.2
  have h4 := numlog_5.1
  have h5 := numlog_6.2
  norm_num [entropyDiff, rpos, rneg, rzero] at *
  linarith

private theorem endpoint_2 : log (1239/1000:ℝ) <
    entropyDiff (208/1000) (4560/20000) := by
  have h0 := numlog_1.2
  have h1 := numlog_7.2
  have h2 := numlog_8.2
  have h3 := numlog_9.2
  have h4 := numlog_10.1
  have h5 := numlog_11.2
  norm_num [entropyDiff, rpos, rneg, rzero] at *
  linarith

private theorem endpoint_3 : log (1239/1000:ℝ) <
    entropyDiff (208/1000) (4840/20000) := by
  have h0 := numlog_1.2
  have h1 := numlog_12.2
  have h2 := numlog_13.2
  have h3 := numlog_14.2
  have h4 := numlog_10.1
  have h5 := numlog_11.2
  norm_num [entropyDiff, rpos, rneg, rzero] at *
  linarith

private theorem endpoint_4 : log (1239/1000:ℝ) <
    entropyDiff (219/1000) (4840/20000) := by
  have h0 := numlog_1.2
  have h1 := numlog_12.2
  have h2 := numlog_13.2
  have h3 := numlog_14.2
  have h4 := numlog_15.1
  have h5 := numlog_16.2
  norm_num [entropyDiff, rpos, rneg, rzero] at *
  linarith

private theorem endpoint_5 : log (1239/1000:ℝ) <
    entropyDiff (219/1000) (5120/20000) := by
  have h0 := numlog_1.2
  have h1 := numlog_17.2
  have h2 := numlog_18.2
  have h3 := numlog_19.2
  have h4 := numlog_15.1
  have h5 := numlog_16.2
  norm_num [entropyDiff, rpos, rneg, rzero] at *
  linarith

private theorem endpoint_6 : log (1239/1000:ℝ) <
    entropyDiff (228/1000) (5120/20000) := by
  have h0 := numlog_1.2
  have h1 := numlog_17.2
  have h2 := numlog_18.2
  have h3 := numlog_19.2
  have h4 := numlog_20.1
  have h5 := numlog_21.2
  norm_num [entropyDiff, rpos, rneg, rzero] at *
  linarith

private theorem endpoint_7 : log (1239/1000:ℝ) <
    entropyDiff (228/1000) (5220/20000) := by
  have h0 := numlog_1.2
  have h1 := numlog_22.2
  have h2 := numlog_23.2
  have h3 := numlog_24.2
  have h4 := numlog_20.1
  have h5 := numlog_21.2
  norm_num [entropyDiff, rpos, rneg, rzero] at *
  linarith

private theorem endpoint_8 : log (1239/1000:ℝ) <
    entropyDiff (2317/10000) (5220/20000) := by
  have h0 := numlog_1.2
  have h1 := numlog_22.2
  have h2 := numlog_23.2
  have h3 := numlog_24.2
  have h4 := numlog_25.1
  have h5 := numlog_26.2
  norm_num [entropyDiff, rpos, rneg, rzero] at *
  linarith

private theorem endpoint_9 : log (1239/1000:ℝ) <
    entropyDiff (2317/10000) (5276/20000) := by
  have h0 := numlog_1.2
  have h1 := numlog_27.2
  have h2 := numlog_28.2
  have h3 := numlog_29.2
  have h4 := numlog_25.1
  have h5 := numlog_26.2
  norm_num [entropyDiff, rpos, rneg, rzero] at *
  linarith

private theorem entropy_interval {x : ℝ} (hx : x ∈ Icc (451/2000:ℝ) (1319/5000)) :
    ∃ t : ℝ, 1/5 ≤ t ∧ t ≤ 1/4 ∧ log (1239/1000:ℝ) ≤ entropyDiff t x := by
  have bound {lo hi t : ℝ} (hl : lo ∈ Icc (451/2000:ℝ) (1319/5000))
      (hh : hi ∈ Icc (451/2000:ℝ) (1319/5000))
      (hlo : log (1239/1000:ℝ) < entropyDiff t lo)
      (hhi : log (1239/1000:ℝ) < entropyDiff t hi)
      (hx' : x ∈ Icc lo hi) : log (1239/1000:ℝ) ≤ entropyDiff t x :=
    (le_min hlo.le hhi.le).trans ((entropyDiff_concave t).min_le_of_mem_Icc hl hh hx')
  rcases hx with ⟨hx1, hx2⟩
  by_cases h0 : x ≤ (4560/20000:ℝ)
  · refine ⟨1/5, by norm_num, by norm_num, ?_⟩
    exact bound (lo := 4510/20000) (hi := 4560/20000)
      (by norm_num) (by norm_num) endpoint_0 endpoint_1
      ⟨by linarith, by linarith⟩
  by_cases h1 : x ≤ (4840/20000:ℝ)
  · refine ⟨208/1000, by norm_num, by norm_num, ?_⟩
    exact bound (lo := 4560/20000) (hi := 4840/20000)
      (by norm_num) (by norm_num) endpoint_2 endpoint_3
      ⟨by linarith [h0], by linarith⟩
  by_cases h2 : x ≤ (5120/20000:ℝ)
  · refine ⟨219/1000, by norm_num, by norm_num, ?_⟩
    exact bound (lo := 4840/20000) (hi := 5120/20000)
      (by norm_num) (by norm_num) endpoint_4 endpoint_5
      ⟨by linarith [h1], by linarith⟩
  by_cases h3 : x ≤ (5220/20000:ℝ)
  · refine ⟨228/1000, by norm_num, by norm_num, ?_⟩
    exact bound (lo := 5120/20000) (hi := 5220/20000)
      (by norm_num) (by norm_num) endpoint_6 endpoint_7
      ⟨by linarith [h2], by linarith⟩
  · refine ⟨2317/10000, by norm_num, by norm_num, ?_⟩
    exact bound (lo := 5220/20000) (hi := 5276/20000)
      (by norm_num) (by norm_num) endpoint_8 endpoint_9
      ⟨by linarith [h3], by linarith⟩

end OMA

namespace OMA

private theorem F_derivative {x : ℝ} (hx : 0 < x) : HasDerivAt F (log x) x := by
  have he : 1 * log x + x*x⁻¹ - 1 = log x := by field_simp; ring
  rw [← he]
  exact ((hasDerivAt_id x).mul (hasDerivAt_log hx.ne')).sub (hasDerivAt_id x)

private theorem F_scale {n z : ℝ} (hn : 0 < n) (hz : 0 < z) :
    F (n*z) = n * (z * log z) + n*z*log n - n*z := by
  unfold F
  rw [log_mul hn.ne' hz.ne']
  ring

private theorem log_factorial_close {n k : ℕ} {t : ℝ}
    (hk : 1 ≤ k) (hkn : k ≤ n) (ht : t ∈ Set.Icc 1 (n : ℝ))
    (hclose : |(k : ℝ) - t| ≤ 3) :
    |log (k.factorial : ℝ) - F t| ≤ 4*log (2*(n:ℝ))+1 := by
  have hn : (1:ℝ) ≤ n := ht.1.trans ht.2
  have hknR : (k:ℝ) ∈ Set.Icc 1 (n:ℝ) := ⟨by exact_mod_cast hk, by exact_mod_cast hkn⟩
  have hlog : 0 ≤ log (2*(n:ℝ)) := log_nonneg (by linarith)
  have hfd (x : ℝ) (hx : x ∈ Set.Icc 1 (n:ℝ)) :
      HasDerivAt F (log x) x := F_derivative (by linarith [hx.1])
  have hd : |F (k:ℝ) - F t| ≤ log (2*(n:ℝ)) * |(k:ℝ) - t| := by
    simpa only [Real.norm_eq_abs] using
      (convex_Icc (1:ℝ) (n:ℝ)).norm_image_sub_le_of_norm_deriv_le
        (fun x hx ↦ (hfd x hx).differentiableAt)
        (fun x hx ↦ by
          rw [(hfd x hx).deriv, Real.norm_eq_abs, abs_of_nonneg (log_nonneg hx.1)]
          exact log_le_log (by linarith [hx.1]) (by linarith [hx.2]))
        ht hknR
  have he := log_factorial_error k
  have hc : log (2*(k:ℝ)) ≤ log (2*(n:ℝ)) :=
    log_le_log (by linarith [hknR.1]) (by linarith [hknR.2])
  have hs : 0 ≤ |(k:ℝ) - t| := abs_nonneg _
  have h := abs_add_le (log (k.factorial:ℝ) - F k) (F k - F t)
  rw [sub_add_sub_cancel] at h
  nlinarith [mul_le_mul_of_nonneg_left hclose hlog]

private theorem log_choose_ternary {n k : ℕ} (hk : k ≤ n) :
    log (n.choose k:ℝ) = log (n.factorial:ℝ) -
      log (k.factorial:ℝ) - log ((n-k).factorial:ℝ) := by
  have he := congrArg (fun a : ℕ => log (a:ℝ)) (Nat.choose_mul_factorial_mul_factorial hk)
  have hk' := Nat.choose_pos hk
  push_cast at he
  rw [log_mul (by positivity) (by positivity), log_mul (by positivity) (by positivity)] at he
  linarith

set_option maxHeartbeats 1000000 in
private theorem slice_beats_monomials (c : ℝ) (hc : 0 < c) (hc' : c < 1239/1000) :
    ∀ᶠ n : ℕ in atTop, ∀ p : ℕ, (451/2000 : ℝ)*(n:ℝ) < p →
      (p:ℝ) ≤ (1319/5000 : ℝ)*(n:ℝ) →
      ∃ a b : ℕ, a+3*b < 2*p ∧ c^n * ((monomials n (p-1)).card : ℝ) ≤ (slice n a b).card := by
  let δ := log (1239/1000 : ℝ) - log c
  have hδ : 0 < δ := sub_pos.mpr (log_lt_log hc hc')
  have hE := tendsto_natCast_atTop_atTop.eventually (small_error hδ)
  filter_upwards [hE, eventually_ge_atTop (100:ℕ)] with n hErr hn
  intro p hlo hhi
  have hnR : (100:ℝ) ≤ n := by exact_mod_cast hn
  have hnP : (0:ℝ) < n := by linarith
  let x : ℝ := (p:ℝ)/(n:ℝ)
  have hx : x ∈ Set.Icc (451/2000:ℝ) (1319/5000) :=
    ⟨(le_div_iff₀ hnP).mpr hlo.le, (div_le_iff₀ hnP).mpr hhi⟩
  have hxn : (n:ℝ)*x = p := by dsimp [x]; field_simp
  let A := (n:ℝ)*rpos x
  let B := (n:ℝ)*rneg x
  let Z := (n:ℝ)*rzero x
  have hA : (2:ℝ) ≤ A := by dsimp [A,rpos]; nlinarith [hx.1]
  have hB : (2:ℝ) ≤ B := by dsimp [B,rneg]; nlinarith [hx.1]
  have hZ : (2:ℝ) ≤ Z := by dsimp [Z,rzero,rpos,rneg]; nlinarith [hx.2]
  have hsum : A+B+Z = n := by simp only [A,B,Z,rzero]; ring
  let a := ⌊A⌋₊ - 1
  let b := ⌊B⌋₊
  have hfa : 2 ≤ ⌊A⌋₊ := Nat.le_floor (by exact hA)
  have hsa : a+1 = ⌊A⌋₊ := by dsimp [a]; omega
  have ha0 : 1 ≤ a := by omega
  have haR : (1:ℝ) ≤ a := by exact_mod_cast ha0
  have hfaR : (a : ℝ) + 1 = (⌊A⌋₊ : ℝ) := by exact_mod_cast hsa
  have haL : (a:ℝ)+1 ≤ A := by rw [hfaR]; exact Nat.floor_le (by linarith)
  have haU : A ≤ (a:ℝ)+2 := by linarith [Nat.lt_floor_add_one A]
  have hb0 : 1 ≤ b := Nat.le_floor (by
    norm_num only [Nat.cast_one]
    linarith)
  have hbR : (1:ℝ) ≤ b := by exact_mod_cast hb0
  have hbL : (b:ℝ) ≤ B := Nat.floor_le (by linarith)
  have hbU : B ≤ (b:ℝ)+1 := (Nat.lt_floor_add_one B).le
  have hpEq : A+3*B = 2*(p:ℝ) := by dsimp [A,B,rpos,rneg]; linear_combination 2*hxn
  have hc : a+3*b < 2*p := by
    exact_mod_cast (show (a:ℝ)+3*(b:ℝ) < 2*(p:ℝ) by linarith)
  have habn : a+b ≤ n := by exact_mod_cast (show (a:ℝ)+(b:ℝ) ≤ n by linarith)
  have han : a ≤ n := by omega
  have hbna : b ≤ n-a := by omega
  let z := n-a-b
  have hzEq : (z:ℝ) = (n:ℝ)-a-b := by
    dsimp [z]
    push_cast [Nat.cast_sub hbna, Nat.cast_sub han]
    rfl
  have hz0 : 1 ≤ z := by exact_mod_cast (show (1:ℝ) ≤ z by linarith)
  have hzn : z ≤ n := by dsimp [z]; omega
  have hbn : b ≤ n := by omega
  have hlog : 0 ≤ log (2*(n:ℝ)) := log_nonneg (by linarith)
  have hla := (abs_le.mp (log_factorial_close ha0 han (show A ∈ Set.Icc 1 (n:ℝ) from
    ⟨by linarith, by linarith⟩) (by rw [abs_le]; constructor <;> linarith))).2
  have hlb := (abs_le.mp (log_factorial_close hb0 hbn (show B ∈ Set.Icc 1 (n:ℝ) from
    ⟨by linarith, by linarith⟩) (by rw [abs_le]; constructor <;> linarith))).2
  have hlz := (abs_le.mp (log_factorial_close hz0 hzn (show Z ∈ Set.Icc 1 (n:ℝ) from
    ⟨by linarith, by linarith⟩) (by rw [abs_le]; constructor <;> linarith))).2
  have hln := (abs_le.mp (log_factorial_error n)).1
  have hpos : (0:ℝ) < (slice n a b).card := by
    rw [slice_card]
    exact_mod_cast Nat.mul_pos (Nat.choose_pos han) (Nat.choose_pos hbna)
  have hslice : log ((slice n a b).card : ℝ) = log (n.factorial:ℝ) -
      log (a.factorial:ℝ) - log (b.factorial:ℝ) - log (z.factorial:ℝ) := by
    rw [slice_card, Nat.cast_mul, log_mul (by exact_mod_cast (Nat.choose_pos han).ne')
      (by exact_mod_cast (Nat.choose_pos hbna).ne'), log_choose_ternary han, log_choose_ternary hbna]
    dsimp [z]
    ring
  have hF : F n - F A - F B - F Z =
      (n:ℝ)*(-(rpos x * log (rpos x)) - rneg x * log (rneg x) - rzero x * log (rzero x)) := by
    have hAp : 0 < rpos x := by dsimp [A] at hA; nlinarith
    have hBp : 0 < rneg x := by dsimp [B] at hB; nlinarith
    have hZp : 0 < rzero x := by dsimp [Z] at hZ; nlinarith
    dsimp only [A,B,Z]
    rw [F_scale hnP hAp, F_scale hnP hBp, F_scale hnP hZp]
    simp only [F, rzero]
    ring
  have hSlog :
      (n:ℝ)*(-(rpos x * log (rpos x)) - rneg x * log (rneg x) - rzero x * log (rzero x)) -
        (13*log (2*(n:ℝ))+4) ≤ log ((slice n a b).card : ℝ) := by
    rw [← hF, hslice]
    linarith
  obtain ⟨t, ht1, ht2, he⟩ := entropy_interval hx
  have ht : 0 < t := by linarith
  have ht' : t ≤ 1 := by linarith
  have hpc : c^n * (1+t+t^2)^n ≤ ((slice n a b).card:ℝ) * t^p := by
    apply (log_le_log_iff (by positivity) (by positivity)).mp
    rw [log_mul (by positivity) (by positivity), log_mul hpos.ne' (by positivity), log_pow,
      log_pow, log_pow]
    have hd := mul_le_mul_of_nonneg_left he hnP.le
    unfold entropyDiff at hd
    dsimp only [δ] at hErr
    have hroot : 0 ≤ √(n:ℝ) * log (n:ℝ) :=
      mul_nonneg (sqrt_nonneg _) (log_nonneg (by linarith))
    nlinarith [congrArg (fun z : ℝ ↦ z * log t) hxn]
  refine ⟨a,b,hc,?_⟩
  have hpow : t^p ≤ t^(p-1) := pow_le_pow_of_le_one ht.le ht' (Nat.sub_le _ _)
  have hm := monomials_bound n (p-1) ht ht'
  have hm' : ((monomials n (p-1)).card : ℝ) * t^p ≤ (1+t+t^2)^n :=
    (mul_le_mul_of_nonneg_left hpow (by positivity)).trans hm
  apply (mul_le_mul_iff_left₀ (show 0 < t^p by positivity)).mp
  rw [mul_assoc]
  exact (mul_le_mul_of_nonneg_left hm' (by positivity)).trans hpc

theorem raigorodskii_bound :
    ∀ c ∈ Set.Ioo (0 : ℝ) 1.239, ∀ᶠ n : ℕ in atTop,
      ∀ k : ℕ, (Erdos704.unitDistanceGraph n).Colorable k → c ^ n ≤ (k : ℝ) := by
  intro c hc
  have hp := tendsto_natCast_atTop_atTop.eventually narrow_prime_interval
  have hc' : c < (1239/1000 : ℝ) := by
    rw [← show (1.239 : ℝ) = 1239/1000 by norm_num]
    exact hc.2
  filter_upwards [hp, slice_beats_monomials c hc.1 hc'] with n hp hb
  obtain ⟨p, hp, hplo, hphi⟩ := hp
  obtain ⟨a,b,hab,hsize⟩ := hb p hplo hphi
  intro k hk
  have hs := color_ternary hp hab hk
  have hR : ((slice n a b).card : ℝ) ≤ (k:ℝ) * ((monomials n (p-1)).card:ℝ) := by
    exact_mod_cast hs
  have hm : 0 < (monomials n (p-1)).card := Finset.card_pos.mpr
    ⟨fun _ ↦ 0, by simp [monomials]⟩
  exact (mul_le_mul_iff_left₀ (by exact_mod_cast hm : (0:ℝ) < (monomials n (p-1)).card)).mp
    (hsize.trans hR)

end OMA

theorem OMA.solution : type_of% @Erdos704.erdos_704.variants.raigorodskii :=
  OMA.raigorodskii_bound