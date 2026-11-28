import OMAStatements.S_oeis_a124571
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.Real.GoldenRatio

namespace OMA.S_oeis_a124571
lemma subcritical_bound (x : ℝ) (hx : 0 < x) (hq : x * (1 + x) < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, (a n : ℝ) * x ^ n ≤ C := by
  let s (n : ℕ) : ℝ := (stage n).eval₂ (Nat.castRingHom ℝ) x
  let q := x * (1 + x)
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hq1 : q < 1 := hq
  have s0 : s 0 = x := by simp [s, stage]
  have ss (n : ℕ) : s (n + 1) = s n * (1 + x ^ n * s n) := by
    simp [s, stage, Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_pow]
    ring
  have sn (n : ℕ) : 0 ≤ s n := by
    induction n with
    | zero => rw [s0]; exact hx.le
    | succ n ih => rw [ss]; positivity
  have tu (n : ℕ) : x ^ n * s n ≤ x * q ^ n := by
    induction n with
    | zero => simp [s0]
    | succ n ih =>
      have small : x ^ n * s n ≤ x := ih.trans (by
        simpa using mul_le_mul_of_nonneg_left (pow_le_one₀ hq0 hq1.le (n := n)) hx.le)
      calc
        x ^ (n + 1) * s (n + 1) =
            (x ^ n * s n) * (x * (1 + x ^ n * s n)) := by rw [ss, pow_succ]; ring
        _ ≤ (x * q ^ n) * q := by
          apply mul_le_mul ih
          · exact mul_le_mul_of_nonneg_left (by linarith : 1 + x ^ n * s n ≤ 1 + x) hx.le
          · have := sn n; positivity
          · positivity
        _ = x * q ^ (n + 1) := by ring
  let K := x / (1 - q)
  have hK : 0 < K := div_pos hx (sub_pos.mpr hq1)
  have hKq : K * (1 - q) = x := div_mul_cancel₀ _ (ne_of_gt (sub_pos.mpr hq1))
  have bound (n : ℕ) : s n ≤ x * Real.exp (K * (1 - q ^ n)) := by
    induction n with
    | zero => simp [s0]
    | succ n ih =>
      have expb : 1 + x ^ n * s n ≤ Real.exp (x * q ^ n) := by
        linarith [tu n, Real.add_one_le_exp (x * q ^ n)]
      calc
        s (n + 1) = s n * (1 + x ^ n * s n) := ss n
        _ ≤ (x * Real.exp (K * (1 - q ^ n))) * Real.exp (x * q ^ n) := by
          apply mul_le_mul ih expb
          · have := sn n; positivity
          · positivity
        _ = x * Real.exp (K * (1 - q ^ (n + 1))) := by
          rw [mul_assoc, ← Real.exp_add]
          congr 2
          rw [pow_succ]
          linear_combination -(q ^ n) * hKq
  refine ⟨x * Real.exp K, by positivity, fun n => ?_⟩
  have coeff_bd : (a n : ℝ) * x ^ n ≤ s n := by
    dsimp [s, a]
    rw [Polynomial.eval₂_eq_sum_range' (n := max n (stage n).natDegree + 1)
      (Nat.castRingHom ℝ) (by omega) x]
    apply Finset.single_le_sum (f := fun i : ℕ => ((stage n).coeff i : ℝ) * x ^ i)
    · intro i hi; positivity
    · exact Finset.mem_range.mpr (by omega)
  apply coeff_bd.trans ((bound n).trans ?_)
  apply mul_le_mul_of_nonneg_left _ hx.le
  apply Real.exp_le_exp.mpr
  nlinarith [mul_nonneg hK.le (pow_nonneg hq0 n)]
end OMA.S_oeis_a124571

namespace OMA.S_oeis_a124571

lemma critical_eval (t : ℝ) (ht : t+t^2=1) (k : ℕ) :
    t^k * (stage k).eval₂ (Nat.castRingHom ℝ) t = t := by
  induction k with
  | zero => simp [stage]
  | succ k ih =>
    simp only [stage, Polynomial.eval₂_add, Polynomial.eval₂_mul,
      Polynomial.eval₂_pow, Polynomial.eval₂_X, pow_succ t k]
    calc
      _ = t * (t^k * (stage k).eval₂ (Nat.castRingHom ℝ) t) +
          t * (t^k * (stage k).eval₂ (Nat.castRingHom ℝ) t)^2 := by ring
      _ = t := by rw [ih]; nlinarith only [congrArg (t * ·) ht]

lemma large_monomial (r : ℝ) (hr : 0 < r) (_hr' : r < 1) (hrr : 1 < r+r^2) :
    ∃ K d : ℕ, 1 < ((stage K).coeff d : ℝ) * r^(d+K+2) := by
  let t := Real.goldenRatio-1
  have htpos : 0<t := by dsimp [t]; linarith [Real.one_lt_goldenRatio]
  have ht : t+t^2=1 := by dsimp [t]; nlinarith [Real.goldenRatio_sq]
  have htr : t < r := by
    by_contra! h
    have := mul_self_le_mul_self hr.le h
    nlinarith
  let q := t/r
  have hqpos : 0 < q := div_pos htpos hr
  have hq : q < 1 := (div_lt_one hr).2 htr
  have h1q : 0 < 1-q := sub_pos.mpr hq
  obtain ⟨K,hK⟩ := exists_pow_lt_of_lt_one (show 0<t*r^2*(1-q) by positivity) hq
  by_contra! h
  have major (d : ℕ) :
      ((stage K).coeff d : ℝ) * t^d * t^K * r^2 ≤ q^d * q^K := by
    have he := mul_le_mul_of_nonneg_right (h K d) (show 0 ≤ q^d*q^K by positivity)
    have xid : ((stage K).coeff d : ℝ) * t^d * t^K * r^2 =
        (((stage K).coeff d : ℝ) * r^(d+K+2)) * (q^d*q^K) := by
      simp only [q, div_pow, pow_add]
      field_simp
    rw [xid]
    simpa only [one_mul] using he
  let N := (stage K).natDegree+1
  have geomb : (∑ i ∈ Finset.range N, q^i) * (1-q) ≤ 1 := by
    rw [geom_sum_mul_neg]
    linarith only [pow_nonneg hqpos.le N]
  have sumBound : t*r^2 ≤ (∑ i ∈ Finset.range N, q^i) * q^K := by
    calc
      t*r^2 = ((stage K).eval₂ (Nat.castRingHom ℝ) t)*t^K*r^2 := by
        rw [mul_comm ((stage K).eval₂ _ _), critical_eval t ht K]
      _ = ∑ i ∈ Finset.range N, ((stage K).coeff i : ℝ) * t^i * t^K * r^2 := by
        rw [Polynomial.eval₂_eq_sum_range, Finset.sum_mul, Finset.sum_mul]
        rfl
      _ ≤ ∑ i ∈ Finset.range N, q^i*q^K := Finset.sum_le_sum (fun i _ => major i)
      _ = _ := Finset.sum_mul .. |>.symm
  have hh := mul_le_mul_of_nonneg_right sumBound h1q.le
  have hg := mul_le_mul_of_nonneg_right geomb (pow_nonneg hqpos.le K)
  nlinarith only [hh, hg, hK]

end OMA.S_oeis_a124571

namespace OMA.S_oeis_a124571

theorem coefficient_monotone (d : ℕ) : Monotone (fun k => (stage k).coeff d) := by
  apply monotone_nat_of_le_succ
  intro k
  simp only [stage, Polynomial.coeff_add]
  omega

theorem multiply_coefficients (j s t : ℕ) :
    (stage j).coeff s * (stage j).coeff t ≤ (stage (j+1)).coeff (s+t+j) := by
  rw [stage, Polynomial.coeff_add, Polynomial.coeff_X_pow_mul, pow_two, Polynomial.coeff_mul]
  apply Nat.le_trans _ (Nat.le_add_left _ _)
  exact Finset.single_le_sum (f := fun x : ℕ × ℕ =>
    (stage j).coeff x.1 * (stage j).coeff x.2) (fun x _ => Nat.zero_le _) (show (s,t) ∈ Finset.antidiagonal (s+t) by simp)

theorem delay_degree (j t n : ℕ) (hn : t+j+1 ≤ n) : (stage j).coeff t ≤ a n := by
  let k := n-t-1
  have hj : j ≤ k := by dsimp [k]; omega
  have h1 : 1 ≤ (stage k).coeff 1 := by
    simpa [stage] using coefficient_monotone 1 (Nat.zero_le k)
  calc
    (stage j).coeff t ≤ (stage k).coeff t := coefficient_monotone t hj
    _ ≤ (stage k).coeff t * (stage k).coeff 1 := by
      simpa using Nat.mul_le_mul_left ((stage k).coeff t) h1
    _ ≤ (stage (k+1)).coeff (t+1+k) := multiply_coefficients k t 1
    _ = (stage (k+1)).coeff n := by congr 1; dsimp [k]; omega
    _ ≤ a n := coefficient_monotone n (by dsimp [k]; omega)

theorem balanced_product (K d h M : ℕ) (hlo : 2^h ≤ M) (hhi : M ≤ 2^(h+1)) :
    ∃ t : ℕ, t + (K+h+1) + 1 = M*(d+K) + 2^(h+1) ∧
      ((stage K).coeff d)^M ≤ (stage (K+h+1)).coeff t := by
  induction h generalizing M with
  | zero =>
    norm_num at hlo hhi
    have hcase : M = 1 ∨ M = 2 := by omega
    rcases hcase with rfl | rfl
    · refine ⟨d, by ring, ?_⟩
      simpa using coefficient_monotone d (Nat.le_succ K)
    · refine ⟨d+d+K, by ring, ?_⟩
      simpa [pow_two] using multiply_coefficients K d d
  | succ h ih =>
    let m := M/2
    let l := M-m
    have hlo' : 2^h*2 ≤ M := by simpa only [pow_succ] using hlo
    have hhi' : M ≤ 2^(h+1)*2 := by simpa only [pow_succ (2:ℕ) (h+1)] using hhi
    have hm0 : 2^h ≤ m := by dsimp [m]; omega
    have hm1 : m ≤ 2^(h+1) := by dsimp [m]; omega
    have hl0 : 2^h ≤ l := by dsimp [l,m]; omega
    have hl1 : l ≤ 2^(h+1) := by dsimp [l,m]; omega
    obtain ⟨s, hs, hcs⟩ := ih m hm0 hm1
    obtain ⟨t, ht, hct⟩ := ih l hl0 hl1
    have hsum : M = m+l := by dsimp [l,m]; omega
    refine ⟨s+t+(K+h+1), ?_, ?_⟩
    · rw [hsum, Nat.add_mul, pow_succ (2:ℕ) (h+1)]
      omega
    · rw [hsum, pow_add]
      exact (Nat.mul_le_mul hcs hct).trans (multiply_coefficients (K+h+1) s t)

theorem coefficient_power_bound (K d M n : ℕ) (hM : 1 ≤ M) (hn : (d+K+2)*M ≤ n) :
    ((stage K).coeff d)^M ≤ a n := by
  let h := Nat.log 2 M
  have h₁ : 2^h ≤ M := Nat.pow_log_le_self 2 (by omega)
  have h₂ : M ≤ 2^(h+1) := (Nat.lt_pow_succ_log_self (by decide : 1 < 2) M).le
  obtain ⟨t,ht,hc⟩ := balanced_product K d h M h₁ h₂
  apply hc.trans (delay_degree _ _ _ ?_)
  have H : 2^(h+1) ≤ M*2 := by rw [pow_succ]; omega
  rw [ht]
  calc
    M*(d+K)+2^(h+1) ≤ M*(d+K)+M*2 := by omega
    _ = (d+K+2)*M := by ring
    _ ≤ n := hn

end OMA.S_oeis_a124571

open Filter
namespace OMA.A124571Analysis

theorem root_limit (a : ℕ → ℕ) (b : ℕ → ℕ → ℕ)
    (upper : ∀ r : ℝ, 0 < r → r + r^2 < 1 → ∃ C : ℝ, 0 < C ∧ ∀ n, (a n : ℝ) * r^n ≤ C)
    (seed : ∀ r : ℝ, 0 < r → r < 1 → 1 < r + r^2 → ∃ K d, 1 < (b K d : ℝ) * r^(d+K+2))
    (pack : ∀ K d M n, 1 ≤ M → (d+K+2)*M ≤ n → (b K d)^M ≤ a n) :
    Tendsto (fun n : ℕ => (a n : ℝ) ^ (1 / (n : ℝ))) atTop (nhds Real.goldenRatio) := by
  have hphi := Real.one_lt_goldenRatio
  have hsquare := Real.goldenRatio_sq
  apply tendsto_order.2
  constructor
  · intro l hl
    obtain ⟨v, hv₁, hvφ⟩ := exists_between (max_lt hl hphi)
    have hv : 1 < v := (le_max_right l 1).trans_lt hv₁
    have hlv : l < v := (le_max_left l 1).trans_lt hv₁
    obtain ⟨w, hvw, hwφ⟩ := exists_between hvφ
    have hw : 1 < w := hv.trans hvw
    have hwpos : 0 < w := by linarith
    have hvpos : 0 < v := by linarith
    have hquadratic : w^2 < w + 1 := by
      nlinarith [mul_pos (sub_pos.mpr hwφ) (show 0 < w + Real.goldenRatio - 1 by linarith)]
    have hcrit : 1 < 1 / w + (1 / w)^2 := by
      field_simp
      linarith
    obtain ⟨K, d, hB⟩ := seed (1 / w) (by positivity) ((div_lt_one hwpos).2 hw) hcrit
    let D := d + K + 2
    have hD : 0 < D := by dsimp [D]; omega
    have hpw : w ^ D < (b K d : ℝ) := by
      change 1 < (b K d : ℝ) * (1/w)^D at hB
      rw [div_pow, one_pow, ← div_eq_mul_one_div, lt_div_iff₀ (pow_pos hwpos D), one_mul] at hB
      exact hB
    have hvw' : 1 < w/v := (one_lt_div hvpos).2 hvw
    filter_upwards [(tendsto_pow_atTop_atTop_of_one_lt hvw').eventually_gt_atTop (w^D),
      eventually_ge_atTop D] with n hn hnD
    have hnpos : 0 < n := hD.trans_le hnD
    have hmul : D * (n / D) ≤ n := Nat.mul_div_le n D
    have hpack := pack K d (n/D) n (Nat.div_pos hnD hD) hmul
    have hest : w ^ (D*(n/D)) ≤ (a n : ℝ) := by
      rw [pow_mul]
      refine (pow_le_pow_left₀ (pow_nonneg hwpos.le _) hpw.le _).trans ?_
      exact_mod_cast hpack
    have hbound : w^n ≤ (a n : ℝ) * w^D := by
      calc w^n = w^(D*(n/D)) * w^(n%D) := by rw [← pow_add, Nat.div_add_mod]
           _ ≤ (a n : ℝ) * w^D := mul_le_mul hest (pow_le_pow_right₀ hw.le (Nat.mod_lt _ hD).le) (pow_nonneg hwpos.le _) (by positivity)
    rw [div_pow, lt_div_iff₀ (pow_pos hvpos n)] at hn
    have hlower : v ^ n < (a n : ℝ) := lt_of_mul_lt_mul_right (by nlinarith [hn.trans_le hbound] : v ^ n * w ^ D < (a n : ℝ) * w ^ D) (pow_nonneg hwpos.le _)
    have hh := Real.rpow_lt_rpow (pow_nonneg hvpos.le _) hlower (show 0 < 1 / (n : ℝ) by positivity)
    rw [one_div, Real.pow_rpow_inv_natCast hvpos.le hnpos.ne'] at hh
    simpa only [one_div] using hlv.trans hh
  · intro u hu
    obtain ⟨t, htφ, htu⟩ := exists_between hu
    have htpos : 0 < t := by linarith
    have hquadratic : t+1 < t^2 := by
      nlinarith [mul_pos (sub_pos.mpr htφ) (show 0 < t + Real.goldenRatio - 1 by linarith)]
    have hcrit : 1 / t + (1 / t)^2 < 1 := by
      field_simp
      linarith
    obtain ⟨C, _, hC⟩ := upper (1/t) (by positivity) hcrit
    have hratio : 1 < u/t := (one_lt_div htpos).2 htu
    filter_upwards [(tendsto_pow_atTop_atTop_of_one_lt hratio).eventually_gt_atTop C,
      eventually_gt_atTop (0 : ℕ)] with n hn hnpos
    have h := (hC n).trans_lt hn
    rw [div_pow, div_pow, one_pow, ← div_eq_mul_one_div, div_lt_div_iff_of_pos_right (pow_pos htpos n)] at h
    have hupos : 0 < u := htpos.trans htu
    have hh := Real.rpow_lt_rpow (by positivity : 0 ≤ (a n : ℝ)) h (show 0 < 1 / (n : ℝ) by positivity)
    rw [one_div, Real.pow_rpow_inv_natCast hupos.le hnpos.ne'] at hh
    simpa only [one_div] using hh

end OMA.A124571Analysis

open OMA.S_oeis_a124571

theorem OMA.solution : type_of% @OMA.S_oeis_a124571.main := by
  apply OMA.A124571Analysis.root_limit a (fun k d => (stage k).coeff d)
  · intro r hr h
    exact subcritical_bound r hr (by nlinarith)
  · exact large_monomial
  · exact coefficient_power_bound
