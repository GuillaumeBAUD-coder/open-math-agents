import FormalConjectures.ErdosProblems.«659»
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.LegendreSymbol.ZModChar
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic
import Mathlib.Data.Rat.Sqrt

/-! # Erdős 659: a rectangular lattice with few distances

Use the lattice in Moree and Osburn (2006) and Grayzel (2026), arXiv:2601.09102.
The global count is proved here using the mod-eight character and a weighted prime-power sum.
For each four-point subset, parity separates the distances; the remaining balanced
configuration contradicts the irrationality of the square root of two.
Credit: @JaviSoto. -/

/- Counting integers represented by x²+2y² using the real character of conductor eight. -/

/- Rankin's bound for harmonic sums of integers selected by an arithmetic condition. -/

open Filter
open scoped Topology BigOperators

namespace Grid659Harmonic

noncomputable def series (S : ℕ → Prop) [DecidablePred S] (s : ℝ) : ℝ :=
  ∑' m : ℕ, if S m then 1 / (m : ℝ) ^ s else 0

lemma rankin (S : ℕ → Prop) [DecidablePred S] (N : ℕ) (hN : 2 ≤ N) :
    ∑ m ∈ ((Finset.range (N + 1)).filter S), (m : ℝ)⁻¹ ≤
      Real.exp 1 * series S (1 + 1 / Real.log N) := by
  let t := 1 / Real.log N
  have hn : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hlog : 0 < Real.log N := Real.log_pos hn
  have ht : 0 < t := one_div_pos.mpr hlog
  let f (m : ℕ) := if S m then 1 / (m : ℝ) ^ (1 + t) else 0
  have hf (m : ℕ) : 0 ≤ f m := by dsimp [f]; split <;> positivity
  have hsum : Summable f := by
    apply Summable.of_nonneg_of_le hf _ (Real.summable_one_div_nat_rpow.mpr (by linarith : 1 < 1+t))
    intro m
    dsimp [f]
    split <;> first | exact le_rfl | positivity
  calc
    _ ≤ ∑ m ∈ ((Finset.range (N + 1)).filter S), Real.exp 1 * f m := by
      apply Finset.sum_le_sum
      intro m hm
      rw [Finset.mem_filter] at hm
      dsimp only [f]
      rw [if_pos hm.2]
      by_cases hm0 : m = 0
      · subst m
        simp [Real.zero_rpow (by linarith : 1 + t ≠ 0)]
      have hmp : 0 < (m : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hm0
      have hmN : (m : ℝ) ≤ N := by exact_mod_cast (Nat.lt_succ_iff.mp (Finset.mem_range.mp hm.1))
      have hpow : (m : ℝ) ^ t ≤ Real.exp 1 := by
        rw [Real.rpow_def_of_pos hmp, Real.exp_le_exp]
        dsimp [t]
        rw [mul_one_div, div_le_iff₀ hlog, one_mul]
        exact Real.log_le_log hmp hmN
      rw [Real.rpow_add hmp, Real.rpow_one, ← mul_div_assoc, mul_one,
        le_div_iff₀ (mul_pos hmp (Real.rpow_pos_of_pos hmp _))]
      simpa [← mul_assoc, hmp.ne'] using hpow
    _ = Real.exp 1 * ∑ m ∈ ((Finset.range (N + 1)).filter S), f m := (Finset.mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (hsum.sum_le_tsum _ fun i _ => hf i) (Real.exp_pos _).le

lemma harmonicOfEulerComparison (S : ℕ → Prop) [DecidablePred S]
    {K : ℝ} (hK : 0 < K)
    (hEuler : ∀ᶠ s : ℝ in 𝓝[>] 1,
      series S s ^ 2 ≤ K * ∑' m : ℕ, 1 / (m : ℝ) ^ s) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      ∑ m ∈ ((Finset.range (N + 1)).filter S), (m : ℝ)⁻¹ ≤ C * Real.sqrt (Real.log N) := by
  let s (N : ℕ) : ℝ := 1 + 1 / Real.log N
  have hl : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hs : Tendsto s atTop (𝓝[>] 1) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa [s, one_div] using
        (tendsto_const_nhds (x := (1 : ℝ))).add (tendsto_inv_atTop_zero.comp hl)
    · filter_upwards [hl.eventually_gt_atTop 0] with N hN
      exact lt_add_of_pos_right _ (one_div_pos.mpr hN)
  have hz := tendsto_sub_mul_tsum_nat_rpow.eventually_lt_const (show (1:ℝ) < 2 by norm_num)
  refine ⟨Real.exp 1 * Real.sqrt (2*K), by positivity, ?_⟩
  filter_upwards [hs.eventually hEuler, hs.eventually hz, eventually_ge_atTop 2] with N he hzN hn
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hz' : (∑' m : ℕ, 1 / (m : ℝ) ^ s N) ≤ 2 * Real.log N := by
    change (s N - 1) * (∑' m : ℕ, 1 / (m : ℝ) ^ s N) < 2 at hzN
    dsimp only [s] at hzN ⊢
    rw [add_sub_cancel_left, one_div, inv_mul_eq_div] at hzN
    simpa only [one_div] using ((div_lt_iff₀ hlog).mp hzN).le
  have hsq := he.trans (mul_le_mul_of_nonneg_left hz' hK.le)
  have hroot : series S (s N) ≤ Real.sqrt (2*K) * Real.sqrt (Real.log N) := by
    nlinarith [sq_nonneg (series S (s N) - Real.sqrt (2*K) * Real.sqrt (Real.log N)),
      Real.sq_sqrt (show 0 ≤ 2*K by positivity), Real.sq_sqrt hlog.le,
      mul_nonneg (Real.sqrt_nonneg (2*K)) (Real.sqrt_nonneg (Real.log N)),
      mul_pow (Real.sqrt (2*K)) (Real.sqrt (Real.log N)) 2]
  simpa [mul_assoc] using (rankin S N hn).trans
    (mul_le_mul_of_nonneg_left hroot (Real.exp_pos _).le)


noncomputable def chi8 : DirichletCharacter ℂ 8 := ZMod.χ₈'.ringHomComp (Int.castRingHom ℂ)

lemma chi8_ne_one : chi8 ≠ 1 := by
  intro h
  have hv := congrArg (fun χ : DirichletCharacter ℂ 8 => χ (-1)) h
  have hh : ZMod.χ₈' (-1) = -1 := by decide
  simp [chi8, MulChar.ringHomComp_apply, hh, MulChar.one_apply isUnit_one.neg] at hv
  norm_num at hv

lemma eventually_bounded_chi8 :
    ∀ᶠ s : ℝ in 𝓝[>] 1, ‖chi8.LFunction (s : ℂ)‖ ≤ ‖chi8.LFunction 1‖ + 1 := by
  have hc : ContinuousAt (fun s : ℝ => ‖chi8.LFunction (s : ℂ)‖) 1 :=
    ((chi8.differentiable_LFunction chi8_ne_one).continuous.comp Complex.continuous_ofReal).norm.continuousAt
  have hh := hc.continuousWithinAt (s := Set.Ioi 1)
  apply (hh.tendsto.eventually_lt_const _).mono fun _ hs => hs.le
  simp

lemma correction_le_zeta_two {s : ℝ} (hs : 1 < s) :
    (∑' m : ℕ, 1 / (m : ℝ) ^ (2 * s)) ≤ ∑' m : ℕ, 1 / (m : ℝ) ^ (2 : ℝ) := by
  apply Summable.tsum_le_tsum _ (Real.summable_one_div_nat_rpow.mpr (by linarith))
    (Real.summable_one_div_nat_rpow.mpr (by norm_num))
  intro m
  rcases m with _ | m
  · simp [Real.zero_rpow (show 2*s ≠ 0 by linarith)]
  · apply one_div_le_one_div_of_le (by positivity)
    apply Real.rpow_le_rpow_of_exponent_le
    · exact_mod_cast (show 1 ≤ m+1 by omega)
    · linarith

lemma localEulerMajorant (p : ℕ) (hp : p.Prime) {x : ℝ} (hx : 0 ≤ x) (hx1 : x < 1) :
    (if (p % 8 = 5 ∨ p % 8 = 7) then (1 - x^2)⁻¹ else (1 - x)⁻¹)^2 ≤
    (if p = 2 then 2 else 1) * (1-x)⁻¹ *
      (1 - (ZMod.χ₈' p : ℝ)*x)⁻¹ * (1-x^2)⁻¹ := by
  have ha : 0 < 1 - x := by linarith
  have hb : 0 < 1 + x := by linarith
  have hc : 0 < 1 - x^2 := by nlinarith [mul_pos ha hb]
  rw [ZMod.χ₈'_nat_eq_if_mod_eight]
  by_cases hp2 : p = 2
  · subst p
    norm_num
    field_simp
    nlinarith [mul_nonneg ha.le ha.le]
  · have hodd := hp.eq_two_or_odd.resolve_left hp2
    have hn2 : p % 2 ≠ 0 := by omega
    by_cases h : p % 8 = 5 ∨ p % 8 = 7
    · have hother : ¬ (p % 8 = 1 ∨ p % 8 = 3) := by omega
      simp [h, hp2, hn2, hother]
      field_simp
      ring_nf
      exact le_rfl
    · have hother : p % 8 = 1 ∨ p % 8 = 3 := by omega
      simp [h, hp2, hn2, hother]
      field_simp
      nlinarith [mul_nonneg (sq_nonneg x) (sq_nonneg (1-x))]

lemma harmonicOfFourFactors (S : ℕ → Prop) [DecidablePred S]
    (hprod : ∀ᶠ s : ℝ in 𝓝[>] 1,
      series S s ^ 2 ≤ 2 * (∑' m : ℕ, 1 / (m : ℝ) ^ (2*s)) *
        ‖chi8.LFunction (s : ℂ)‖ * ∑' m : ℕ, 1 / (m : ℝ) ^ s) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      ∑ m ∈ ((Finset.range (N + 1)).filter S), (m : ℝ)⁻¹ ≤ C * Real.sqrt (Real.log N) := by
  let M := (∑' m : ℕ, 1 / (m : ℝ) ^ (2 : ℝ)) + 1
  have hZ : 0 ≤ ∑' m : ℕ, 1 / (m : ℝ) ^ (2 : ℝ) := tsum_nonneg (fun _ => by positivity)
  have hM : 0 < M := by dsimp [M]; positivity
  apply harmonicOfEulerComparison S (K := 2 * M * (‖chi8.LFunction 1‖ + 1)) (by positivity)
  filter_upwards [hprod, eventually_bounded_chi8, self_mem_nhdsWithin] with s hp hL hs
  have hs' : 1 < s := hs
  have hcor : (∑' m : ℕ, 1 / (m : ℝ) ^ (2*s)) ≤ M :=
    (correction_le_zeta_two hs').trans (by dsimp [M]; linarith)
  exact hp.trans (by gcongr)


abbrev admissible (n : ℕ) := ∀ q ∈ n.primeFactors, (q % 8 = 5 ∨ q % 8 = 7) → Even (padicValNat q n)

lemma admissible_iff (n : ℕ) : admissible n ↔ ∀ q, (q % 8 = 5 ∨ q % 8 = 7) → Even (n.factorization q) := by
  constructor
  · intro h q hq
    by_cases hm : q ∈ n.primeFactors
    · rw [Nat.factorization_def _ (Nat.prime_of_mem_primeFactors hm)]
      exact h q hm hq
    · rw [Finsupp.notMem_support_iff.mp (show q ∉ n.factorization.support from hm)]
      simp
  · intro h q hm hq
    rw [← Nat.factorization_def _ (Nat.prime_of_mem_primeFactors hm)]
    exact h q hq

lemma admissible_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a.Coprime b) :
    admissible (a*b) ↔ admissible a ∧ admissible b := by
  simp only [admissible_iff, Nat.factorization_mul ha hb, Finsupp.add_apply]
  refine ⟨fun h => ⟨?_, ?_⟩, fun ⟨h₁,h₂⟩ q hq => (h₁ q hq).add (h₂ q hq)⟩
  · intro q hq
    by_cases hqa : q ∈ a.primeFactors
    · have hqb := Finset.disjoint_left.mp hab.disjoint_primeFactors hqa
      simpa [Finsupp.notMem_support_iff.mp (show q ∉ b.factorization.support from hqb)] using h q hq
    · simp [Finsupp.notMem_support_iff.mp (show q ∉ a.factorization.support from hqa)]
  · intro q hq
    by_cases hqb : q ∈ b.primeFactors
    · have hqa := Finset.disjoint_left.mp hab.disjoint_primeFactors.symm hqb
      simpa [Finsupp.notMem_support_iff.mp (show q ∉ a.factorization.support from hqa)] using h q hq
    · simp [Finsupp.notMem_support_iff.mp (show q ∉ b.factorization.support from hqb)]

lemma admissible_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    admissible (p^k) ↔ ((p % 8 = 5 ∨ p % 8 = 7) → Even k) := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp [admissible]
  simp [admissible, Nat.primeFactors_prime_pow hk hp, ← Nat.factorization_def _ hp,
    hp.factorization_self]

noncomputable def weight (s : ℝ) (n : ℕ) : ℝ := 1 / (n : ℝ)^s

lemma weight_mul (s : ℝ) (a b : ℕ) : weight s (a*b) = weight s a * weight s b := by
  simp [weight, Real.mul_rpow, Nat.cast_nonneg, mul_comm]

lemma weight_pow (s : ℝ) (p k : ℕ) : weight s (p^k) = (weight s p)^k := by
  induction k with
  | zero => simp [weight]
  | succ k ih => rw [pow_succ, weight_mul, ih, pow_succ]

lemma weight_lt_one {s : ℝ} (hs : 1 < s) {p : ℕ} (hp : p.Prime) :
    weight s p < 1 := by
  apply (div_lt_one (Real.rpow_pos_of_pos (by exact_mod_cast hp.pos) _)).mpr
  exact Real.one_lt_rpow (by exact_mod_cast hp.one_lt) (by linarith)

lemma evenGeom {x : ℝ} (hx : 0 ≤ x) (hx1 : x < 1) :
    (∑' k : ℕ, if Even k then x^k else 0) = (1-x^2)⁻¹ := by
  let f (k : ℕ) := if Even k then x^k else 0
  have hsum : HasSum (fun k : ℕ => f (2*k)) (1-x^2)⁻¹ := by
    simpa [f, pow_mul] using hasSum_geometric_of_lt_one (sq_nonneg x)
      (show x^2 < 1 by nlinarith [mul_pos (show 0 < 1-x by linarith) (show 0 < 1+x by linarith)])
  have hod : HasSum (fun k : ℕ => f (2*k+1)) 0 := by
    simp [f]
  simpa using (hsum.even_add_odd hod).tsum_eq

lemma admissibleEuler {s : ℝ} (hs : 1 < s) :
    HasProd (fun p : Nat.Primes => if (p.val % 8 = 5 ∨ p.val % 8 = 7) then (1-(weight s p)^2)⁻¹ else (1-weight s p)⁻¹)
      (series admissible s) := by
  let f (n : ℕ) := if admissible n then weight s n else 0
  have hsn : s ≠ 0 := by linarith
  have hz : f 0 = 0 := by simp [f, weight, Real.zero_rpow hsn]
  have h1 : f 1 = 1 := by simp [f, weight, admissible]
  have hm {a b : ℕ} (hab : a.Coprime b) : f (a*b) = f a * f b := by
    rcases eq_or_ne a 0 with rfl | ha
    · simp [hz]
    rcases eq_or_ne b 0 with rfl | hb
    · simp [hz]
    simp only [f, admissible_mul ha hb hab, weight_mul]
    split_ifs <;> simp_all
  have hsum : Summable (fun n : ℕ => ‖f n‖) := by
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ (Real.summable_one_div_nat_rpow.mpr hs)
    intro n
    by_cases h : admissible n
    · change ‖if admissible n then weight s n else 0‖ ≤ 1/(n:ℝ)^s
      rw [if_pos h, weight, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    · change ‖if admissible n then weight s n else 0‖ ≤ 1/(n:ℝ)^s
      rw [if_neg h, norm_zero]; positivity
  have hp := EulerProduct.eulerProduct_hasProd h1 @hm hsum hz
  apply hp.congr_fun
  intro p
  have hnon : 0 ≤ weight s p := by dsimp [weight]; positivity
  simp only [f, admissible_prime_pow p.prop, weight_pow]
  by_cases h : (p.val % 8 = 5 ∨ p.val % 8 = 7)
  · simp [h, evenGeom hnon (weight_lt_one hs p.prop)]
  · simp [h, tsum_geometric_of_lt_one hnon (weight_lt_one hs p.prop)]


lemma zetaProdWeight {s : ℝ} (hs : 1 < s) :
    HasProd (fun p : Nat.Primes => (1-weight s p)⁻¹) (∑' m : ℕ, 1/(m:ℝ)^s) := by
  have hsn : s ≠ 0 := by linarith
  have hsum : Summable (fun n : ℕ => ‖weight s n‖) := by
    simpa only [weight, Real.norm_eq_abs, abs_of_nonneg (div_nonneg zero_le_one (Real.rpow_nonneg (Nat.cast_nonneg _) _))] using
      (show Summable (fun n : ℕ => 1/(n:ℝ)^s) from Real.summable_one_div_nat_rpow.mpr hs)
  apply (EulerProduct.eulerProduct_hasProd (f := weight s) (by simp [weight])
    (fun {a b} _ => weight_mul s a b) hsum (by simp [weight, Real.zero_rpow hsn])).congr_fun
  intro p
  rw [show (fun k : ℕ => weight s (p.val ^ k)) = (fun k : ℕ => (weight s p)^k) by
    funext k; exact weight_pow s p k]
  exact (tsum_geometric_of_lt_one (by dsimp [weight]; positivity) (weight_lt_one hs p.prop)).symm

lemma weight_double (s : ℝ) (p : Nat.Primes) : weight (2*s) p = (weight s p)^2 := by
  have hpos : 0 < (p.val : ℝ) := by exact_mod_cast p.prop.pos
  simp [weight, two_mul, Real.rpow_add hpos, sq]

lemma chi8ProdWeight {s : ℝ} (hs : 1 < s) :
    HasProd (fun p : Nat.Primes => |(1 - (ZMod.χ₈' p : ℝ) * weight s p)⁻¹|)
      ‖chi8.LFunction (s : ℂ)‖ := by
  have hre : 1 < (s : ℂ).re := hs
  rw [DirichletCharacter.LFunction_eq_LSeries chi8 hre]
  apply (chi8.LSeries_eulerProduct_hasProd hre).norm.congr_fun
  intro p
  have hx : ((weight s p : ℝ) : ℂ) = (p.val : ℂ) ^ (-(s : ℂ)) := by
    rw [← Complex.ofReal_neg, ← Complex.ofReal_natCast,
      ← Complex.ofReal_cpow (Nat.cast_nonneg _), Real.rpow_neg (Nat.cast_nonneg _)]
    simp [weight]
  have hχ : (((ZMod.χ₈' p : ℤ) : ℝ) : ℂ) = chi8 p := by simp [chi8, MulChar.ringHomComp_apply]
  have hv : (((1 - (ZMod.χ₈' p : ℝ) * weight s p)⁻¹ : ℝ) : ℂ) =
      (1 - chi8 p * (p.val : ℂ)^(-(s : ℂ)))⁻¹ := by
    rw [Complex.ofReal_inv, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_one, hχ, hx]
  rw [← hv, Complex.norm_real, Real.norm_eq_abs]

lemma actualEulerComparison {s : ℝ} (hs : 1 < s) :
    series admissible s ^ 2 ≤ 2 * (∑' m : ℕ, 1 / (m : ℝ) ^ (2*s)) *
      ‖chi8.LFunction (s : ℂ)‖ * ∑' m : ℕ, 1 / (m : ℝ) ^ s := by
  let l (p : Nat.Primes) := if (p.val % 8 = 5 ∨ p.val % 8 = 7) then (1-(weight s p)^2)⁻¹ else (1-weight s p)⁻¹
  let b (p : Nat.Primes) : ℝ := if p.val = 2 then 2 else 1
  have htwo : HasProd b 2 := by
    apply (hasProd_ite_eq (⟨2, Nat.prime_two⟩ : Nat.Primes) (2:ℝ)).congr_fun
    intro p
    simp [b, Subtype.ext_iff]
  have he : HasProd l (series admissible s) := admissibleEuler hs
  have hright := ((htwo.mul (zetaProdWeight (s := 2*s) (by linarith))).mul
    (chi8ProdWeight hs)).mul (zetaProdWeight hs)
  rw [sq]
  apply le_of_tendsto_of_tendsto' (he.mul he) hright
  intro d
  apply Finset.prod_le_prod
  · intro p _
    exact mul_self_nonneg (l p)
  · intro p _
    let x := weight s p
    have hx : 0 ≤ x := by dsimp [x,weight]; positivity
    have hx1 : x < 1 := weight_lt_one hs p.prop
    have hb : 0 ≤ b p := by dsimp [b]; split <;> norm_num
    have hx2 : 0 < 1-x^2 := by nlinarith [mul_pos (show 0 < 1-x by linarith) (show 0 < 1+x by linarith)]
    change l p * l p ≤ b p * (1-weight (2*s) p)⁻¹ * |(1-(ZMod.χ₈' p : ℝ)*x)⁻¹| * (1-x)⁻¹
    rw [weight_double]
    calc
      _ ≤ b p * (1-x)⁻¹ * (1-(ZMod.χ₈' p : ℝ)*x)⁻¹ * (1-x^2)⁻¹ := by
        simpa only [l, b, x, sq] using localEulerMajorant p.val p.prop hx hx1
      _ ≤ b p * (1-x)⁻¹ * |(1-(ZMod.χ₈' p : ℝ)*x)⁻¹| * (1-x^2)⁻¹ := by
        gcongr
        exact le_abs_self _
      _ = _ := by ring

lemma harmonicActual :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      ∑ m ∈ ((Finset.range (N + 1)).filter admissible), (m : ℝ)⁻¹ ≤
        C * Real.sqrt (Real.log N) := by
  apply harmonicOfFourFactors
  filter_upwards [self_mem_nhdsWithin] with s hs using actualEulerComparison hs

end Grid659Harmonic

/- The sum of the full logarithms of prime powers up to X is O(X). -/

open Finset Chebyshev ArithmeticFunction

namespace OMA.Grid659Prime

theorem prime_power_log_sum_linear :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ,
      (∑ d ∈ Ioc 0 X with IsPrimePow d, Real.log (d : ℝ)) ≤ C * X := by
  obtain ⟨B, hB⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨Real.log 4 + 2 * |B| / Real.log 2, by positivity, ?_⟩
  intro X
  let A := Real.log X / Real.log 2
  have hA : 0 ≤ A := div_nonneg (Real.log_natCast_nonneg _) htwo.le
  let primeLog (d : ℕ) : ℝ := if d.Prime then Real.log d else 0
  have hcmp (d : ℕ) (hd : d ∈ Ioc 0 X) :
      (if IsPrimePow d then Real.log d else 0) ≤
        primeLog d + A * (vonMangoldt d - primeLog d) := by
    by_cases hp : d.Prime
    · simp [primeLog, hp, hp.isPrimePow, vonMangoldt_apply_prime hp]
    by_cases hq : IsPrimePow d
    · simp only [hq, if_true, primeLog, hp, if_false, sub_zero, zero_add]
      have hmin : Real.log 2 ≤ vonMangoldt d := by
        rw [vonMangoldt_apply, if_pos hq]
        apply Real.log_le_log (by norm_num)
        exact_mod_cast (Nat.minFac_prime hq.ne_one).two_le
      calc Real.log d ≤ Real.log X := Real.log_le_log (by exact_mod_cast (mem_Ioc.mp hd).1)
            (by exact_mod_cast (mem_Ioc.mp hd).2)
           _ = A * Real.log 2 := by dsimp [A]; field_simp
           _ ≤ _ := mul_le_mul_of_nonneg_left hmin hA
    · simp [primeLog, hp, hq, vonMangoldt_eq_zero_iff.mpr hq]
  have htheta : (∑ d ∈ Ioc 0 X, primeLog d) = theta X := by
    simp [Chebyshev.theta, sum_filter, primeLog]
  have hpsi : (∑ d ∈ Ioc 0 X, vonMangoldt d) = psi X := by simp [Chebyshev.psi]
  have hsum : (∑ d ∈ Ioc 0 X with IsPrimePow d, Real.log (d : ℝ)) ≤
      theta X + A * (psi X - theta X) := by
    rw [sum_filter, ← htheta, ← hpsi, ← sum_sub_distrib, mul_sum, ← sum_add_distrib]
    exact sum_le_sum hcmp
  have hx : 0 ≤ (X : ℝ) := Nat.cast_nonneg _
  have hlog : Real.log X ≤ 2 * Real.sqrt X := by
    linarith [Real.log_le_self (Real.sqrt_nonneg X), Real.log_sqrt hx]
  have habs : psi X - theta X ≤ |B| * Real.sqrt X :=
    (hB X).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.sqrt_nonneg _))
  calc
    _ ≤ theta X + A * (psi X - theta X) := hsum
    _ ≤ Real.log 4 * X + (2 * Real.sqrt X / Real.log 2) * (|B| * Real.sqrt X) := by
      refine add_le_add (theta_le_log4_mul_x hx) ?_
      exact (mul_le_mul_of_nonneg_left habs hA).trans
        (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hlog htwo.le) (by positivity))
    _ = _ := by
      ring_nf
      rw [Real.sq_sqrt hx]

end OMA.Grid659Prime

/- Strip the entire prime-power component from a represented norm, then sum over its complement. -/

namespace OMA.Grid659Weighted

open Finset Filter

private abbrev admissible (n : ℕ) :=
  ∀ q ∈ n.primeFactors, (q % 8 = 5 ∨ q % 8 = 7) → Even (padicValNat q n)

private theorem admissible_ordCompl {n : ℕ} (hn : admissible n) (p : ℕ) :
    admissible (ordCompl[p] n) := by
  intro q hq hmod
  have hpq := Nat.prime_of_mem_primeFactors hq
  rw [← Nat.factorization_def _ hpq, Nat.factorization_ordCompl]
  by_cases he : q = p
  · simp [he]
  · rw [Finsupp.erase_ne he]
    have hqn : q ∈ n.primeFactors := by
      have hne : n ≠ 0 := by rintro rfl; simp at hq
      exact Nat.mem_primeFactors.mpr ⟨hpq,
        (Nat.dvd_of_mem_primeFactors hq).trans (Nat.ordCompl_dvd n p), hne⟩
    rw [Nat.factorization_def _ hpq]
    exact hn q hqn hmod

private theorem component_sum (n : ℕ) :
    Real.log n = ∑ p ∈ n.primeFactors, Real.log (ordProj[p] n : ℕ) := by
  rw [Real.log_nat_eq_sum_factorization]
  simp [Finsupp.sum, Real.log_pow]

private abbrev Index := Σ _ : ℕ, ℕ

private def strip (x : Index) : Index := ⟨ordCompl[x.2] x.1, ordProj[x.2] x.1⟩

private theorem strip_injective {S : Finset ℕ} :
    Set.InjOn strip (S.sigma Nat.primeFactors) := by
  intro ⟨m,p⟩ hmp ⟨n,q⟩ hnq he
  have hp := (mem_sigma.mp hmp).2
  have hq := (mem_sigma.mp hnq).2
  have hc : ordCompl[p] m = ordCompl[q] n := congrArg (fun z : Index => z.1) he
  have hd : ordProj[p] m = ordProj[q] n := congrArg (fun z : Index => z.2) he
  have hmn : m = n := by
    rw [← Nat.ordProj_mul_ordCompl_eq_self m p, hc, hd, Nat.ordProj_mul_ordCompl_eq_self]
  have hpow {v r : ℕ} (h : r ∈ v.primeFactors) : (ordProj[r] v).minFac = r :=
    (Nat.prime_of_mem_primeFactors h).pow_minFac (Finsupp.mem_support_iff.mp h)
  have hpq := (hpow hp).symm.trans ((congrArg Nat.minFac hd).trans (hpow hq))
  subst n q
  rfl

private noncomputable def admissibleSet (N : ℕ) := (range (N+1)).filter admissible

private theorem component_bound (N : ℕ) :
    ∑ n ∈ admissibleSet N, Real.log n ≤
      ∑ m ∈ admissibleSet N, ∑ d ∈ (Ioc 0 (N/m)).filter IsPrimePow, Real.log d := by
  classical
  let S := admissibleSet N
  let A : Finset Index := S.sigma Nat.primeFactors
  let B : Finset Index := S.sigma (fun m => (Ioc 0 (N/m)).filter IsPrimePow)
  have hsub : A.image strip ⊆ B := by
    intro z hz
    obtain ⟨⟨n,p⟩, hnp, rfl⟩ := mem_image.mp hz
    obtain ⟨hn, hp⟩ := mem_sigma.mp hnp
    obtain ⟨hN, ha⟩ := mem_filter.mp hn
    have hle : n ≤ N := by simpa using hN
    have hn0 := (Nat.mem_primeFactors.mp hp).2.2
    have hcp := Nat.ordCompl_pos p hn0
    apply mem_sigma.mpr
    refine ⟨mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le ((Nat.ordCompl_le n p).trans hle)),
      admissible_ordCompl ha p⟩, mem_filter.mpr ⟨mem_Ioc.mpr ⟨Nat.ordProj_pos n p, ?_⟩, ?_⟩⟩
    · exact (Nat.le_div_iff_mul_le hcp).mpr ((Nat.ordProj_mul_ordCompl_eq_self n p).le.trans hle)
    · exact ⟨p, n.factorization p, Nat.prime_iff.mp (Nat.prime_of_mem_primeFactors hp),
        Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hp), rfl⟩
  calc
    _ = ∑ x ∈ A, Real.log (strip x).2 := by
      rw [Finset.sum_sigma]
      exact sum_congr rfl (fun n _ => component_sum n)
    _ = ∑ y ∈ A.image strip, Real.log y.2 :=
      (sum_image (f := fun y : Index => Real.log y.2) (strip_injective (S := S))).symm
    _ ≤ ∑ y ∈ B, Real.log y.2 := sum_le_sum_of_subset_of_nonneg hsub
      (fun y _ _ => Real.log_natCast_nonneg y.2)
    _ = _ := Finset.sum_sigma ..

theorem weighted_of_primePowers
    (hprime : ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ,
      (∑ d ∈ (Ioc 0 X).filter IsPrimePow, Real.log (d : ℝ)) ≤ C * X) :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ N : ℕ in atTop,
      let S := ((range (N + 1)).filter fun m =>
        ∀ q ∈ m.primeFactors, (q % 8 = 5 ∨ q % 8 = 7) → Even (padicValNat q m))
      (∑ m ∈ S, Real.log m) ≤ D * N * ∑ m ∈ S, (m : ℝ)⁻¹ := by
  obtain ⟨C, hC, h⟩ := hprime
  refine ⟨C, hC, Eventually.of_forall fun N => ?_⟩
  change _ ≤ _ * ∑ m ∈ admissibleSet N, (m : ℝ)⁻¹
  rw [Finset.mul_sum]
  apply (component_bound N).trans
  apply sum_le_sum
  intro m _
  calc
    _ ≤ _ := h (N/m)
    _ ≤ C * ((N:ℝ)/m) := mul_le_mul_of_nonneg_left Nat.cast_div_le hC.le
    _ = _ := by ring

end OMA.Grid659Weighted

/- Every pair of points in a square grid gives a sum of two squares. The count uses the two arithmetic estimates from the Erdős 604 reduction. -/

namespace OMA.Grid659Count

open Filter
open scoped BigOperators

/-- The reciprocal sum over numbers whose inert prime exponents are even. The term at zero
is zero by the convention for the reciprocal in ℝ. -/
def H1 : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
    (∑ m ∈ ((Finset.range (N + 1)).filter fun m =>
      ∀ q ∈ m.primeFactors, (q % 8 = 5 ∨ q % 8 = 7) → Even (padicValNat q m)), (m : ℝ)⁻¹) ≤
      C * Real.sqrt (Real.log N)

/-- Chebyshev's weighted counting estimate on the same multiplicative set. -/
def H2 : Prop :=
  ∃ D : ℝ, 0 < D ∧ ∀ᶠ N : ℕ in atTop,
    let S := ((Finset.range (N + 1)).filter fun m =>
      ∀ q ∈ m.primeFactors, (q % 8 = 5 ∨ q % 8 = 7) → Even (padicValNat q m))
    (∑ m ∈ S, Real.log m) ≤ D * N * ∑ m ∈ S, (m : ℝ)⁻¹

open Asymptotics

/-- Separate the integers at √N. Above the cutoff each term contributes at least log(N)/2. -/
private lemma count_from_log_sum (S : Finset ℕ) {N : ℕ} (hN : 2 ≤ N) :
    (S.card : ℝ) ≤ (Nat.sqrt N + 1 : ℕ) +
      2 * (∑ m ∈ S, Real.log m) / Real.log N := by
  let small := S.filter fun m => m ≤ Nat.sqrt N
  let large := S.filter fun m => ¬ m ≤ Nat.sqrt N
  have hsplit : small.card + large.card = S.card :=
    Finset.card_filter_add_card_filter_not _
  have hs : small.card ≤ Nat.sqrt N + 1 := by
    rw [← Finset.card_range (Nat.sqrt N + 1)]
    apply Finset.card_le_card
    intro m hm
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_filter.mp hm).2)
  have hl : (large.card : ℝ) * Real.log N ≤ 2 * ∑ m ∈ S, Real.log m := calc
    _ = ∑ _m ∈ large, Real.log N := by simp
    _ ≤ ∑ m ∈ large, 2 * Real.log m := by
      apply Finset.sum_le_sum
      intro m hm
      have hsq := Nat.sqrt_lt.mp (lt_of_not_ge (Finset.mem_filter.mp hm).2)
      have hreal : (N : ℝ) ≤ (m : ℝ) ^ 2 := by
        exact_mod_cast (show N ≤ m ^ 2 by simpa [sq] using hsq.le)
      have hnpos : 0 < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
      simpa only [Real.log_pow, Nat.cast_ofNat] using Real.log_le_log hnpos hreal
    _ = 2 * ∑ m ∈ large, Real.log m := (Finset.mul_sum ..).symm
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun i _ _ =>
        Real.log_natCast_nonneg i
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hl' := (le_div_iff₀ hlog).mpr hl
  rw [← hsplit, Nat.cast_add]
  exact add_le_add (by exact_mod_cast hs) hl'

/-- The two estimates for the multiplicative set imply the required counting bound. -/
lemma count_asymptotic (harmonic : H1) (weighted : H2) :
    (fun N : ℕ => (((Finset.range (N + 1)).filter fun m =>
      ∀ q ∈ m.primeFactors, (q % 8 = 5 ∨ q % 8 = 7) → Even (padicValNat q m)).card : ℝ)) =O[atTop]
      (fun N : ℕ => (N : ℝ) / (Real.log N).sqrt) := by
  obtain ⟨C, hC, hh⟩ := harmonic
  obtain ⟨D, hD, hw⟩ := weighted
  refine Asymptotics.isBigO_iff.mpr ⟨2 + 2 * D * C, ?_⟩
  filter_upwards [hh, hw, eventually_ge_atTop 2] with N hH hW hN
  let S := ((Finset.range (N + 1)).filter fun m =>
      ∀ q ∈ m.primeFactors, (q % 8 = 5 ∨ q % 8 = 7) → Even (padicValNat q m))
  change (∑ m ∈ S, Real.log m) ≤ D * N * ∑ m ∈ S, (m : ℝ)⁻¹ at hW
  change (∑ m ∈ S, (m : ℝ)⁻¹) ≤ C * (Real.log N).sqrt at hH
  have hn : 1 < (N : ℝ) := by exact_mod_cast (by omega : 1 < N)
  have hn' : (0 : ℝ) ≤ N := by positivity
  have hlog := Real.log_pos hn
  have hroot := Real.sqrt_pos.2 hlog
  have hroot2 := Real.sq_sqrt hlog.le
  have hW' : (∑ m ∈ S, Real.log m) ≤ (D * N) * (C * (Real.log N).sqrt) :=
    hW.trans (mul_le_mul_of_nonneg_left hH (by positivity))
  have hsmall : ((Nat.sqrt N + 1 : ℕ) : ℝ) * (Real.log N).sqrt ≤ 2 * N := by
    have hlogN : (Real.log N).sqrt ≤ Real.sqrt N :=
      Real.sqrt_le_sqrt (Real.log_le_self hn')
    have hOne : 1 ≤ Real.sqrt N := by simpa using Real.sqrt_le_sqrt hn.le
    calc
      _ ≤ (Real.sqrt N + Real.sqrt N) * Real.sqrt N := by
        push_cast
        exact mul_le_mul (add_le_add Real.nat_sqrt_le_real_sqrt hOne) hlogN
          hroot.le (by positivity)
      _ = _ := by nlinarith [Real.sq_sqrt hn']
  have hlarge : (2 * (∑ m ∈ S, Real.log m) / Real.log N) * (Real.log N).sqrt
        ≤ 2 * D * C * N := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hlog]
    calc
      _ ≤ (2 * ((D * N) * (C * (Real.log N).sqrt))) * (Real.log N).sqrt := by gcongr
      _ = _ := by linear_combination 2 * D * C * (N : ℝ) * hroot2
  simp only [Real.norm_eq_abs, Nat.abs_cast, abs_of_nonneg (div_nonneg hn' hroot.le)]
  rw [← mul_div_assoc, le_div_iff₀ hroot]
  calc
    (S.card : ℝ) * _ ≤ _ :=
      mul_le_mul_of_nonneg_right (count_from_log_sum S hN) hroot.le
    _ ≤ _ := by rw [add_mul]; linarith


end OMA.Grid659Count

/- Inert primes have even valuations in a norm from ℤ[√−2]. -/

namespace OMA.E659

private lemma divides_coordinates {p x y : ℕ} (hp : p.Prime) (hi : p % 8 = 5 ∨ p % 8 = 7)
    (h : p ∣ x^2 + 2*y^2) : p ∣ x ∧ p ∣ y := by
  let : Fact p.Prime := ⟨hp⟩
  have h2 : p ≠ 2 := by rintro rfl; norm_num at hi
  have heq := (ZMod.natCast_eq_zero_iff _ _).mpr h
  push_cast at heq
  have hy : (y : ZMod p) = 0 := by
    by_contra hy
    have hs : IsSquare (-2 : ZMod p) := by
      refine (isSquare_iff_exists_sq _).mpr ⟨(x : ZMod p)/y, ?_⟩
      rw [div_pow, eq_div_iff (pow_ne_zero _ hy)]
      linear_combination -heq
    have := (ZMod.exists_sq_eq_neg_two_iff h2).mp hs
    omega
  have hx : (x : ZMod p) = 0 := by simpa [hy] using heq
  exact ⟨(ZMod.natCast_eq_zero_iff _ _).mp hx, (ZMod.natCast_eq_zero_iff _ _).mp hy⟩

theorem even_valuation_of_norm {p n : ℕ} (hp : p.Prime) (hi : p % 8 = 5 ∨ p % 8 = 7)
    (hn : ∃ x y : ℕ, n = x^2 + 2*y^2) : Even (padicValNat p n) := by
  let : Fact p.Prime := ⟨hp⟩
  induction n using Nat.strong_induction_on with
  | h n ih =>
    obtain ⟨x, y, heq⟩ := hn
    by_cases hz : n = 0
    · simp [hz]
    by_cases hpn : p ∣ n
    · rw [heq] at hpn
      obtain ⟨⟨u, hu⟩, ⟨v, hv⟩⟩ := divides_coordinates hp hi hpn
      let z := u^2 + 2*v^2
      have hf : n = p^2 * z := by rw [heq, hu, hv]; dsimp [z]; ring
      have hz' : z ≠ 0 := by intro h; simp [h] at hf; contradiction
      have hlt : z < n := by
        rw [hf]
        exact lt_mul_of_one_lt_left (Nat.pos_of_ne_zero hz') (one_lt_pow₀ hp.one_lt (by decide))
      have hvz := ih z hlt ⟨u, v, rfl⟩
      rw [hf, padicValNat.mul (pow_ne_zero _ hp.ne_zero) hz', padicValNat.prime_pow]
      exact (show Even 2 by decide).add hvz
    · simp [padicValNat.eq_zero_of_not_dvd hpn]

end OMA.E659

open Filter Asymptotics
open scoped Classical

theorem OMA.Grid659Count.norm_count_isBigO :
    (fun N : ℕ => (((Finset.range (N+1)).filter (fun t => ∃ a b : ℕ, t = a^2 + 2*b^2)).card : ℝ))
      =O[atTop] (fun N : ℕ => (N:ℝ) / (Real.log N).sqrt) := by
  have hc := OMA.Grid659Count.count_asymptotic Grid659Harmonic.harmonicActual
    (OMA.Grid659Weighted.weighted_of_primePowers OMA.Grid659Prime.prime_power_log_sum_linear)
  refine (Asymptotics.IsBigO.of_bound 1 ?_).trans hc
  apply Filter.Eventually.of_forall
  intro N
  simp only [Real.norm_eq_abs, Nat.abs_cast, one_mul]
  exact_mod_cast Finset.card_le_card (fun n hn => Finset.mem_filter.mpr
    ⟨(Finset.mem_filter.mp hn).1, fun q hq hi =>
      OMA.E659.even_valuation_of_norm (Nat.prime_of_mem_primeFactors hq) hi (Finset.mem_filter.mp hn).2⟩)

/- Integers of the form (a^2+2b^2) count the distances on the rectangular lattice. -/

namespace OMA.Grid659

open Filter Asymptotics
open scoped EuclideanGeometry Classical

noncomputable def point (p : ℤ × ℤ) : ℝ² :=
  !₂[(p.1 : ℝ), (p.2 : ℝ) * Real.sqrt 2]

def squareNorm (p q : ℤ × ℤ) : ℤ := (p.1 - q.1)^2 + 2 * (p.2 - q.2)^2

def squared (S : Finset (ℤ × ℤ)) : Finset ℤ :=
  S.offDiag.image fun pq => squareNorm pq.1 pq.2

noncomputable def count (X : ℕ) : ℕ :=
  ((Finset.range (X + 1)).filter (fun t => ∃ a b : ℕ, t = a^2 + 2*b^2)).card

private theorem point_inj : Function.Injective point := by
  intro p q h
  have h0 := congrArg (fun v : ℝ² => v 0) h
  have h1 := congrArg (fun v : ℝ² => v 1) h
  apply Prod.ext
  · exact_mod_cast (show (p.1 : ℝ) = q.1 by simpa [point] using h0)
  · have h' : (p.2 : ℝ) * Real.sqrt 2 = q.2 * Real.sqrt 2 := by simpa [point] using h1
    exact_mod_cast (mul_right_cancel₀ (by positivity : Real.sqrt 2 ≠ 0) h')

private theorem dist_point (p q : ℤ × ℤ) :
    dist (point p) (point q) = Real.sqrt (squareNorm p q : ℝ) := by
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_two]
  congr 1
  simp [point, squareNorm, Real.dist_eq, sq_abs, ← sub_mul, mul_pow,
    Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  ring

private theorem distinct_eq (S : Finset (ℤ × ℤ)) :
    distinctDistances (S.image point) = (squared S).card := by
  classical
  have hset : distanceSet (S.image point) =
      (squared S).image (fun t : ℤ => Real.sqrt (t : ℝ)) := by
    ext d
    constructor
    · rintro hd
      obtain ⟨⟨a,b⟩, hab, rfl⟩ := Finset.mem_image.mp hd
      obtain ⟨ha, hb, hne⟩ := Finset.mem_offDiag.mp hab
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hb
      exact Finset.mem_image.mpr ⟨_, Finset.mem_image.mpr
        ⟨(p,q), Finset.mem_offDiag.mpr ⟨hp,hq,fun h => hne (congrArg point h)⟩, rfl⟩,
        (dist_point p q).symm⟩
    · intro hd
      obtain ⟨_, ht, rfl⟩ := Finset.mem_image.mp hd
      obtain ⟨⟨p,q⟩, hpq, rfl⟩ := Finset.mem_image.mp ht
      obtain ⟨hp,hq,hne⟩ := Finset.mem_offDiag.mp hpq
      exact Finset.mem_image.mpr ⟨(point p, point q), Finset.mem_offDiag.mpr
        ⟨Finset.mem_image_of_mem _ hp, Finset.mem_image_of_mem _ hq,
          fun h => hne (point_inj h)⟩, dist_point p q⟩
  rw [distinctDistances, hset]
  apply Finset.card_image_of_injOn
  have hnonneg {t : ℤ} (ht : t ∈ squared S) : 0 ≤ (t : ℝ) := by
    obtain ⟨⟨p,q⟩, _, rfl⟩ := Finset.mem_image.mp ht
    dsimp [squareNorm]
    positivity
  intro a ha b hb he
  exact_mod_cast (Real.sqrt_inj (hnonneg ha) (hnonneg hb)).mp he

private def side (m : ℕ) : Finset ℤ := (Finset.range m).image Int.ofNat

private theorem count_grid {m : ℕ} {S : Finset (ℤ × ℤ)}
    (hS : S ⊆ side m ×ˢ side m) : (squared S).card ≤ count (3 * m^2) := by
  classical
  let T := (Finset.range (3 * m^2 + 1)).filter fun t => ∃ a b : ℕ, t = a^2 + 2*b^2
  have hs : squared S ⊆ T.image Int.ofNat := by
    intro t ht
    obtain ⟨⟨p,q⟩, hpq, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨hp,hq,_⟩ := Finset.mem_offDiag.mp hpq
    have hbound {x : ℤ} (hx : x ∈ side m) : 0 ≤ x ∧ x < (m : ℤ) := by
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      change 0 ≤ (i : ℤ) ∧ (i : ℤ) < (m : ℤ)
      exact ⟨by positivity, by exact_mod_cast Finset.mem_range.mp hi⟩
    obtain ⟨hp₁,hp₂⟩ := Finset.mem_product.mp (hS hp)
    obtain ⟨hq₁,hq₂⟩ := Finset.mem_product.mp (hS hq)
    let a := (p.1 - q.1).natAbs
    let b := (p.2 - q.2).natAbs
    have hdiff {x y : ℤ} (hx : x ∈ side m) (hy : y ∈ side m) : (x-y).natAbs ≤ m := by
      have h1 := hbound hx
      have h2 := hbound hy
      omega
    have hsize : a^2 + 2*b^2 < 3*m^2 + 1 := by
      nlinarith [Nat.pow_le_pow_left (hdiff hp₁ hq₁) 2, Nat.pow_le_pow_left (hdiff hp₂ hq₂) 2,
        show a^2 = (p.1-q.1).natAbs^2 by rfl, show b^2 = (p.2-q.2).natAbs^2 by rfl]
    refine Finset.mem_image.mpr ⟨a^2 + 2*b^2, Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr hsize, a, b, rfl⟩, ?_⟩
    change ((a^2 + 2*b^2 : ℕ) : ℤ) = squareNorm p q
    simp [a,b,squareNorm,sq_abs]
  exact (Finset.card_le_card hs).trans Finset.card_image_le

private theorem finite_family
    (hloc : ∀ S : Finset (ℤ × ℤ), S.card = 4 → 3 ≤ (squared S).card) (n : ℕ) :
    ∃ A : Finset ℝ², A.card = n ∧ (∀ B ⊆ A, B.card = 4 → 3 ≤ distinctDistances B) ∧
      distinctDistances A ≤ count (3*(n.sqrt+1)^2) := by
  classical
  let m := n.sqrt + 1
  let box := side m ×ˢ side m
  have hm : (side m).card = m := by
    have hi : Function.Injective Int.ofNat := fun _ _ h => Int.ofNat_inj.mp h
    simp [side, Finset.card_image_of_injective _ hi]
  have hn : n ≤ box.card := by
    simpa [box, Finset.card_product, hm, m] using (Nat.lt_succ_sqrt n).le
  obtain ⟨S,hS,hnS⟩ := Finset.exists_subset_card_eq hn
  refine ⟨S.image point, (Finset.card_image_of_injective _ point_inj).trans hnS, ?_, ?_⟩
  · intro B hB hfour
    obtain ⟨U, _, rfl⟩ := Finset.subset_image_iff.mp hB
    rw [Finset.card_image_of_injective _ point_inj] at hfour
    exact (hloc U hfour).trans_eq (distinct_eq U).symm
  · exact (distinct_eq S).le.trans (count_grid hS)

theorem transfer
    (hloc : ∀ S : Finset (ℤ × ℤ), S.card = 4 → 3 ≤ (squared S).card)
    (hcount : (fun n : ℕ => (count n : ℝ)) =O[atTop]
        (fun n : ℕ => (n : ℝ) / Real.sqrt (Real.log n))) :
    type_of% @Erdos659.erdos_659 := by
  choose A hcard hfour hgrid using finite_family hloc
  refine ⟨A, fun n => ⟨hcard n,hfour n⟩, ?_⟩
  obtain ⟨C, hC, h⟩ := hcount.exists_nonneg
  obtain ⟨N, hN⟩ := eventually_atTop.1 h.bound
  apply IsBigO.of_bound (C * 12)
  filter_upwards [eventually_ge_atTop (max 2 N)] with n hn
  let m := 3 * (n.sqrt + 1)^2
  have hn2 : 2 ≤ n := (le_max_left _ _).trans hn
  have hnm : n ≤ m := by
    have hside : n < (n.sqrt + 1)^2 := Nat.lt_succ_sqrt' n
    dsimp [m]
    omega
  have hs : 1 ≤ n.sqrt := Nat.le_sqrt.mpr (by omega)
  have hm12 : m ≤ 12*n := by
    dsimp [m]
    calc
      3 * (n.sqrt + 1)^2 ≤ 3 * (2 * n.sqrt)^2 := by gcongr; omega
      _ = 12 * n.sqrt^2 := by ring
      _ ≤ 12*n := by gcongr; exact Nat.sqrt_le' n
  have hc := hN m (((le_max_right _ _).trans hn).trans hnm)
  have hnpos : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hlogpos : 0 < (n : ℝ).log.sqrt := Real.sqrt_pos.2 (Real.log_pos hnpos)
  have hlogle : (n : ℝ).log.sqrt ≤ (m : ℝ).log.sqrt :=
    Real.sqrt_le_sqrt (Real.log_le_log (by positivity) (by exact_mod_cast hnm))
  simp only [Real.norm_eq_abs, Nat.abs_cast,
    abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _))] at hc ⊢
  calc
    (distinctDistances (A n) : ℝ) ≤ count m := by exact_mod_cast hgrid n
    _ ≤ C * ((m : ℝ) / (m : ℝ).log.sqrt) := hc
    _ ≤ C * ((12 * (n : ℝ)) / (n : ℝ).log.sqrt) := by
      apply mul_le_mul_of_nonneg_left _ hC
      calc
        (m : ℝ) / (m : ℝ).log.sqrt ≤ (m : ℝ) / (n : ℝ).log.sqrt :=
          div_le_div_of_nonneg_left (Nat.cast_nonneg _) hlogpos hlogle
        _ ≤ (12 * (n : ℝ)) / (n : ℝ).log.sqrt := by gcongr; exact_mod_cast hm12
    _ = (C * 12) * ((n : ℝ) / (n : ℝ).log.sqrt) := by ring

end OMA.Grid659

/- The square norm of the rectangular lattice distinguishes successive binary coordinate bits. -/

namespace OMA.Grid659

def quadDist (x y : ℤ × ℤ) : ℤ := (x.1-y.1)^2 + 2*(x.2-y.2)^2

private theorem quad_comm (x y : ℤ × ℤ) : quadDist x y = quadDist y x := by
  dsimp [quadDist]; ring

private theorem sq_mod (z : ℤ) : z^2 % 4 = z % 2 := by
  generalize hx : z/2 = w
  rcases Int.emod_two_eq_zero_or_one z with he | he
  · have hz : z = 2*w := by omega
    rw [he,hz]
    ring_nf
    omega
  · have hz : z = 2*w+1 := by omega
    rw [he,hz]
    ring_nf
    omega

private theorem quad_mod (x y : ℤ × ℤ) : quadDist x y % 4 =
    (x.1-y.1)%2 + 2*((x.2-y.2)%2) := by
  have h := sq_mod (x.1-y.1)
  have h' := sq_mod (x.2-y.2)
  unfold quadDist
  omega

private theorem bit_eq (x y : ℤ) :
    decide (x%2=0) = decide (y%2=0) ↔ x%2=y%2 := by
  by_cases hx : x%2=0 <;> by_cases hy : y%2=0 <;> simp [hx,hy] <;> omega

private def Split {ι : Type*} (f : ι → ℤ × ℤ) : Prop :=
  ∃ c : ι → Bool, (∃ u v, c u ≠ c v) ∧
    ∀ i j k l, c i = c j → c k ≠ c l → quadDist (f i) (f j) ≠ quadDist (f k) (f l)

private theorem has_split {ι : Type*} (f : ι → ℤ × ℤ) (u v : ι) (huv : f u ≠ f v) :
    Split f := by
  classical
  induction hN : (quadDist (f u) (f v)).natAbs using Nat.strong_induction_on generalizing f with
  | _ n ih =>
    by_cases hx : ∀ i j, (f i).1%2=(f j).1%2
    · by_cases hy : ∀ i j, (f i).2%2=(f j).2%2
      · let g (i : ι) : ℤ × ℤ := ((f i).1/2, (f i).2/2)
        have hscale (i j : ι) : quadDist (f i) (f j) = 4*quadDist (g i) (g j) := by
          have hx' := hx i j
          have hy' := hy i j
          have h1 : (f i).1-(f j).1 = 2*((g i).1-(g j).1) := by dsimp [g]; omega
          have h2 : (f i).2-(f j).2 = 2*((g i).2-(g j).2) := by dsimp [g]; omega
          simp only [quadDist,h1,h2]
          ring
        have hpos : quadDist (f u) (f v) ≠ 0 := by
          intro hz
          obtain ⟨h1,h2⟩ := (add_eq_zero_iff_of_nonneg (sq_nonneg _) (mul_nonneg (by decide) (sq_nonneg _))).mp hz
          apply huv
          apply Prod.ext
          · exact sub_eq_zero.mp (by simpa using h1)
          · exact sub_eq_zero.mp (by simpa using h2)
        have hg : g u ≠ g v := by
          intro he
          exact hpos (by rw [hscale,he]; simp [quadDist])
        have hlt : (quadDist (g u) (g v)).natAbs < n := by
          have : 0 < n := hN ▸ Int.natAbs_pos.mpr hpos
          rw [hscale,Int.natAbs_mul] at hN
          norm_num at hN
          omega
        obtain ⟨c,hn,hs⟩ := ih _ hlt g hg rfl
        refine ⟨c,hn,fun i j k l hij hkl => ?_⟩
        rw [hscale,hscale]
        exact fun eq => hs i j k l hij hkl (by omega)
      · push Not at hy
        obtain ⟨u',v',hne⟩ := hy
        refine ⟨fun i => decide ((f i).2%2=0), ⟨u',v',fun h => hne ((bit_eq _ _).mp h)⟩, ?_⟩
        intro i j k l hij hkl eq
        have h1 := (bit_eq _ _).mp hij
        have h2 : (f k).2%2 ≠ (f l).2%2 := fun he => hkl ((bit_eq _ _).mpr he)
        have h3 := hx i j
        have h4 := hx k l
        have hmod := (quad_mod (f i) (f j)).symm.trans
          ((congrArg (fun z : ℤ => z%4) eq).trans (quad_mod (f k) (f l)))
        omega
    · push Not at hx
      obtain ⟨u',v',hne⟩ := hx
      refine ⟨fun i => decide ((f i).1%2=0), ⟨u',v',fun h => hne ((bit_eq _ _).mp h)⟩, ?_⟩
      intro i j k l hij hkl eq
      have h1 := (bit_eq _ _).mp hij
      have h2 : (f k).1%2 ≠ (f l).1%2 := fun he => hkl ((bit_eq _ _).mpr he)
      have hmod := (quad_mod (f i) (f j)).symm.trans
        ((congrArg (fun z : ℤ => z%4) eq).trans (quad_mod (f k) (f l)))
      omega

private theorem three_pair : ∀ c : Fin 3 → Bool, ∃ i j, i ≠ j ∧ c i = c j := by decide

private theorem no_mono_triangle (x y z : ℤ × ℤ) (hxy : x ≠ y)
    (hxz : quadDist x y = quadDist x z) (hyz : quadDist x y = quadDist y z) : False := by
  let f : Fin 3 → ℤ × ℤ := ![x,y,z]
  obtain ⟨c, ⟨k,l,hkl⟩, hs⟩ := has_split f 0 1 hxy
  obtain ⟨i,j,hij,hc⟩ := three_pair c
  have hconst : ∀ i j : Fin 3, i ≠ j → quadDist (f i) (f j) = quadDist x y := by
    have hyx := quad_comm y x
    have hzx := quad_comm z x
    have hzy := quad_comm z y
    intro i j h
    fin_cases i <;> fin_cases j <;>
      first | exact (h rfl).elim | simp [f] <;> grind
  exact hs i j k l hc hkl ((hconst i j hij).trans (hconst k l (fun t => hkl (congrArg c t))).symm)

private theorem four_patterns : ∀ c : Fin 4 → Bool,
    (∀ i j k, i ≠ j → i ≠ k → j ≠ k → c i = c j → c i = c k → False) →
    (c 0 = c 1 ∧ c 2 = c 3 ∧ c 0 ≠ c 2) ∨
    (c 0 = c 2 ∧ c 1 = c 3 ∧ c 0 ≠ c 1) ∨
    (c 0 = c 3 ∧ c 2 = c 1 ∧ c 0 ≠ c 2) := by
  intro c hn
  have h012 := hn 0 1 2 (by decide) (by decide) (by decide)
  have h013 := hn 0 1 3 (by decide) (by decide) (by decide)
  have h023 := hn 0 2 3 (by decide) (by decide) (by decide)
  have h123 := hn 1 2 3 (by decide) (by decide) (by decide)
  cases h0 : c 0 <;> cases h1 : c 1 <;> cases h2 : c 2 <;> cases h3 : c 3 <;>
    simp_all

private theorem balanced_four (c : Fin 4 → Bool)
    (hn : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → c i = c j → c i = c k → False) :
    ∃ σ : Equiv.Perm (Fin 4), c (σ 0) = c (σ 1) ∧ c (σ 2) = c (σ 3) ∧ c (σ 0) ≠ c (σ 2) := by
  rcases four_patterns c hn with h | h | h
  · exact ⟨Equiv.refl _,h⟩
  · exact ⟨Equiv.swap 1 2,by simpa [Equiv.swap_apply_def] using h⟩
  · exact ⟨Equiv.swap 1 3,by simpa [Equiv.swap_apply_def] using h⟩

private theorem two_other {a b d e o : ℤ} (hd : d = a ∨ d = b)
    (he : e = a ∨ e = b) (ho : o = a ∨ o = b) (hdo : d ≠ o) (heo : e ≠ o) : d = e := by
  grind

theorem four_split (f : Fin 4 → ℤ × ℤ) (hf : Function.Injective f)
    (a b : ℤ) (h2 : ∀ i j, i ≠ j → quadDist (f i) (f j) = a ∨ quadDist (f i) (f j) = b) :
    ∃ σ : Equiv.Perm (Fin 4),
      quadDist (f (σ 0)) (f (σ 2)) = quadDist (f (σ 0)) (f (σ 3)) ∧
      quadDist (f (σ 0)) (f (σ 2)) = quadDist (f (σ 1)) (f (σ 2)) ∧
      quadDist (f (σ 0)) (f (σ 2)) = quadDist (f (σ 1)) (f (σ 3)) ∧
      quadDist (f (σ 0)) (f (σ 1)) = quadDist (f (σ 2)) (f (σ 3)) := by
  obtain ⟨c,⟨u,v,huv⟩,hs⟩ := has_split f 0 1 (hf.ne (by decide))
  have within (i j k l) (hij : i ≠ j) (hkl : k ≠ l) (hc : c i = c j) (hc' : c k = c l) :
      quadDist (f i) (f j) = quadDist (f k) (f l) :=
    two_other (h2 _ _ hij) (h2 _ _ hkl) (h2 u v (fun t => huv (congrArg c t)))
      (hs i j u v hc huv) (hs k l u v hc' huv)
  have hn (i j k) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
      (hc : c i = c j) (hc' : c i = c k) : False :=
    no_mono_triangle _ _ _ (hf.ne hij) (within i j i k hij hik hc hc')
      (within i j j k hij hjk hc (hc.symm.trans hc'))
  obtain ⟨σ,h01,h23,h02⟩ := balanced_four c hn
  have cross (i j k l) (hc : c i ≠ c j) (hc' : c k ≠ c l) :
      quadDist (f i) (f j) = quadDist (f k) (f l) :=
    two_other (h2 _ _ (fun t => hc (congrArg c t))) (h2 _ _ (fun t => hc' (congrArg c t)))
      (h2 (σ 0) (σ 1) (σ.injective.ne (by decide)))
      (hs _ _ i j h01 hc).symm (hs _ _ k l h01 hc').symm
  exact ⟨σ,cross _ _ _ _ h02 (by grind),cross _ _ _ _ h02 (by grind),
    cross _ _ _ _ h02 (by grind),
    within _ _ _ _ (σ.injective.ne (by decide)) (σ.injective.ne (by decide)) h01 h23⟩

end OMA.Grid659

/- A nondegenerate balanced two-distance quartet cannot occur in the norm x² + 2y². -/

namespace OMA.Grid659Balance

abbrev Q (v : ℤ × ℤ) : ℤ := v.1 ^ 2 + 2 * v.2 ^ 2

private lemma zero_of_sq_eq_two_sq {x y : ℤ} (h : x ^ 2 = 2 * y ^ 2) : x = 0 := by
  by_cases hy : y = 0
  · simpa [hy] using h
  have hq : (x : ℚ)^2 = 2 * (y : ℚ)^2 := by exact_mod_cast h
  have hyq : (y : ℚ) ≠ 0 := by exact_mod_cast hy
  have hs : IsSquare (2 : ℚ) := (isSquare_iff_exists_sq _).mpr ⟨(x : ℚ)/y, by
    rw [div_pow, eq_div_iff (pow_ne_zero _ hyq)]
    exact hq.symm⟩
  exact False.elim ((by norm_num : ¬ IsSquare (2 : ℚ)) hs)

theorem not_balanced (a b c d : ℤ × ℤ) (hab : a ≠ b)
    (h1 : Q (a-c) = Q (a-d)) (h2 : Q (a-c) = Q (b-c)) (h3 : Q (a-c) = Q (b-d))
    (he : Q (a-b) = Q (c-d)) : False := by
  let dot := (a.1-b.1)*(c.1-d.1) + 2*(a.2-b.2)*(c.2-d.2)
  let det := (a.1-b.1)*(c.2-d.2) - (a.2-b.2)*(c.1-d.1)
  have hd : dot = 0 := by
    dsimp [Q, dot] at *
    linarith only [h1, h2, h3]
  have hsq : Q (a-b)^2 = 2 * det^2 := calc
    _ = Q (a-b) * Q (c-d) := by rw [← he, sq]
    _ = dot^2 + 2 * det^2 := by dsimp [Q, dot, det]; ring
    _ = _ := by rw [hd]; ring
  have z := zero_of_sq_eq_two_sq hsq
  change (a.1-b.1)^2 + 2*(a.2-b.2)^2 = 0 at z
  apply hab
  apply Prod.ext <;> nlinarith [sq_nonneg (a.1-b.1), sq_nonneg (a.2-b.2)]

end OMA.Grid659Balance

/- Convert numerical two-distance labels into the cardinality statement for every four lattice points. -/

namespace OMA.Grid659Finish

private abbrev Q (p q : ℤ × ℤ) : ℤ := (p.1-q.1)^2 + 2*(p.2-q.2)^2

theorem card_of_no_two_labels
    (hno : ∀ (f : Fin 4 → ℤ × ℤ), Function.Injective f → ∀ a b : ℤ,
      ¬ ∀ i j, i ≠ j → Q (f i) (f j) = a ∨ Q (f i) (f j) = b)
    (S : Finset (ℤ × ℤ)) (hS : S.card = 4) :
    3 ≤ (S.offDiag.image (fun p => Q p.1 p.2)).card := by
  classical
  by_contra! h
  let D := S.offDiag.image (fun p => Q p.1 p.2)
  have hD : D.card ≤ 2 := by dsimp only [D]; omega
  obtain ⟨a,b,hab⟩ : ∃ a b : ℤ, ∀ z ∈ D, z = a ∨ z = b := by
    rcases hD.eq_or_lt with h2 | h1
    · obtain ⟨a,b,_,hp⟩ := Finset.card_eq_two.mp h2
      exact ⟨a,b,by simp [hp]⟩
    · obtain ⟨a, ha⟩ := Finset.card_le_one_iff_subset_singleton.mp (by omega : D.card ≤ 1)
      exact ⟨a,a,fun z hz => Or.inl (Finset.mem_singleton.mp (ha hz))⟩
  let e := (S.equivFinOfCardEq hS).symm
  let f : Fin 4 → ℤ × ℤ := fun i => (e i).val
  have hf : Function.Injective f := Subtype.val_injective.comp e.injective
  apply hno f hf a b
  intro i j hij
  exact hab _ (Finset.mem_image.mpr ⟨(f i,f j), Finset.mem_offDiag.mpr
    ⟨(e i).property, (e j).property, hf.ne hij⟩, rfl⟩)

end OMA.Grid659Finish

theorem OMA.solution : type_of% @Erdos659.erdos_659 := by
  refine OMA.Grid659.transfer ?_ OMA.Grid659Count.norm_count_isBigO
  apply OMA.Grid659Finish.card_of_no_two_labels
  intro f hf a b ht
  obtain ⟨σ, h₁, h₂, h₃, h₄⟩ := OMA.Grid659.four_split f hf a b ht
  exact OMA.Grid659Balance.not_balanced _ _ _ _ (hf.ne (σ.injective.ne (by decide : (0 : Fin 4) ≠ 1)))
    h₁ h₂ h₃ h₄
