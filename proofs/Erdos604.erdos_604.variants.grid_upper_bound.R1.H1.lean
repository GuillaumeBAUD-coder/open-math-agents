import OMAReductions.R_Erdos604_erdos_604_variants_grid_upper_bound_R1
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.LegendreSymbol.ZModChar
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries

/-! # Reciprocal sum over integers representable as two squares

Compare the square of the Dirichlet series with a product of zeta and the mod-four
Dirichlet L-function. The local inequalities at split, inert, and ramified primes give
the comparison, and Rankin's estimate at s = 1 + 1/log N turns it into the harmonic bound. -/

open Filter
open scoped Topology BigOperators

namespace Grid604Harmonic

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


noncomputable def chi4 : DirichletCharacter ℂ 4 := ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)

lemma chi4_ne_one : chi4 ≠ 1 := by
  intro h
  have hv := congrArg (fun χ : DirichletCharacter ℂ 4 => χ (-1)) h
  have hh : ZMod.χ₄ (-1) = -1 := by decide
  simp [chi4, MulChar.ringHomComp_apply, hh, MulChar.one_apply isUnit_one.neg] at hv
  norm_num at hv

lemma eventually_bounded_chi4 :
    ∀ᶠ s : ℝ in 𝓝[>] 1, ‖chi4.LFunction (s : ℂ)‖ ≤ ‖chi4.LFunction 1‖ + 1 := by
  have hc : ContinuousAt (fun s : ℝ => ‖chi4.LFunction (s : ℂ)‖) 1 :=
    ((chi4.differentiable_LFunction chi4_ne_one).continuous.comp Complex.continuous_ofReal).norm.continuousAt
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
    (if p % 4 = 3 then (1 - x^2)⁻¹ else (1 - x)⁻¹)^2 ≤
    (if p = 2 then 2 else 1) * (1-x)⁻¹ *
      (1 - (ZMod.χ₄ p : ℝ)*x)⁻¹ * (1-x^2)⁻¹ := by
  have ha : 0 < 1 - x := by linarith
  have hb : 0 < 1 + x := by linarith
  have hc : 0 < 1 - x^2 := by nlinarith [mul_pos ha hb]
  rw [ZMod.χ₄_nat_eq_if_mod_four]
  by_cases hp2 : p = 2
  · subst p
    norm_num
    field_simp
    nlinarith [mul_nonneg ha.le ha.le]
  · have hodd := hp.eq_two_or_odd.resolve_left hp2
    have his : p % 4 = 1 ∨ p % 4 = 3 := by omega
    rcases his with h | h
    · simp [h, hp2, show ¬ p % 2 = 0 by omega]
      field_simp
      nlinarith [mul_nonneg (sq_nonneg x) (sq_nonneg (1-x))]
    · simp [h, hp2, show ¬ p % 2 = 0 by omega]
      field_simp
      ring_nf
      exact le_rfl


lemma harmonicOfFourFactors (S : ℕ → Prop) [DecidablePred S]
    (hprod : ∀ᶠ s : ℝ in 𝓝[>] 1,
      series S s ^ 2 ≤ 2 * (∑' m : ℕ, 1 / (m : ℝ) ^ (2*s)) *
        ‖chi4.LFunction (s : ℂ)‖ * ∑' m : ℕ, 1 / (m : ℝ) ^ s) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      ∑ m ∈ ((Finset.range (N + 1)).filter S), (m : ℝ)⁻¹ ≤ C * Real.sqrt (Real.log N) := by
  let M := (∑' m : ℕ, 1 / (m : ℝ) ^ (2 : ℝ)) + 1
  have hZ : 0 ≤ ∑' m : ℕ, 1 / (m : ℝ) ^ (2 : ℝ) := tsum_nonneg (fun _ => by positivity)
  have hM : 0 < M := by dsimp [M]; positivity
  apply harmonicOfEulerComparison S (K := 2 * M * (‖chi4.LFunction 1‖ + 1)) (by positivity)
  filter_upwards [hprod, eventually_bounded_chi4, self_mem_nhdsWithin] with s hp hL hs
  have hs' : 1 < s := hs
  have hcor : (∑' m : ℕ, 1 / (m : ℝ) ^ (2*s)) ≤ M :=
    (correction_le_zeta_two hs').trans (by dsimp [M]; linarith)
  exact hp.trans (by gcongr)


abbrev admissible (n : ℕ) := ∀ q ∈ n.primeFactors, q % 4 = 3 → Even (padicValNat q n)

lemma admissible_iff (n : ℕ) : admissible n ↔ ∀ q, q % 4 = 3 → Even (n.factorization q) := by
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
    admissible (p^k) ↔ (p % 4 = 3 → Even k) := by
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
    HasProd (fun p : Nat.Primes => if p.val % 4 = 3 then (1-(weight s p)^2)⁻¹ else (1-weight s p)⁻¹)
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
  by_cases h : p.val % 4 = 3
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

lemma chi4ProdWeight {s : ℝ} (hs : 1 < s) :
    HasProd (fun p : Nat.Primes => |(1 - (ZMod.χ₄ p : ℝ) * weight s p)⁻¹|)
      ‖chi4.LFunction (s : ℂ)‖ := by
  have hre : 1 < (s : ℂ).re := hs
  rw [DirichletCharacter.LFunction_eq_LSeries chi4 hre]
  apply (chi4.LSeries_eulerProduct_hasProd hre).norm.congr_fun
  intro p
  have hx : ((weight s p : ℝ) : ℂ) = (p.val : ℂ) ^ (-(s : ℂ)) := by
    rw [← Complex.ofReal_neg, ← Complex.ofReal_natCast,
      ← Complex.ofReal_cpow (Nat.cast_nonneg _), Real.rpow_neg (Nat.cast_nonneg _)]
    simp [weight]
  have hχ : (((ZMod.χ₄ p : ℤ) : ℝ) : ℂ) = chi4 p := by simp [chi4, MulChar.ringHomComp_apply]
  have hv : (((1 - (ZMod.χ₄ p : ℝ) * weight s p)⁻¹ : ℝ) : ℂ) =
      (1 - chi4 p * (p.val : ℂ)^(-(s : ℂ)))⁻¹ := by
    rw [Complex.ofReal_inv, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_one, hχ, hx]
  rw [← hv, Complex.norm_real, Real.norm_eq_abs]

lemma actualEulerComparison {s : ℝ} (hs : 1 < s) :
    series admissible s ^ 2 ≤ 2 * (∑' m : ℕ, 1 / (m : ℝ) ^ (2*s)) *
      ‖chi4.LFunction (s : ℂ)‖ * ∑' m : ℕ, 1 / (m : ℝ) ^ s := by
  let l (p : Nat.Primes) := if p.val % 4 = 3 then (1-(weight s p)^2)⁻¹ else (1-weight s p)⁻¹
  let b (p : Nat.Primes) : ℝ := if p.val = 2 then 2 else 1
  have htwo : HasProd b 2 := by
    apply (hasProd_ite_eq (⟨2, Nat.prime_two⟩ : Nat.Primes) (2:ℝ)).congr_fun
    intro p
    simp [b, Subtype.ext_iff]
  have he : HasProd l (series admissible s) := admissibleEuler hs
  have hright := ((htwo.mul (zetaProdWeight (s := 2*s) (by linarith))).mul
    (chi4ProdWeight hs)).mul (zetaProdWeight hs)
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
    change l p * l p ≤ b p * (1-weight (2*s) p)⁻¹ * |(1-(ZMod.χ₄ p : ℝ)*x)⁻¹| * (1-x)⁻¹
    rw [weight_double]
    calc
      _ ≤ b p * (1-x)⁻¹ * (1-(ZMod.χ₄ p : ℝ)*x)⁻¹ * (1-x^2)⁻¹ := by
        simpa only [l, b, x, sq] using localEulerMajorant p.val p.prop hx hx1
      _ ≤ b p * (1-x)⁻¹ * |(1-(ZMod.χ₄ p : ℝ)*x)⁻¹| * (1-x^2)⁻¹ := by
        gcongr
        exact le_abs_self _
      _ = _ := by ring

lemma harmonicActual :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      ∑ m ∈ ((Finset.range (N + 1)).filter admissible), (m : ℝ)⁻¹ ≤
        C * Real.sqrt (Real.log N) := by
  apply harmonicOfFourFactors
  filter_upwards [self_mem_nhdsWithin] with s hs using actualEulerComparison hs

end Grid604Harmonic

theorem OMA.solution : OMA.R_Erdos604_erdos_604_variants_grid_upper_bound_R1.H1 :=
  Grid604Harmonic.harmonicActual
