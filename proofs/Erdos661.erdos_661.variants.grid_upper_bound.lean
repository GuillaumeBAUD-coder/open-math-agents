import FormalConjectures.ErdosProblems.«661»
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.LegendreSymbol.ZModChar
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.Chebyshev

/-! Use the square-grid construction from #2120 on 2n points, then split the grid into two sets.
Credit: @JaviSoto. -/

/- Every pair of points in a square grid gives a sum of two squares. The count uses the two arithmetic estimates from the Erdős 604 reduction. -/

namespace OMA.Grid89

open Filter
open scoped BigOperators

/-- The reciprocal sum over numbers whose inert prime exponents are even. The term at zero
is zero by the convention for the reciprocal in ℝ. -/
def H1 : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
    (∑ m ∈ ((Finset.range (N + 1)).filter fun m =>
      ∀ q ∈ m.primeFactors, q % 4 = 3 → Even (padicValNat q m)), (m : ℝ)⁻¹) ≤
      C * Real.sqrt (Real.log N)

/-- Chebyshev's weighted counting estimate on the same multiplicative set. -/
def H2 : Prop :=
  ∃ D : ℝ, 0 < D ∧ ∀ᶠ N : ℕ in atTop,
    let S := ((Finset.range (N + 1)).filter fun m =>
      ∀ q ∈ m.primeFactors, q % 4 = 3 → Even (padicValNat q m))
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
private lemma count_asymptotic (harmonic : H1) (weighted : H2) :
    (fun N : ℕ => (((Finset.range (N + 1)).filter fun m =>
      ∀ q ∈ m.primeFactors, q % 4 = 3 → Even (padicValNat q m)).card : ℝ)) =O[atTop]
      (fun N : ℕ => (N : ℝ) / (Real.log N).sqrt) := by
  obtain ⟨C, hC, hh⟩ := harmonic
  obtain ⟨D, hD, hw⟩ := weighted
  refine Asymptotics.isBigO_iff.mpr ⟨2 + 2 * D * C, ?_⟩
  filter_upwards [hh, hw, eventually_ge_atTop 2] with N hH hW hN
  let S := ((Finset.range (N + 1)).filter fun m =>
      ∀ q ∈ m.primeFactors, q % 4 = 3 → Even (padicValNat q m))
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

/-- Passing from the number of points to the range of squared distances changes only the constant. -/
private lemma gridAsymptoticTransfer (P count : ℕ → ℕ)
    (hgrid : ∀ n : ℕ, P n ≤ count (2 * (n.sqrt + 1)^2))
    (hcount : (fun x : ℕ => (count x : ℝ)) =O[atTop]
      (fun x : ℕ => (x : ℝ) / (x : ℝ).log.sqrt)) :
    (fun n : ℕ => (P n : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ) / (n : ℝ).log.sqrt) := by
  obtain ⟨C, hC, h⟩ := hcount.exists_nonneg
  obtain ⟨N, hN⟩ := eventually_atTop.1 h.bound
  apply IsBigO.of_bound (C * 8)
  filter_upwards [eventually_ge_atTop (max 2 N)] with n hn
  let m := 2 * (n.sqrt + 1)^2
  have hn2 : 2 ≤ n := (le_max_left _ _).trans hn
  have hnm : n ≤ m := by
    have hside : n < (n.sqrt + 1)^2 := Nat.lt_succ_sqrt' n
    dsimp [m]
    omega
  have hs : 1 ≤ n.sqrt := Nat.le_sqrt.mpr (by omega)
  have hm8 : m ≤ 8 * n := by
    dsimp [m]
    calc
      2 * (n.sqrt + 1)^2 ≤ 2 * (2 * n.sqrt)^2 := by gcongr; omega
      _ = 8 * n.sqrt^2 := by ring
      _ ≤ 8 * n := by gcongr; exact Nat.sqrt_le' n
  have hmcount := hN m (((le_max_right _ _).trans hn).trans hnm)
  have hnpos : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hlogpos : 0 < (n : ℝ).log.sqrt := Real.sqrt_pos.2 (Real.log_pos hnpos)
  have hlogle : (n : ℝ).log.sqrt ≤ (m : ℝ).log.sqrt :=
    Real.sqrt_le_sqrt (Real.log_le_log (by positivity) (by exact_mod_cast hnm))
  simp only [Real.norm_eq_abs, Nat.abs_cast,
    abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _))] at hmcount ⊢
  calc
    (P n : ℝ) ≤ count m := by exact_mod_cast hgrid n
    _ ≤ C * ((m : ℝ) / (m : ℝ).log.sqrt) := hmcount
    _ ≤ C * ((8 * (n : ℝ)) / (n : ℝ).log.sqrt) := by
      apply mul_le_mul_of_nonneg_left _ hC
      calc
        (m : ℝ) / (m : ℝ).log.sqrt ≤ (m : ℝ) / (n : ℝ).log.sqrt :=
          div_le_div_of_nonneg_left (Nat.cast_nonneg _) hlogpos hlogle
        _ ≤ (8 * (n : ℝ)) / (n : ℝ).log.sqrt := by gcongr; exact_mod_cast hm8
    _ = (C * 8) * ((n : ℝ) / (n : ℝ).log.sqrt) := by ring

open scoped EuclideanGeometry Classical

private lemma nat_dist_cast_abs (a b : ℕ) : (Nat.dist a b : ℝ) = |(a : ℝ) - b| := by
  rcases le_total a b with h | h
  · rw [Nat.dist_eq_sub_of_le h, Nat.cast_sub h, abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast h))]
    ring
  · rw [Nat.dist_eq_sub_of_le_right h, Nat.cast_sub h, abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast h))]

/-- Choose any n points of an m by m grid. Each squared distance is a sum of two squares. -/
private lemma grid_le_square_count (n m : ℕ) (hn : n ≤ m * m) :
    minimalDistinctDistances ℝ² n ≤
      ((Finset.range (2 * m ^ 2 + 1)).filter (fun t => ∃ a b : ℕ, t = a ^ 2 + b ^ 2)).card := by
  classical
  let pt (i : Fin m × Fin m) : ℝ² := !₂[(i.1.val : ℝ), (i.2.val : ℝ)]
  have hinj : Function.Injective pt := by
    intro i j h
    have h0 := congrArg (fun v : ℝ² => v 0) h
    have h1 := congrArg (fun v : ℝ² => v 1) h
    apply Prod.ext <;> apply Fin.ext
    · exact_mod_cast (show (i.1.val : ℝ) = j.1.val by simpa [pt] using h0)
    · exact_mod_cast (show (i.2.val : ℝ) = j.2.val by simpa [pt] using h1)
  let grid := Finset.univ.image pt
  have hcard : grid.card = m * m := by simp [grid, Finset.card_image_of_injective _ hinj]
  obtain ⟨A, hA, hAn⟩ := Finset.exists_subset_card_eq (s := grid) (n := n) (hcard ▸ hn)
  let T := (Finset.range (2 * m ^ 2 + 1)).filter (fun t => ∃ a b : ℕ, t = a ^ 2 + b ^ 2)
  have hdist (i j : Fin m × Fin m) :
      dist (pt i) (pt j) = Real.sqrt ((Nat.dist i.1.val j.1.val ^ 2 + Nat.dist i.2.val j.2.val ^ 2 : ℕ) : ℝ) := by
    rw [EuclideanSpace.dist_eq, Fin.sum_univ_two]
    simp [pt, Real.dist_eq, nat_dist_cast_abs]
  unfold minimalDistinctDistances
  apply le_trans (Nat.sInf_le (show distinctDistances A ∈
    {v : ℕ | ∃ a : Finset ℝ², a.card = n ∧ distinctDistances a = v} from
    ⟨A, hAn, rfl⟩))
  unfold distinctDistances distanceSet
  refine le_trans (Finset.card_le_card (t := T.image (fun t : ℕ => Real.sqrt (t : ℝ))) ?_) Finset.card_image_le
  rintro d hd
  obtain ⟨⟨p,q⟩, hpq, rfl⟩ := Finset.mem_image.mp hd
  obtain ⟨hp,hq,_⟩ := Finset.mem_offDiag.mp hpq
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (hA hp)
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp (hA hq)
  let a := Nat.dist i.1.val j.1.val
  let b := Nat.dist i.2.val j.2.val
  have ha : a ≤ m := by
    have := i.1.isLt
    have := j.1.isLt
    dsimp [a, Nat.dist]
    omega
  have hb : b ≤ m := by
    have := i.2.isLt
    have := j.2.isLt
    dsimp [b, Nat.dist]
    omega
  have hbound : a ^ 2 + b ^ 2 < 2 * m ^ 2 + 1 := by
    nlinarith [Nat.pow_le_pow_left ha 2, Nat.pow_le_pow_left hb 2]
  refine Finset.mem_image.mpr ⟨a ^ 2 + b ^ 2, Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr hbound, a, b, rfl⟩, ?_⟩
  rw [← hi, ← hj]
  exact (hdist i j).symm

theorem main : H1 → H2 →
    (fun n : ℕ => (minimalDistinctDistances ℝ² n : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ) / (n : ℝ).log.sqrt) := by
  intro harmonic weighted
  apply gridAsymptoticTransfer _ _ _ (count_asymptotic harmonic weighted)
  intro n
  have hside : n ≤ (n.sqrt + 1) * (n.sqrt + 1) := (Nat.lt_succ_sqrt n).le
  apply (grid_le_square_count n (n.sqrt + 1) hside).trans
  apply Finset.card_le_card
  intro t ht
  obtain ⟨hr, hsq⟩ := Finset.mem_filter.mp ht
  exact Finset.mem_filter.mpr ⟨hr, Nat.eq_sq_add_sq_iff.mp hsq⟩

end OMA.Grid89

/- Rankin's bound for harmonic sums of integers selected by an arithmetic condition. -/

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

/- The sum of the full logarithms of prime powers up to X is O(X). -/

open Finset Chebyshev ArithmeticFunction

namespace OMA.Grid604

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

end OMA.Grid604

/- Strip the entire prime-power component from a sum of two squares, then sum over its complement. -/

namespace OMA.Grid604Weighted

open Finset Filter

private abbrev admissible (n : ℕ) :=
  ∀ q ∈ n.primeFactors, q % 4 = 3 → Even (padicValNat q n)

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
        ∀ q ∈ m.primeFactors, q % 4 = 3 → Even (padicValNat q m))
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

end OMA.Grid604Weighted

open Filter Asymptotics
open scoped EuclideanGeometry

theorem OMA.solution : type_of% @Erdos661.erdos_661.variants.grid_upper_bound := by
  have grid := OMA.Grid89.main Grid604Harmonic.harmonicActual
    (OMA.Grid604Weighted.weighted_of_primePowers OMA.Grid604.prime_power_log_sum_linear)
  obtain ⟨C, hC, bound⟩ := grid.exists_nonneg
  obtain ⟨N, hN⟩ := eventually_atTop.mp bound.bound
  apply IsBigO.of_bound (2 * C)
  filter_upwards [eventually_ge_atTop (max 2 N)] with n hn
  have hn2 : 2 ≤ n := (le_max_left _ _).trans hn
  have hnN : N ≤ n := (le_max_right _ _).trans hn
  have h := hN (2*n) (by omega)
  have hn1 : 1 < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
  have hp : 0 < (Real.log n).sqrt := Real.sqrt_pos.mpr (Real.log_pos hn1)
  have hle : (Real.log n).sqrt ≤ (Real.log (2*n : ℕ)).sqrt :=
    Real.sqrt_le_sqrt (Real.log_le_log (by positivity) (by exact_mod_cast (show n ≤ 2*n by omega)))
  simp only [Real.norm_eq_abs, Nat.abs_cast,
    abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _))] at h ⊢
  calc
    _ ≤ (minimalDistinctDistances ℝ² (2*n) : ℝ) := by
      exact_mod_cast Erdos661.erdos_661.variants.le_minimalDistinctDistances n
    _ ≤ C * ((2*n : ℕ) / (Real.log (2*n : ℕ)).sqrt) := h
    _ ≤ C * ((2*n : ℕ) / (Real.log n).sqrt) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left (by positivity) hp hle) hC
    _ = 2 * C * ((n : ℝ) / (Real.log n).sqrt) := by push_cast; ring
