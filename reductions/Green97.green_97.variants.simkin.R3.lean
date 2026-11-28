import FormalConjectures.GreensOpenProblems.«97»
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
Reduction Green97.green_97.variants.simkin.R3 of Simkin's theorem (Simkin, Adv. Math. 427, 2023).
Credit: @mucoucah

S is the set of finite-grid step queenon entropy scores (the set of merged reduction R2).
Both numerical certificates are PROVED below without hypotheses:
- upper_certificate: every score is at most -1.94267 < -1.94 (explicit degree-4 polynomial
  dual certificate plus an exact one-dimensional duality identity);
- lower_witness: an explicit 12 x 12 step density has score > -1.9449 (adapted from PR 12951).
What remains is the variational counting principle, split into its two analytic halves:
- H1 (entropy upper bound, Simkin Sections 3-4): any upper bound u of S bounds the limsup of
  Q(n)^(1/n)/n by exp u;
- H2 (constructive lower bound, Simkin Section 5, random greedy plus absorber): every score t
  in S bounds the liminf by exp t.
main combines them at s = sSup S, which lies strictly in (-1.9449, -1.94) by the certificates.
Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
-/

open Filter Topology Finset

namespace OMA.R_Green97_green_97_variants_simkin_R3


/- Part 1: Uniform Dual Upper Certificate (`∀ r ∈ ({r | ∃ N : ℕ, 0 < N ∧ ∃ A : Fin N → Fin N → ℝ, let f := fun x : ℝ ↦ x * Real.log x; let d := fun (b : Bool) (k : ℕ) ↦ 1 - (∑ i : Fin N, ∑ j : Fin N, if i.val + j.val + 1 = k then A i (if b then j.rev else j) else 0) / N; (∀ i j, 0 ≤ A i j) ∧ (∀ i, ∑ j, A i j = N) ∧ (∀ j, ∑ i, A i j = N) ∧ (∀ b (k : Fin (2 * N + 1)), 0 ≤ d b k.val) ∧ r = -3 - (∑ i, ∑ j, f (A i j)) / (N : ℝ) ^ 2 - (∑ b : Bool, ∑ k : Fin (2 * N), ∫ t in (0 : ℝ)..1, f ((1 - t) * d b k.val + t * d b (k.val + 1))) / N} : Set ℝ), r ≤ u < -1.94`) -/

/-- Fenchel-Legendre inequality for `x ↦ x * log x`. -/
lemma neg_mul_log_le {x lam : ℝ} (hx : 0 ≤ x) :
    -(x * Real.log x) ≤ -lam * x + Real.exp (lam - 1) := by
  rcases eq_or_lt_of_le hx with rfl | hpos
  · simp [Real.exp_nonneg]
  · have h1 := Real.log_le_sub_one_of_pos (div_pos (Real.exp_pos (lam - 1)) hpos)
    rw [Real.log_div (Real.exp_pos _).ne' hpos.ne', Real.log_exp] at h1
    have h2 := mul_le_mul_of_nonneg_left h1 hpos.le
    have h3 : x * (Real.exp (lam - 1) / x - 1) = Real.exp (lam - 1) - x := by
      field_simp [hpos.ne']
    linarith

/-- Alternating Taylor remainder sign for `exp u` when `u ≤ 0`. -/
lemma taylor_exp_sign_nonpos : ∀ n : ℕ, ∀ u : ℝ, u ≤ 0 →
    0 ≤ (-1 : ℝ) ^ n *
      ((∑ k ∈ Finset.range (n + 1), u ^ k / (k.factorial : ℝ)) - Real.exp u) := by
  intro n
  induction n with
  | zero =>
    intro u hu
    simp only [pow_zero, one_mul, zero_add, Finset.sum_range_one, Nat.factorial_zero, Nat.cast_one, div_one, sub_nonneg]
    exact Real.exp_le_one_iff.mpr hu
  | succ n ih =>
    intro u hu
    let P : ℝ → ℝ := fun t ↦ ∑ k ∈ Finset.range (n + 2), t ^ k / (k.factorial : ℝ)
    let g : ℝ → ℝ := fun t ↦ (-1 : ℝ) ^ (n + 1) * (P t - Real.exp t)
    have hPderiv : ∀ t : ℝ, HasDerivAt P
        (∑ k ∈ Finset.range (n + 1), t ^ k / (k.factorial : ℝ)) t := by
      intro t
      have h1 : HasDerivAt (fun x ↦ ∑ k ∈ Finset.range (n + 2), x ^ k / (k.factorial : ℝ))
          (∑ k ∈ Finset.range (n + 2), ((k : ℝ) * t ^ (k - 1)) / (k.factorial : ℝ)) t := by
        apply HasDerivAt.fun_sum
        intro k _
        exact (hasDerivAt_pow k t).div_const (k.factorial : ℝ)
      convert h1 using 1
      rw [Finset.sum_range_succ' (f := fun k ↦ ((k : ℝ) * t ^ (k - 1)) / (k.factorial : ℝ))]
      simp only [Nat.cast_zero, zero_mul, zero_div, add_zero]
      apply Finset.sum_congr rfl
      intro k _
      rw [Nat.factorial_succ, Nat.cast_mul, Nat.add_sub_cancel]
      have hk : ((k + 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)
      field_simp [hk]
    have hgderiv : ∀ t : ℝ, HasDerivAt g
        ((-1 : ℝ) ^ (n + 1) *
          ((∑ k ∈ Finset.range (n + 1), t ^ k / (k.factorial : ℝ)) - Real.exp t)) t := by
      intro t
      exact ((hPderiv t).sub (Real.hasDerivAt_exp t)).const_mul _
    have hanti : AntitoneOn g (Set.Icc u 0) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc u 0)
      · exact (continuous_iff_continuousAt.mpr fun t ↦ (hgderiv t).continuousAt).continuousOn
      · exact fun t _ ↦ (hgderiv t).differentiableAt.differentiableWithinAt
      · intro t ht
        rw [(hgderiv t).deriv]
        have ht0 : t ≤ 0 := (interior_subset ht).2
        have hih := ih t ht0
        rw [pow_succ']
        linarith
    have h0 : g 0 = 0 := by
      dsimp only [g, P]
      rw [Finset.sum_range_succ']
      simp [Real.exp_zero]
    have hle : g 0 ≤ g u := hanti (Set.left_mem_Icc.mpr hu) (Set.right_mem_Icc.mpr hu) hu
    linarith

/-- Degree-8 Taylor upper bound for `exp u` when `u ≤ 0`. -/
lemma exp_le_poly8_of_nonpos {u : ℝ} (hu : u ≤ 0) :
    Real.exp u ≤ 1 + u + u ^ 2 / 2 + u ^ 3 / 6 + u ^ 4 / 24 + u ^ 5 / 120 +
      u ^ 6 / 720 + u ^ 7 / 5040 + u ^ 8 / 40320 := by
  have h := taylor_exp_sign_nonpos 8 u hu
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  linarith

/-- Degree-4 polynomial upper bound for `exp u` when `|u| ≤ 1`. -/
lemma exp_le_poly4_of_abs_le_one {u : ℝ} (hu : |u| ≤ 1) :
    Real.exp u ≤ 1 + u + u ^ 2 / 2 + u ^ 3 / 6 + (5 / 96 : ℝ) * u ^ 4 := by
  have h := Real.exp_bound hu (show 0 < 4 by norm_num)
  have hle := (abs_le.mp h).2
  have habs4 : |u| ^ 4 = u ^ 4 := by
    calc |u| ^ 4 = (|u| ^ 2) ^ 2 := by ring
      _ = (u ^ 2) ^ 2 := by rw [sq_abs]
      _ = u ^ 4 := by ring
  rw [habs4] at hle
  norm_num [Finset.sum_range_succ, Nat.factorial] at hle
  linarith

/-- Partition of `[0, m / N]` into `m` subintervals of width `1 / N`. -/
lemma sum_integral_grid {φ : ℝ → ℝ} (hφ : Continuous φ) {N : ℕ} :
    ∀ m : ℕ, ∑ i ∈ Finset.range m,
        ∫ x in ((i : ℝ) / N)..(((i + 1 : ℕ) : ℝ) / N), φ x =
      ∫ x in (0 : ℝ)..((m : ℝ) / N), φ x := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    exact intervalIntegral.integral_add_adjacent_intervals
      (hφ.intervalIntegrable _ _) (hφ.intervalIntegrable _ _)

/-- Partition of `[0, 1]` into `N` equal cells. -/
lemma sum_fin_integral_unit {φ : ℝ → ℝ} (hφ : Continuous φ) {N : ℕ} (hN : 0 < N) :
    ∑ i : Fin N, ∫ x in ((i.val : ℝ) / N)..(((i.val + 1 : ℕ) : ℝ) / N), φ x =
      ∫ x in (0 : ℝ)..1, φ x := by
  rw [Fin.sum_univ_eq_sum_range (fun i ↦ ∫ x in ((i : ℝ) / N)..(((i + 1 : ℕ) : ℝ) / N), φ x) N]
  rw [sum_integral_grid hφ N]
  have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  rw [div_self hN0]

/-- Partition of `[0, 2]` into `2 * N` equal cells. -/
lemma sum_fin_integral_two {φ : ℝ → ℝ} (hφ : Continuous φ) {N : ℕ} (hN : 0 < N) :
    ∑ k : Fin (2 * N), ∫ z in ((k.val : ℝ) / N)..(((k.val + 1 : ℕ) : ℝ) / N), φ z =
      ∫ z in (0 : ℝ)..2, φ z := by
  rw [Fin.sum_univ_eq_sum_range (fun k ↦ ∫ z in ((k : ℝ) / N)..(((k + 1 : ℕ) : ℝ) / N), φ z)
    (2 * N)]
  rw [sum_integral_grid hφ (2 * N)]
  have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have h2 : ((2 * N : ℕ) : ℝ) / (N : ℝ) = 2 := by push_cast; field_simp [hN0]
  rw [h2]

/-- Affine change of variables on a cell `[k / N, (k + 1) / N]`. -/
lemma integral_cell_subst {φ : ℝ → ℝ} {N : ℕ} (hN : 0 < N) (k : ℕ) :
    ∫ x in ((k : ℝ) / N)..(((k + 1 : ℕ) : ℝ) / N), φ x =
      (1 / (N : ℝ)) * ∫ t in (0 : ℝ)..1, φ (((k : ℝ) + t) / N) := by
  have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have h := intervalIntegral.integral_comp_mul_add (f := φ) (a := (0 : ℝ)) (b := 1)
    (c := (1 / (N : ℝ))) (d := ((k : ℝ) / N)) (by positivity)
  have heq : (fun t : ℝ ↦ φ ((1 / (N : ℝ)) * t + (k : ℝ) / N)) =
      fun t : ℝ ↦ φ (((k : ℝ) + t) / N) := by
    funext t; congr 1; ring
  rw [heq] at h
  have h0 : (1 / (N : ℝ)) * 0 + (k : ℝ) / N = (k : ℝ) / N := by ring
  have h1 : (1 / (N : ℝ)) * 1 + (k : ℝ) / N = ((k + 1 : ℕ) : ℝ) / N := by
    push_cast; ring
  rw [h0, h1, smul_eq_mul, one_div, inv_inv] at h
  have hmul := congrArg (fun z ↦ (1 / (N : ℝ)) * z) h
  rw [← mul_assoc, one_div_mul_cancel hN0, one_mul] at hmul
  exact hmul.symm

/-- Exact 1D-FTC tent identity for `∫_0^1 ∫_0^1 ψ (u + v) dv du`. -/
lemma tent_integral {ψ : ℝ → ℝ} (hψ : Continuous ψ) :
    ∫ u in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, ψ (u + v) =
      (∫ t in (0 : ℝ)..1, t * ψ t) + ∫ t in (0 : ℝ)..1, (1 - t) * ψ (1 + t) := by
  let Ψ : ℝ → ℝ := fun s ↦ ∫ r in (0 : ℝ)..s, ψ r
  let Φ : ℝ → ℝ := fun s ↦ ∫ r in (0 : ℝ)..s, Ψ r
  have hΨ : ∀ s : ℝ, HasDerivAt Ψ (ψ s) s := fun s ↦
    intervalIntegral.integral_hasDerivAt_right (hψ.intervalIntegrable _ _)
      (hψ.stronglyMeasurableAtFilter _ _) hψ.continuousAt
  have hΨc : Continuous Ψ := continuous_iff_continuousAt.mpr fun s ↦ (hΨ s).continuousAt
  have hΦ : ∀ s : ℝ, HasDerivAt Φ (Ψ s) s := fun s ↦
    intervalIntegral.integral_hasDerivAt_right (hΨc.intervalIntegrable _ _)
      (hΨc.stronglyMeasurableAtFilter _ _) hΨc.continuousAt
  have hinner : ∀ u : ℝ, ∫ v in (0 : ℝ)..1, ψ (u + v) = Ψ (u + 1) - Ψ u := by
    intro u
    have hd : ∀ v ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt (fun x ↦ Ψ (u + x)) (ψ (u + v)) v := by
      intro v _
      have h1 := (hΨ (u + v)).comp v ((hasDerivAt_id v).const_add u)
      simpa only [Function.comp_def, id_eq, mul_one] using h1
    have hc : IntervalIntegrable (fun v ↦ ψ (u + v)) MeasureTheory.volume 0 1 :=
      (hψ.comp (continuous_const.add continuous_id)).intervalIntegrable _ _
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc, add_zero]
  have hL : ∫ u in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, ψ (u + v) = Φ 2 - 2 * Φ 1 + Φ 0 := by
    simp_rw [hinner]
    have hd : ∀ u ∈ Set.uIcc (0 : ℝ) 1,
        HasDerivAt (fun x ↦ Φ (x + 1) - Φ x) (Ψ (u + 1) - Ψ u) u := by
      intro u _
      have h1 : HasDerivAt (fun x ↦ Φ (x + 1)) (Ψ (u + 1)) u := by
        simpa only [Function.comp_def, id_eq, mul_one] using
          (hΦ (u + 1)).comp u ((hasDerivAt_id u).add_const 1)
      exact h1.sub (hΦ u)
    have hc : IntervalIntegrable (fun u ↦ Ψ (u + 1) - Ψ u) MeasureTheory.volume 0 1 :=
      ((hΨc.comp (continuous_id.add continuous_const)).sub hΨc).intervalIntegrable _ _
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc]
    norm_num; ring
  have hR1 : ∫ t in (0 : ℝ)..1, t * ψ t = Ψ 1 - Φ 1 + Φ 0 := by
    have hd : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
        HasDerivAt (fun x ↦ x * Ψ x - Φ x) (t * ψ t) t := by
      intro t _
      have h1 : HasDerivAt (fun x ↦ x * Ψ x - Φ x) (1 * Ψ t + t * ψ t - Ψ t) t :=
        ((hasDerivAt_id t).mul (hΨ t)).sub (hΦ t)
      convert h1 using 1; ring
    have hc : IntervalIntegrable (fun t ↦ t * ψ t) MeasureTheory.volume 0 1 :=
      (continuous_id.mul hψ).intervalIntegrable _ _
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc]
    ring
  have hR2 : ∫ t in (0 : ℝ)..1, (1 - t) * ψ (1 + t) = Φ 2 - Ψ 1 - Φ 1 := by
    have hd : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
        HasDerivAt (fun x ↦ (1 - x) * Ψ (1 + x) + Φ (1 + x)) ((1 - t) * ψ (1 + t)) t := by
      intro t _
      have hsub : HasDerivAt (fun x : ℝ ↦ 1 - x) (0 - 1) t :=
        (hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)
      have hΨ1 : HasDerivAt (fun x ↦ Ψ (1 + x)) (ψ (1 + t)) t := by
        simpa only [Function.comp_def, id_eq, mul_one] using
          (hΨ (1 + t)).comp t ((hasDerivAt_id t).const_add 1)
      have hΦ1 : HasDerivAt (fun x ↦ Φ (1 + x)) (Ψ (1 + t)) t := by
        simpa only [Function.comp_def, id_eq, mul_one] using
          (hΦ (1 + t)).comp t ((hasDerivAt_id t).const_add 1)
      have htot : HasDerivAt (fun x ↦ (1 - x) * Ψ (1 + x) + Φ (1 + x))
          ((0 - 1) * Ψ (1 + t) + (1 - t) * ψ (1 + t) + Ψ (1 + t)) t :=
        (hsub.mul hΨ1).add hΦ1
      convert htot using 1; ring
    have hc : IntervalIntegrable (fun t ↦ (1 - t) * ψ (1 + t)) MeasureTheory.volume 0 1 :=
      ((continuous_const.sub continuous_id).mul
        (hψ.comp (continuous_const.add continuous_id))).intervalIntegrable _ _
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc]
    have h2 : (1 : ℝ) + 1 = 2 := by norm_num
    rw [h2]; simp only [sub_self, zero_mul, zero_add, sub_zero, one_mul, add_zero]
    ring
  linarith

/-- Cell integral of `γ (x + y)` rewritten via the tent identity. -/
lemma cell_diag_integral {γ : ℝ → ℝ} (hγ : Continuous γ) {N : ℕ} (hN : 0 < N) (i j : Fin N) :
    ∫ x in ((i.val : ℝ) / N)..(((i.val + 1 : ℕ) : ℝ) / N),
      ∫ y in ((j.val : ℝ) / N)..(((j.val + 1 : ℕ) : ℝ) / N), γ (x + y) =
    (1 / (N : ℝ) ^ 2) *
      ((∫ t in (0 : ℝ)..1, t * γ ((((i.val + j.val : ℕ) : ℝ) + t) / N)) +
       ∫ t in (0 : ℝ)..1, (1 - t) * γ ((((i.val + j.val + 1 : ℕ) : ℝ) + t) / N)) := by
  have hinner : ∀ x : ℝ,
      ∫ y in ((j.val : ℝ) / N)..(((j.val + 1 : ℕ) : ℝ) / N), γ (x + y) =
        (1 / (N : ℝ)) * ∫ v in (0 : ℝ)..1, γ (x + ((j.val : ℝ) + v) / N) :=
    fun x ↦ integral_cell_subst (φ := fun y ↦ γ (x + y)) hN j.val
  simp_rw [hinner]
  rw [intervalIntegral.integral_const_mul, integral_cell_subst hN i.val]
  have hring : ∀ u v : ℝ,
      ((i.val : ℝ) + u) / (N : ℝ) + ((j.val : ℝ) + v) / (N : ℝ) =
        (((i.val + j.val : ℕ) : ℝ) + (u + v)) / (N : ℝ) := by
    intro u v; push_cast; ring
  simp_rw [hring]
  let ψ : ℝ → ℝ := fun w ↦ γ ((((i.val + j.val : ℕ) : ℝ) + w) / N)
  have hψ : Continuous ψ := by fun_prop
  have ht := tent_integral hψ
  have h2 : ∀ t : ℝ, ψ (1 + t) = γ ((((i.val + j.val + 1 : ℕ) : ℝ) + t) / N) := by
    intro t; dsimp only [ψ]; congr 1; push_cast; ring
  simp_rw [h2] at ht
  calc (1 / (N : ℝ)) * ((1 / (N : ℝ)) * ∫ u in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, ψ (u + v))
      = (1 / (N : ℝ) ^ 2) * ∫ u in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, ψ (u + v) := by ring
    _ = _ := by rw [ht]

/-- Cell integral of `γ (x + 1 - y)` equals the cell integral of `γ (x + y)` at `j.rev`. -/
lemma cell_antidiag_integral {γ : ℝ → ℝ} {N : ℕ} (hN : 0 < N) (i j : Fin N) :
    ∫ x in ((i.val : ℝ) / N)..(((i.val + 1 : ℕ) : ℝ) / N),
      ∫ y in ((j.val : ℝ) / N)..(((j.val + 1 : ℕ) : ℝ) / N), γ (x + 1 - y) =
    ∫ x in ((i.val : ℝ) / N)..(((i.val + 1 : ℕ) : ℝ) / N),
      ∫ y in ((j.rev.val : ℝ) / N)..(((j.rev.val + 1 : ℕ) : ℝ) / N), γ (x + y) := by
  congr 1; funext x
  have h := intervalIntegral.integral_comp_sub_left (f := fun z ↦ γ (x + z)) (d := (1 : ℝ))
    (a := ((j.val : ℝ) / N)) (b := (((j.val + 1 : ℕ) : ℝ) / N))
  have heq : (fun y : ℝ ↦ γ (x + (1 - y))) = fun y : ℝ ↦ γ (x + 1 - y) := by
    funext y; congr 1; ring
  rw [heq] at h
  have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hj1 : j.val + 1 ≤ N := j.isLt
  have ha : (1 : ℝ) - ((j.val + 1 : ℕ) : ℝ) / N = (j.rev.val : ℝ) / N := by
    rw [Fin.val_rev, Nat.cast_sub hj1]
    field_simp [hN0]
  have hb : (1 : ℝ) - (j.val : ℝ) / N = ((j.rev.val + 1 : ℕ) : ℝ) / N := by
    rw [Fin.val_rev]
    have hnat : N - (j.val + 1) + 1 = N - j.val := by omega
    rw [hnat, Nat.cast_sub j.isLt.le]
    field_simp [hN0]
  rw [ha, hb] at h
  exact h

/-- Reindexing double cell sums into diagonal integrals against `1 - d`. -/
lemma sum_cell_diag_eq {γ : ℝ → ℝ} (hγ : Continuous γ) {N : ℕ} (hN : 0 < N)
    (B : Fin N → Fin N → ℝ) :
    let d := fun k : ℕ ↦ 1 - (∑ i : Fin N, ∑ j : Fin N,
      if i.val + j.val + 1 = k then B i j else 0) / N
    ∑ i : Fin N, ∑ j : Fin N, B i j *
      (∫ x in ((i.val : ℝ) / N)..(((i.val + 1 : ℕ) : ℝ) / N),
        ∫ y in ((j.val : ℝ) / N)..(((j.val + 1 : ℕ) : ℝ) / N), γ (x + y)) =
    (∫ z in (0 : ℝ)..2, γ z) -
      (∑ k : Fin (2 * N), ∫ t in (0 : ℝ)..1,
        ((1 - t) * d k.val + t * d (k.val + 1)) * γ (((k.val : ℝ) + t) / N)) / N := by
  intro d
  have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  let I1 : ℕ → ℝ := fun k ↦ ∫ t in (0 : ℝ)..1, t * γ (((k : ℝ) + t) / N)
  let I2 : ℕ → ℝ := fun k ↦ ∫ t in (0 : ℝ)..1, (1 - t) * γ (((k : ℝ) + t) / N)
  have hstep1 :
      ∑ i : Fin N, ∑ j : Fin N, B i j *
        (∫ x in ((i.val : ℝ) / N)..(((i.val + 1 : ℕ) : ℝ) / N),
          ∫ y in ((j.val : ℝ) / N)..(((j.val + 1 : ℕ) : ℝ) / N), γ (x + y)) =
      (1 / (N : ℝ) ^ 2) * (∑ i : Fin N, ∑ j : Fin N, B i j * I1 (i.val + j.val)) +
      (1 / (N : ℝ) ^ 2) * (∑ i : Fin N, ∑ j : Fin N, B i j * I2 (i.val + j.val + 1)) := by
    simp_rw [cell_diag_integral hγ hN]
    simp_rw [← mul_assoc, mul_comm (B _ _) (1 / (N : ℝ) ^ 2), mul_assoc, ← Finset.mul_sum, mul_add, Finset.sum_add_distrib, mul_add]
    rfl
  have hS1 : ∑ i : Fin N, ∑ j : Fin N, B i j * I1 (i.val + j.val) =
      ∑ k : Fin (2 * N),
        (∑ i : Fin N, ∑ j : Fin N, if i.val + j.val + 1 = k.val + 1 then B i j else 0) *
          I1 k.val := by
    have h1 : ∀ i j : Fin N, B i j * I1 (i.val + j.val) =
        ∑ k : Fin (2 * N), if i.val + j.val + 1 = k.val + 1 then B i j * I1 k.val else 0 := by
      intro i j
      have hlt : i.val + j.val < 2 * N := by omega
      rw [Finset.sum_eq_single ⟨i.val + j.val, hlt⟩]
      · simp
      · intro k _ hk
        have hne : i.val + j.val + 1 ≠ k.val + 1 := by
          intro heq; apply hk; ext; dsimp; omega
        rw [if_neg hne]
      · intro h; exact absurd (Finset.mem_univ _) h
    simp_rw [h1]
    conv_lhs =>
      arg 2; ext i
      rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> ring
  have hS2 : ∑ i : Fin N, ∑ j : Fin N, B i j * I2 (i.val + j.val + 1) =
      ∑ k : Fin (2 * N),
        (∑ i : Fin N, ∑ j : Fin N, if i.val + j.val + 1 = k.val then B i j else 0) *
          I2 k.val := by
    have h1 : ∀ i j : Fin N, B i j * I2 (i.val + j.val + 1) =
        ∑ k : Fin (2 * N), if i.val + j.val + 1 = k.val then B i j * I2 k.val else 0 := by
      intro i j
      have hlt : i.val + j.val + 1 < 2 * N := by omega
      rw [Finset.sum_eq_single ⟨i.val + j.val + 1, hlt⟩]
      · simp
      · intro k _ hk
        have hne : i.val + j.val + 1 ≠ k.val := by
          intro heq; apply hk; ext; dsimp; omega
        rw [if_neg hne]
      · intro h; exact absurd (Finset.mem_univ _) h
    simp_rw [h1]
    conv_lhs =>
      arg 2; ext i
      rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> ring
  have hcomb : ∀ k : Fin (2 * N),
      (1 / (N : ℝ) ^ 2) *
        ((∑ i : Fin N, ∑ j : Fin N, if i.val + j.val + 1 = k.val + 1 then B i j else 0) *
          I1 k.val +
         (∑ i : Fin N, ∑ j : Fin N, if i.val + j.val + 1 = k.val then B i j else 0) *
          I2 k.val) =
      (∫ z in ((k.val : ℝ) / N)..(((k.val + 1 : ℕ) : ℝ) / N), γ z) -
        (∫ t in (0 : ℝ)..1,
          ((1 - t) * d k.val + t * d (k.val + 1)) * γ (((k.val : ℝ) + t) / N)) / N := by
    intro k
    have hd1 : (∑ i : Fin N, ∑ j : Fin N,
        if i.val + j.val + 1 = k.val + 1 then B i j else 0) = (N : ℝ) * (1 - d (k.val + 1)) := by
      dsimp only [d]; field_simp [hN0]; ring
    have hd0 : (∑ i : Fin N, ∑ j : Fin N,
        if i.val + j.val + 1 = k.val then B i j else 0) = (N : ℝ) * (1 - d k.val) := by
      dsimp only [d]; field_simp [hN0]; ring
    rw [hd1, hd0, integral_cell_subst hN k.val]
    have hcont1 : Continuous (fun t : ℝ ↦ t * γ (((k.val : ℝ) + t) / N)) := by fun_prop
    have hcont2 : Continuous (fun t : ℝ ↦ (1 - t) * γ (((k.val : ℝ) + t) / N)) := by fun_prop
    have hcont3 : Continuous (fun t : ℝ ↦ γ (((k.val : ℝ) + t) / N)) := by fun_prop
    have hcont4 : Continuous (fun t : ℝ ↦
        ((1 - t) * d k.val + t * d (k.val + 1)) * γ (((k.val : ℝ) + t) / N)) := by fun_prop
    have hint : (1 - d (k.val + 1)) * I1 k.val + (1 - d k.val) * I2 k.val =
        (∫ t in (0 : ℝ)..1, γ (((k.val : ℝ) + t) / N)) -
        ∫ t in (0 : ℝ)..1, ((1 - t) * d k.val + t * d (k.val + 1)) * γ (((k.val : ℝ) + t) / N) := by
      dsimp only [I1, I2]
      rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add (hcont1.const_mul _ |>.intervalIntegrable _ _)
          (hcont2.const_mul _ |>.intervalIntegrable _ _), ← intervalIntegral.integral_sub (hcont3.intervalIntegrable _ _)
          (hcont4.intervalIntegrable _ _)]
      congr 1; funext t; ring
    calc (1 / (N : ℝ) ^ 2) *
          ((N : ℝ) * (1 - d (k.val + 1)) * I1 k.val + (N : ℝ) * (1 - d k.val) * I2 k.val)
        = (1 / (N : ℝ)) * ((1 - d (k.val + 1)) * I1 k.val + (1 - d k.val) * I2 k.val) := by
          field_simp [hN0]
      _ = (1 / (N : ℝ)) * ((∫ t in (0 : ℝ)..1, γ (((k.val : ℝ) + t) / N)) -
          ∫ t in (0 : ℝ)..1,
            ((1 - t) * d k.val + t * d (k.val + 1)) * γ (((k.val : ℝ) + t) / N)) := by
          rw [hint]
      _ = _ := by ring
  rw [hstep1, hS1, hS2, ← mul_add, ← Finset.sum_add_distrib, Finset.mul_sum]
  simp_rw [hcomb]
  rw [Finset.sum_sub_distrib, ← Finset.sum_div, sum_fin_integral_two hγ hN]


lemma duality_upper_bound {α γ : ℝ → ℝ} (hα : Continuous α) (hγ : Continuous γ)
    {r : ℝ} (hr : r ∈ ({r | ∃ N : ℕ, 0 < N ∧ ∃ A : Fin N → Fin N → ℝ, let f := fun x : ℝ ↦ x * Real.log x; let d := fun (b : Bool) (k : ℕ) ↦ 1 - (∑ i : Fin N, ∑ j : Fin N, if i.val + j.val + 1 = k then A i (if b then j.rev else j) else 0) / N; (∀ i j, 0 ≤ A i j) ∧ (∀ i, ∑ j, A i j = N) ∧ (∀ j, ∑ i, A i j = N) ∧ (∀ b (k : Fin (2 * N + 1)), 0 ≤ d b k.val) ∧ r = -3 - (∑ i, ∑ j, f (A i j)) / (N : ℝ) ^ 2 - (∑ b : Bool, ∑ k : Fin (2 * N), ∫ t in (0 : ℝ)..1, f ((1 - t) * d b k.val + t * d b (k.val + 1))) / N} : Set ℝ)) :
    r ≤ -3 - 2 * (∫ x in (0 : ℝ)..1, α x) - 2 * (∫ z in (0 : ℝ)..2, γ z) +
      2 * (∫ z in (0 : ℝ)..2, Real.exp (γ z - 1)) +
      ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1,
        Real.exp (α x + α y + γ (x + y) + γ (x + 1 - y) - 1) := by
  rcases hr with ⟨N, hN, A, hAnon, hrow, hcol, hdnon, rfl⟩
  have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  let f : ℝ → ℝ := fun x ↦ x * Real.log x
  let d : Bool → ℕ → ℝ := fun b k ↦ 1 - (∑ i : Fin N, ∑ j : Fin N,
    if i.val + j.val + 1 = k then A i (if b then j.rev else j) else 0) / N
  let H : ℝ → ℝ → ℝ := fun x y ↦ α x + α y + γ (x + y) + γ (x + 1 - y) - 1
  have hcell : ∀ i j : Fin N,
      -f (A i j) / (N : ℝ) ^ 2 ≤
        -(A i j / (N : ℝ)) * (∫ x in ((i.val : ℝ) / N)..(((i.val + 1 : ℕ) : ℝ) / N), α x) -
        (A i j / (N : ℝ)) * (∫ y in ((j.val : ℝ) / N)..(((j.val + 1 : ℕ) : ℝ) / N), α y) -
        A i j * (∫ x in ((i.val : ℝ) / N)..(((i.val + 1 : ℕ) : ℝ) / N),
          ∫ y in ((j.val : ℝ) / N)..(((j.val + 1 : ℕ) : ℝ) / N), γ (x + y)) -
        A i j * (∫ x in ((i.val : ℝ) / N)..(((i.val + 1 : ℕ) : ℝ) / N),
          ∫ y in ((j.val : ℝ) / N)..(((j.val + 1 : ℕ) : ℝ) / N), γ (x + 1 - y)) +
        ∫ x in ((i.val : ℝ) / N)..(((i.val + 1 : ℕ) : ℝ) / N),
          ∫ y in ((j.val : ℝ) / N)..(((j.val + 1 : ℕ) : ℝ) / N), Real.exp (H x y) := by
    intro i j
    have ha_le : ((i.val : ℝ) / N) ≤ ((i.val + 1 : ℕ) : ℝ) / N := by
      apply div_le_div_of_nonneg_right _ hNpos.le; push_cast; linarith
    have hb_le : ((j.val : ℝ) / N) ≤ ((j.val + 1 : ℕ) : ℝ) / N := by
      apply div_le_div_of_nonneg_right _ hNpos.le; push_cast; linarith
    have hpt : ∀ x y : ℝ, -f (A i j) ≤
        -A i j * (α x + α y + γ (x + y) + γ (x + 1 - y)) + Real.exp (H x y) := by
      intro x y
      have := neg_mul_log_le (lam := α x + α y + γ (x + y) + γ (x + 1 - y)) (hAnon i j)
      dsimp only [f, H]
      linarith
    have hinner : ∀ x : ℝ,
        ∫ y in ((j.val : ℝ) / N)..(((j.val + 1 : ℕ) : ℝ) / N), (-f (A i j)) ≤
        ∫ y in ((j.val : ℝ) / N)..(((j.val + 1 : ℕ) : ℝ) / N),
          (-A i j * (α x + α y + γ (x + y) + γ (x + 1 - y)) + Real.exp (H x y)) := by
      intro x
      apply intervalIntegral.integral_mono_on hb_le
      · exact continuous_const.intervalIntegrable _ _
      · have hcont : Continuous (fun y ↦ -A i j * (α x + α y + γ (x + y) + γ (x + 1 - y)) +
            Real.exp (H x y)) := by fun_prop
        exact hcont.intervalIntegrable _ _
      · intro y _; exact hpt x y
    have houter :
        ∫ x in ((i.val : ℝ) / N)..(((i.val + 1 : ℕ) : ℝ) / N),
          ∫ y in ((j.val : ℝ) / N)..(((j.val + 1 : ℕ) : ℝ) / N), (-f (A i j)) ≤
        ∫ x in ((i.val : ℝ) / N)..(((i.val + 1 : ℕ) : ℝ) / N),
          ∫ y in ((j.val : ℝ) / N)..(((j.val + 1 : ℕ) : ℝ) / N),
            (-A i j * (α x + α y + γ (x + y) + γ (x + 1 - y)) + Real.exp (H x y)) := by
      apply intervalIntegral.integral_mono_on ha_le
      · exact continuous_const.intervalIntegrable _ _
      · have hcont : Continuous (fun x ↦
            ∫ y in ((j.val : ℝ) / N)..(((j.val + 1 : ℕ) : ℝ) / N),
              (-A i j * (α x + α y + γ (x + y) + γ (x + 1 - y)) + Real.exp (H x y))) := by
          apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
          fun_prop
        exact hcont.intervalIntegrable _ _
      · intro x _; exact hinner x
    have hwidth_i : ((i.val + 1 : ℕ) : ℝ) / N - (i.val : ℝ) / N = 1 / (N : ℝ) := by
      push_cast; field_simp [hN0]; ring
    have hwidth_j : ((j.val + 1 : ℕ) : ℝ) / N - (j.val : ℝ) / N = 1 / (N : ℝ) := by
      push_cast; field_simp [hN0]; ring
    have hLHS :
        ∫ x in ((i.val : ℝ) / N)..(((i.val + 1 : ℕ) : ℝ) / N),
          ∫ y in ((j.val : ℝ) / N)..(((j.val + 1 : ℕ) : ℝ) / N), (-f (A i j)) =
        -f (A i j) / (N : ℝ) ^ 2 := by
      simp only [intervalIntegral.integral_const, smul_eq_mul, hwidth_i, hwidth_j]
      ring
    have hRHS_in : ∀ x : ℝ,
        ∫ y in ((j.val : ℝ) / N)..(((j.val + 1 : ℕ) : ℝ) / N),
          (-A i j * (α x + α y + γ (x + y) + γ (x + 1 - y)) + Real.exp (H x y)) =
        (-A i j * α x / (N : ℝ)) +
        (-A i j * ∫ y in ((j.val : ℝ) / N)..(((j.val + 1 : ℕ) : ℝ) / N), α y) +
        (-A i j * ∫ y in ((j.val : ℝ) / N)..(((j.val + 1 : ℕ) : ℝ) / N), γ (x + y)) +
        (-A i j * ∫ y in ((j.val : ℝ) / N)..(((j.val + 1 : ℕ) : ℝ) / N), γ (x + 1 - y)) +
        ∫ y in ((j.val : ℝ) / N)..(((j.val + 1 : ℕ) : ℝ) / N), Real.exp (H x y) := by
      intro x
      have hsplit : (fun y ↦ -A i j * (α x + α y + γ (x + y) + γ (x + 1 - y)) + Real.exp (H x y)) =
          fun y ↦ ((((-A i j * α x) + (-A i j * α y)) + (-A i j * γ (x + y))) +
            (-A i j * γ (x + 1 - y))) + Real.exp (H x y) := by funext y; ring
      rw [hsplit]
      rw [intervalIntegral.integral_add
            ((by fun_prop : Continuous fun y : ℝ ↦
              (((-A i j * α x) + (-A i j * α y)) + (-A i j * γ (x + y))) +
                (-A i j * γ (x + 1 - y))).intervalIntegrable _ _)
            ((by fun_prop : Continuous fun y : ℝ ↦ Real.exp (H x y)).intervalIntegrable _ _), intervalIntegral.integral_add
            ((by fun_prop : Continuous fun y : ℝ ↦
              ((-A i j * α x) + (-A i j * α y)) + (-A i j * γ (x + y))).intervalIntegrable _ _)
            ((by fun_prop : Continuous fun y : ℝ ↦ -A i j * γ (x + 1 - y)).intervalIntegrable _ _), intervalIntegral.integral_add
            ((by fun_prop : Continuous fun y : ℝ ↦
              (-A i j * α x) + (-A i j * α y)).intervalIntegrable _ _)
            ((by fun_prop : Continuous fun y : ℝ ↦ -A i j * γ (x + y)).intervalIntegrable _ _), intervalIntegral.integral_add
            (continuous_const.intervalIntegrable _ _)
            ((by fun_prop : Continuous fun y : ℝ ↦ -A i j * α y).intervalIntegrable _ _), intervalIntegral.integral_const, smul_eq_mul, hwidth_j, intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
      ring
    simp_rw [hRHS_in] at houter
    have hg1 : Continuous (fun x : ℝ ↦ -A i j * α x / (N : ℝ)) := by fun_prop
    have hg2 : Continuous (fun _ : ℝ ↦
        -A i j * ∫ y in ((j.val : ℝ) / N)..(((j.val + 1 : ℕ) : ℝ) / N), α y) := continuous_const
    have hg3 : Continuous (fun x : ℝ ↦
        -A i j * ∫ y in ((j.val : ℝ) / N)..(((j.val + 1 : ℕ) : ℝ) / N), γ (x + y)) :=
      continuous_const.mul
        (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (by fun_prop) _ _)
    have hg4 : Continuous (fun x : ℝ ↦
        -A i j * ∫ y in ((j.val : ℝ) / N)..(((j.val + 1 : ℕ) : ℝ) / N), γ (x + 1 - y)) :=
      continuous_const.mul
        (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (by fun_prop) _ _)
    have hg5 : Continuous (fun x : ℝ ↦
        ∫ y in ((j.val : ℝ) / N)..(((j.val + 1 : ℕ) : ℝ) / N), Real.exp (H x y)) :=
      intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (by fun_prop) _ _
    have hg12 : Continuous (fun x : ℝ ↦ -A i j * α x / (N : ℝ) +
        -A i j * ∫ y in ((j.val : ℝ) / N)..(((j.val + 1 : ℕ) : ℝ) / N), α y) := hg1.add hg2
    have hg123 : Continuous (fun x : ℝ ↦ (-A i j * α x / (N : ℝ) +
        -A i j * ∫ y in ((j.val : ℝ) / N)..(((j.val + 1 : ℕ) : ℝ) / N), α y) +
        -A i j * ∫ y in ((j.val : ℝ) / N)..(((j.val + 1 : ℕ) : ℝ) / N), γ (x + y)) :=
      hg12.add hg3
    have hg1234 : Continuous (fun x : ℝ ↦ ((-A i j * α x / (N : ℝ) +
        -A i j * ∫ y in ((j.val : ℝ) / N)..(((j.val + 1 : ℕ) : ℝ) / N), α y) +
        -A i j * ∫ y in ((j.val : ℝ) / N)..(((j.val + 1 : ℕ) : ℝ) / N), γ (x + y)) +
        -A i j * ∫ y in ((j.val : ℝ) / N)..(((j.val + 1 : ℕ) : ℝ) / N), γ (x + 1 - y)) :=
      hg123.add hg4
    rw [hLHS, intervalIntegral.integral_add (hg1234.intervalIntegrable _ _) (hg5.intervalIntegrable _ _), intervalIntegral.integral_add (hg123.intervalIntegrable _ _) (hg4.intervalIntegrable _ _), intervalIntegral.integral_add (hg12.intervalIntegrable _ _) (hg3.intervalIntegrable _ _), intervalIntegral.integral_add (hg1.intervalIntegrable _ _) (hg2.intervalIntegrable _ _), intervalIntegral.integral_const, smul_eq_mul, hwidth_i, intervalIntegral.integral_div, intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at houter
    exact houter.trans (le_of_eq (by ring))
  have hsumA := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) ↦
    Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) ↦ hcell i j
  have hT_lhs : ∑ i : Fin N, ∑ j : Fin N, (-f (A i j) / (N : ℝ) ^ 2) =
      -(∑ i : Fin N, ∑ j : Fin N, f (A i j)) / (N : ℝ) ^ 2 := by
    simp only [neg_div, Finset.sum_neg_distrib, ← Finset.sum_div]
  have hT_row : ∑ i : Fin N, ∑ j : Fin N,
      -(A i j / (N : ℝ)) * (∫ x in ((i.val : ℝ) / N)..(((i.val + 1 : ℕ) : ℝ) / N), α x) =
      -(∫ x in (0 : ℝ)..1, α x) := by
    simp only [neg_mul, Finset.sum_neg_distrib]
    congr 1
    rw [← sum_fin_integral_unit hα hN]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_mul, ← Finset.sum_div, hrow i, div_self hN0, one_mul]
  have hT_col : ∑ i : Fin N, ∑ j : Fin N,
      (A i j / (N : ℝ)) * (∫ y in ((j.val : ℝ) / N)..(((j.val + 1 : ℕ) : ℝ) / N), α y) =
      ∫ y in (0 : ℝ)..1, α y := by
    rw [Finset.sum_comm, ← sum_fin_integral_unit hα hN]
    apply Finset.sum_congr rfl
    intro j _
    rw [← Finset.sum_mul, ← Finset.sum_div, hcol j, div_self hN0, one_mul]
  have hT_exp : ∑ i : Fin N, ∑ j : Fin N,
      ∫ x in ((i.val : ℝ) / N)..(((i.val + 1 : ℕ) : ℝ) / N),
        ∫ y in ((j.val : ℝ) / N)..(((j.val + 1 : ℕ) : ℝ) / N), Real.exp (H x y) =
      ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, Real.exp (H x y) := by
    have hinner_sum : ∀ i : Fin N,
        ∑ j : Fin N, ∫ x in ((i.val : ℝ) / N)..(((i.val + 1 : ℕ) : ℝ) / N),
          ∫ y in ((j.val : ℝ) / N)..(((j.val + 1 : ℕ) : ℝ) / N), Real.exp (H x y) =
        ∫ x in ((i.val : ℝ) / N)..(((i.val + 1 : ℕ) : ℝ) / N),
          ∫ y in (0 : ℝ)..1, Real.exp (H x y) := by
      intro i
      rw [← intervalIntegral.integral_finsetSum]
      · congr 1; funext x
        exact sum_fin_integral_unit (φ := fun y ↦ Real.exp (H x y)) (by fun_prop) hN
      · intro j _
        exact (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
          (by fun_prop) _ _).intervalIntegrable _ _
    simp_rw [hinner_sum]
    exact sum_fin_integral_unit
      (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (by fun_prop) _ _) hN
  have hT_diag0 : ∑ i : Fin N, ∑ j : Fin N, A i j *
      (∫ x in ((i.val : ℝ) / N)..(((i.val + 1 : ℕ) : ℝ) / N),
        ∫ y in ((j.val : ℝ) / N)..(((j.val + 1 : ℕ) : ℝ) / N), γ (x + y)) =
      (∫ z in (0 : ℝ)..2, γ z) -
      (∑ k : Fin (2 * N), ∫ t in (0 : ℝ)..1,
        ((1 - t) * d false k.val + t * d false (k.val + 1)) * γ (((k.val : ℝ) + t) / N)) / N := by
    simpa [d] using sum_cell_diag_eq hγ hN (fun i j ↦ A i j)
  have hT_diag1 : ∑ i : Fin N, ∑ j : Fin N, A i j *
      (∫ x in ((i.val : ℝ) / N)..(((i.val + 1 : ℕ) : ℝ) / N),
        ∫ y in ((j.val : ℝ) / N)..(((j.val + 1 : ℕ) : ℝ) / N), γ (x + 1 - y)) =
      (∫ z in (0 : ℝ)..2, γ z) -
      (∑ k : Fin (2 * N), ∫ t in (0 : ℝ)..1,
        ((1 - t) * d true k.val + t * d true (k.val + 1)) * γ (((k.val : ℝ) + t) / N)) / N := by
    have hrev : ∑ i : Fin N, ∑ j : Fin N, A i j *
        (∫ x in ((i.val : ℝ) / N)..(((i.val + 1 : ℕ) : ℝ) / N),
          ∫ y in ((j.val : ℝ) / N)..(((j.val + 1 : ℕ) : ℝ) / N), γ (x + 1 - y)) =
        ∑ i : Fin N, ∑ j : Fin N, A i j.rev *
        (∫ x in ((i.val : ℝ) / N)..(((i.val + 1 : ℕ) : ℝ) / N),
          ∫ y in ((j.val : ℝ) / N)..(((j.val + 1 : ℕ) : ℝ) / N), γ (x + y)) := by
      apply Finset.sum_congr rfl; intro i _
      simp_rw [cell_antidiag_integral hN i]
      exact Fintype.sum_equiv (Equiv.ofBijective Fin.rev Fin.rev_bijective) _ _ (fun j ↦ by simp)
    rw [hrev]
    simpa [d] using sum_cell_diag_eq hγ hN (fun i j ↦ A i j.rev)
  have hdiag_bound : ∀ b : Bool,
      -(∑ k : Fin (2 * N), ∫ t in (0 : ℝ)..1,
        f ((1 - t) * d b k.val + t * d b (k.val + 1))) / N ≤
      -(∑ k : Fin (2 * N), ∫ t in (0 : ℝ)..1,
        ((1 - t) * d b k.val + t * d b (k.val + 1)) * γ (((k.val : ℝ) + t) / N)) / N +
      ∫ z in (0 : ℝ)..2, Real.exp (γ z - 1) := by
    intro b
    have hk : ∀ k : Fin (2 * N),
        -(∫ t in (0 : ℝ)..1, f ((1 - t) * d b k.val + t * d b (k.val + 1))) ≤
        -(∫ t in (0 : ℝ)..1,
          ((1 - t) * d b k.val + t * d b (k.val + 1)) * γ (((k.val : ℝ) + t) / N)) +
        ∫ t in (0 : ℝ)..1, Real.exp (γ (((k.val : ℝ) + t) / N) - 1) := by
      intro k
      rw [← intervalIntegral.integral_neg, ← intervalIntegral.integral_neg, ← intervalIntegral.integral_add
          ((by fun_prop : Continuous fun t : ℝ ↦
            -(((1 - t) * d b k.val + t * d b (k.val + 1)) *
              γ (((k.val : ℝ) + t) / N))).intervalIntegrable _ _)
          ((by fun_prop : Continuous fun t : ℝ ↦
            Real.exp (γ (((k.val : ℝ) + t) / N) - 1)).intervalIntegrable _ _)]
      apply intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
      · have hcf : Continuous (fun t : ℝ ↦ -f ((1 - t) * d b k.val + t * d b (k.val + 1))) := by
          dsimp only [f]; exact (Real.continuous_mul_log.comp (by fun_prop)).neg
        exact hcf.intervalIntegrable _ _
      · exact (by fun_prop : Continuous fun t : ℝ ↦
          -(((1 - t) * d b k.val + t * d b (k.val + 1)) * γ (((k.val : ℝ) + t) / N)) +
          Real.exp (γ (((k.val : ℝ) + t) / N) - 1)).intervalIntegrable _ _
      · intro t ht
        have hd0 : 0 ≤ d b k.val := hdnon b ⟨k.val, by omega⟩
        have hd1 : 0 ≤ d b (k.val + 1) := hdnon b ⟨k.val + 1, by omega⟩
        have hlin : 0 ≤ (1 - t) * d b k.val + t * d b (k.val + 1) :=
          add_nonneg (mul_nonneg (sub_nonneg.mpr ht.2) hd0) (mul_nonneg ht.1 hd1)
        have := neg_mul_log_le (lam := γ (((k.val : ℝ) + t) / N)) hlin
        dsimp only [f]
        linarith
    have hsumk := Finset.sum_le_sum fun k (_ : k ∈ Finset.univ) ↦ hk k
    rw [Finset.sum_neg_distrib, Finset.sum_add_distrib, Finset.sum_neg_distrib] at hsumk
    have hdiv := div_le_div_of_nonneg_right hsumk hNpos.le
    have hexp_sum : (∑ k : Fin (2 * N),
        ∫ t in (0 : ℝ)..1, Real.exp (γ (((k.val : ℝ) + t) / N) - 1)) / (N : ℝ) =
        ∫ z in (0 : ℝ)..2, Real.exp (γ z - 1) := by
      rw [← sum_fin_integral_two (φ := fun z ↦ Real.exp (γ z - 1)) (by fun_prop) hN]
      simp_rw [integral_cell_subst hN]
      rw [← Finset.mul_sum]; ring
    linarith [hdiv, hexp_sum, add_div
      (-(∑ k : Fin (2 * N), ∫ t in (0 : ℝ)..1,
        ((1 - t) * d b k.val + t * d b (k.val + 1)) * γ (((k.val : ℝ) + t) / N)))
      (∑ k : Fin (2 * N), ∫ t in (0 : ℝ)..1, Real.exp (γ (((k.val : ℝ) + t) / N) - 1))
      (N : ℝ)]
  have hsumA' :
      -((∑ i : Fin N, ∑ j : Fin N, f (A i j)) / (N : ℝ) ^ 2) ≤
      -2 * (∫ x in (0 : ℝ)..1, α x) - 2 * (∫ z in (0 : ℝ)..2, γ z) +
      (∑ k : Fin (2 * N), ∫ t in (0 : ℝ)..1,
        ((1 - t) * d false k.val + t * d false (k.val + 1)) * γ (((k.val : ℝ) + t) / N)) / N +
      (∑ k : Fin (2 * N), ∫ t in (0 : ℝ)..1,
        ((1 - t) * d true k.val + t * d true (k.val + 1)) * γ (((k.val : ℝ) + t) / N)) / N +
      ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, Real.exp (H x y) := by
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib] at hsumA
    rw [hT_lhs, hT_row, hT_col, hT_diag0, hT_diag1, hT_exp, neg_div] at hsumA
    linarith
  have hbool :
      -((∑ b : Bool, ∑ k : Fin (2 * N), ∫ t in (0 : ℝ)..1,
        f ((1 - t) * d b k.val + t * d b (k.val + 1))) / N) =
      -((∑ k : Fin (2 * N), ∫ t in (0 : ℝ)..1,
        f ((1 - t) * d true k.val + t * d true (k.val + 1))) / N) +
      -((∑ k : Fin (2 * N), ∫ t in (0 : ℝ)..1,
        f ((1 - t) * d false k.val + t * d false (k.val + 1))) / N) := by
    rw [Fintype.sum_bool]; ring
  have hd_true := hdiag_bound true
  have hd_false := hdiag_bound false
  rw [neg_div, neg_div] at hd_true hd_false
  dsimp only [f, d, H] at hsumA' hbool hd_true hd_false ⊢
  linarith

/- Part 2: Explicit Degree-4 Polynomial Dual Certificate -/



private lemma integral_even_pow_unit (k : ℕ) :
    ∫ w in (-1 : ℝ)..1, w ^ (2 * k) = 2 / (2 * k + 1 : ℝ) := by
  rw [integral_pow]
  have hneg : (-1 : ℝ) ^ (2 * k + 1) = -1 := by
    rw [pow_succ, pow_mul]; norm_num
  rw [one_pow, hneg]
  push_cast; ring

private lemma integral_even_pow_half (k : ℕ) :
    ∫ u in (-(1 / 2) : ℝ)..(1 / 2), u ^ (2 * k) = 1 / ((2 * k + 1 : ℝ) * 4 ^ k) := by
  rw [integral_pow]
  have h1 : (-(1 / 2) : ℝ) ^ (2 * k + 1) = -((1 / 2 : ℝ) ^ (2 * k + 1)) :=
    Odd.neg_pow ⟨k, rfl⟩ (1 / 2 : ℝ)
  have h2 : (1 / 2 : ℝ) ^ (2 * k + 1) = (1 / 2) * (1 / 4 : ℝ) ^ k := by
    rw [pow_succ, pow_mul]; norm_num; ring
  rw [h1, h2]
  have h4 : (4 : ℝ) ^ k ≠ 0 := by positivity
  have h2k : (2 * (k : ℝ) + 1) ≠ 0 := by positivity
  rw [one_div_pow]
  push_cast
  field_simp [h4, h2k]
  ring

private lemma integral_sum_even_pow_unit {m : ℕ} (c : ℕ → ℝ) :
    ∫ w in (-1 : ℝ)..1, ∑ k ∈ Finset.range m, c k * w ^ (2 * k) =
      ∑ k ∈ Finset.range m, c k * (2 / (2 * k + 1 : ℝ)) := by
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl; intro k _
    rw [intervalIntegral.integral_const_mul, integral_even_pow_unit]
  · intro k _; exact (by fun_prop : Continuous fun w : ℝ ↦ c k * w ^ (2 * k)).intervalIntegrable _ _

private lemma integral_sum_even_pow_half {m : ℕ} (c : ℕ → ℝ) :
    ∫ u in (-(1 / 2) : ℝ)..(1 / 2), ∑ k ∈ Finset.range m, c k * u ^ (2 * k) =
      ∑ k ∈ Finset.range m, c k * (1 / ((2 * k + 1 : ℝ) * 4 ^ k)) := by
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl; intro k _
    rw [intervalIntegral.integral_const_mul, integral_even_pow_half]
  · intro k _
    exact (by fun_prop : Continuous fun u : ℝ ↦ c k * u ^ (2 * k)).intervalIntegrable _ _

private lemma integral_alphaPoly :
    ∫ x in (0 : ℝ)..1, (fun x : ℝ => 11 / 10 - 51 / 10 * (x - 1 / 2) ^ 2 + 25 / 10 * (x - 1 / 2) ^ 4) x = 113 / 160 := by
  have h := intervalIntegral.integral_comp_sub_right
    (f := fun u : ℝ ↦ 11 / 10 - 51 / 10 * u ^ 2 + 25 / 10 * u ^ 4) (d := (1 / 2 : ℝ))
    (a := (0 : ℝ)) (b := 1)
  have hsub : (0 : ℝ) - 1 / 2 = -(1 / 2) := by norm_num
  have hsub2 : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
  rw [hsub, hsub2] at h
  change ∫ x in (0 : ℝ)..1, (11 / 10 - 51 / 10 * (x - 1 / 2) ^ 2 + 25 / 10 * (x - 1 / 2) ^ 4) = _
  rw [h]
  have hsum : (fun u : ℝ ↦ 11 / 10 - 51 / 10 * u ^ 2 + 25 / 10 * u ^ 4) =
      fun u ↦ ∑ k ∈ Finset.range 3,
        (match k with | 0 => (11 / 10 : ℝ) | 1 => -(51 / 10) | _ => 25 / 10) * u ^ (2 * k) := by
    funext u; simp [Finset.sum_range_succ]; ring
  rw [hsum, integral_sum_even_pow_half]
  norm_num [Finset.sum_range_succ]

private lemma integral_gammaPoly :
    ∫ z in (0 : ℝ)..2, (fun z : ℝ => -(7 / 10) + 38 / 10 * (z - 1) ^ 2 - 22 / 10 * (z - 1) ^ 4) z = 19 / 75 := by
  have h := intervalIntegral.integral_comp_sub_right
    (f := fun w : ℝ ↦ -(7 / 10) + 38 / 10 * w ^ 2 - 22 / 10 * w ^ 4) (d := (1 : ℝ))
    (a := (0 : ℝ)) (b := 2)
  have hsub : (0 : ℝ) - 1 = -1 := by norm_num
  have hsub2 : (2 : ℝ) - 1 = 1 := by norm_num
  rw [hsub, hsub2] at h
  change ∫ z in (0 : ℝ)..2, (-(7 / 10) + 38 / 10 * (z - 1) ^ 2 - 22 / 10 * (z - 1) ^ 4) = _
  rw [h]
  have hsum : (fun w : ℝ ↦ -(7 / 10) + 38 / 10 * w ^ 2 - 22 / 10 * w ^ 4) =
      fun w ↦ ∑ k ∈ Finset.range 3,
        (match k with | 0 => -(7 / 10 : ℝ) | 1 => 38 / 10 | _ => -(22 / 10)) * w ^ (2 * k) := by
    funext w; simp [Finset.sum_range_succ]; ring
  rw [hsum, integral_sum_even_pow_unit]
  norm_num [Finset.sum_range_succ]


private lemma p8G_eq (w : ℝ) :
    let u := -(17 / 10 : ℝ) + 38 / 10 * w ^ 2 - 22 / 10 * w ^ 4
    (1 : ℝ) + u + u ^ 2 / 2 + u ^ 3 / 6 + u ^ 4 / 24 + u ^ 5 / 120 +
      u ^ 6 / 720 + u ^ 7 / 5040 + u ^ 8 / 40320 =
    ∑ k ∈ Finset.range 17, (fun k : ℕ => (match k with | 0 => 105386271143 / 576000000000 | 1 => 173547933383 / 252000000000 | 2 => 20339931683 / 21000000000 | 3 => -2841664567 / 18000000000 | 4 => 4377443801 / 12000000000 | 5 => -13711707599 / 3000000000 | 6 => 6780417089 / 750000000 | 7 => -71524356029 / 4500000000 | 8 => 341540326899 / 14000000000 | 9 => -449581173019 / 15750000000 | 10 => 4911536531 / 187500000 | 11 => -7193380183 / 375000000 | 12 => 2691996747 / 250000000 | 13 => -2444915231 / 562500000 | 14 => 54918391 / 46875000 | 15 => -370256249 / 1968750000 | 16 => 214358881 / 15750000000 | _ => 0 : ℝ)) k * w ^ (2 * k) := by
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
  ring

private lemma integral_exp_gammaPoly_le :
    ∫ z in (0 : ℝ)..2, Real.exp ((fun z : ℝ => -(7 / 10) + 38 / 10 * (z - 1) ^ 2 - 22 / 10 * (z - 1) ^ 4) z - 1) ≤
      9674781409637358885367 / 9771668992800000000000 := by
  have h := intervalIntegral.integral_comp_sub_right
    (f := fun w : ℝ ↦ Real.exp (-(17 / 10 : ℝ) + 38 / 10 * w ^ 2 - 22 / 10 * w ^ 4))
    (d := (1 : ℝ)) (a := (0 : ℝ)) (b := 2)
  have h1 : (fun z : ℝ ↦ Real.exp ((fun z : ℝ => -(7 / 10) + 38 / 10 * (z - 1) ^ 2 - 22 / 10 * (z - 1) ^ 4) z - 1)) =
      fun z ↦ Real.exp (-(17 / 10 : ℝ) + 38 / 10 * (z - 1) ^ 2 - 22 / 10 * (z - 1) ^ 4) := by
    funext z; dsimp only []; congr 1; ring
  rw [h1, h]
  have hsub : (0 : ℝ) - 1 = -1 := by norm_num
  have hsub2 : (2 : ℝ) - 1 = 1 := by norm_num
  rw [hsub, hsub2]
  have hmono :
      ∫ w in (-1 : ℝ)..1, Real.exp (-(17 / 10 : ℝ) + 38 / 10 * w ^ 2 - 22 / 10 * w ^ 4) ≤
      ∫ w in (-1 : ℝ)..1, ∑ k ∈ Finset.range 17, (fun k : ℕ => (match k with | 0 => 105386271143 / 576000000000 | 1 => 173547933383 / 252000000000 | 2 => 20339931683 / 21000000000 | 3 => -2841664567 / 18000000000 | 4 => 4377443801 / 12000000000 | 5 => -13711707599 / 3000000000 | 6 => 6780417089 / 750000000 | 7 => -71524356029 / 4500000000 | 8 => 341540326899 / 14000000000 | 9 => -449581173019 / 15750000000 | 10 => 4911536531 / 187500000 | 11 => -7193380183 / 375000000 | 12 => 2691996747 / 250000000 | 13 => -2444915231 / 562500000 | 14 => 54918391 / 46875000 | 15 => -370256249 / 1968750000 | 16 => 214358881 / 15750000000 | _ => 0 : ℝ)) k * w ^ (2 * k) := by
    apply intervalIntegral.integral_mono_on (by norm_num : (-1 : ℝ) ≤ 1)
    · exact (by fun_prop : Continuous fun w : ℝ ↦
        Real.exp (-(17 / 10 : ℝ) + 38 / 10 * w ^ 2 - 22 / 10 * w ^ 4)).intervalIntegrable _ _
    · exact (by fun_prop : Continuous fun w : ℝ ↦
        ∑ k ∈ Finset.range 17, (fun k : ℕ => (match k with | 0 => 105386271143 / 576000000000 | 1 => 173547933383 / 252000000000 | 2 => 20339931683 / 21000000000 | 3 => -2841664567 / 18000000000 | 4 => 4377443801 / 12000000000 | 5 => -13711707599 / 3000000000 | 6 => 6780417089 / 750000000 | 7 => -71524356029 / 4500000000 | 8 => 341540326899 / 14000000000 | 9 => -449581173019 / 15750000000 | 10 => 4911536531 / 187500000 | 11 => -7193380183 / 375000000 | 12 => 2691996747 / 250000000 | 13 => -2444915231 / 562500000 | 14 => 54918391 / 46875000 | 15 => -370256249 / 1968750000 | 16 => 214358881 / 15750000000 | _ => 0 : ℝ)) k * w ^ (2 * k)).intervalIntegrable _ _
    · intro w _
      rw [← p8G_eq w]
      apply exp_le_poly8_of_nonpos
      nlinarith [sq_nonneg (w ^ 2 - 19 / 22)]
  rw [integral_sum_even_pow_unit] at hmono
  calc _ ≤ ∑ k ∈ Finset.range 17, (fun k : ℕ => (match k with | 0 => 105386271143 / 576000000000 | 1 => 173547933383 / 252000000000 | 2 => 20339931683 / 21000000000 | 3 => -2841664567 / 18000000000 | 4 => 4377443801 / 12000000000 | 5 => -13711707599 / 3000000000 | 6 => 6780417089 / 750000000 | 7 => -71524356029 / 4500000000 | 8 => 341540326899 / 14000000000 | 9 => -449581173019 / 15750000000 | 10 => 4911536531 / 187500000 | 11 => -7193380183 / 375000000 | 12 => 2691996747 / 250000000 | 13 => -2444915231 / 562500000 | 14 => 54918391 / 46875000 | 15 => -370256249 / 1968750000 | 16 => 214358881 / 15750000000 | _ => 0 : ℝ)) k * (2 / (2 * k + 1 : ℝ)) := hmono
    _ = 9674781409637358885367 / 9771668992800000000000 := by
      norm_num [Finset.sum_range_succ]



private lemma hPoly_expand (u v : ℝ) :
    let h := -(1 / 5 : ℝ) + 5 / 2 * (u ^ 2 + v ^ 2) - 19 / 10 * (u ^ 4 + v ^ 4) -
      132 / 5 * u ^ 2 * v ^ 2
    (1 : ℝ) + h + h ^ 2 / 2 + h ^ 3 / 6 + 5 / 96 * h ^ 4 =
      ∑ j ∈ Finset.range 9, (fun (j : ℕ) (s : ℝ) => (match j with | 0 => 131 / 160 + 491 / 240 * s + 24559 / 24000 * s ^ 2 - 629 / 320 * s ^ 3 - 178463 / 192000 * s ^ 4 - 5377 / 1920 * s ^ 5 + 198189 / 32000 * s ^ 6 - 6859 / 1920 * s ^ 7 + 130321 / 192000 * s ^ 8 | 1 => 491 / 240 - 65791 / 4000 * s - 16803 / 320 * s ^ 2 - 1020539 / 48000 * s ^ 3 - 4517 / 640 * s ^ 4 + 2788801 / 16000 * s ^ 5 - 292771 / 1920 * s ^ 6 + 75449 / 2000 * s ^ 7 | 2 => 24559 / 24000 - 16803 / 320 * s + 5440801 / 32000 * s ^ 2 + 1415 / 3 * s ^ 3 + 40803879 / 32000 * s ^ 4 - 1426387 / 640 * s ^ 5 + 7574141 / 9600 * s ^ 6 | 3 => -(629 / 320) - 1020539 / 48000 * s + 1415 / 3 * s ^ 2 + 6169057 / 8000 * s ^ 3 - 7654939 / 640 * s ^ 4 + 14792811 / 2000 * s ^ 5 | 4 => -(178463 / 192000) - 4517 / 640 * s + 40803879 / 32000 * s ^ 2 - 7654939 / 640 * s ^ 3 + 860039569 / 32000 * s ^ 4 | 5 => -(5377 / 1920) + 2788801 / 16000 * s - 1426387 / 640 * s ^ 2 + 14792811 / 2000 * s ^ 3 | 6 => 198189 / 32000 - 292771 / 1920 * s + 7574141 / 9600 * s ^ 2 | 7 => -(6859 / 1920) + 75449 / 2000 * s | 8 => 130321 / 192000 | _ => 0 : ℝ)) j (u ^ 2) * v ^ (2 * j) := by
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
  ring

private lemma qPoly_sum_eq (s : ℝ) :
    ∑ j ∈ Finset.range 9, (fun (j : ℕ) (s : ℝ) => (match j with | 0 => 131 / 160 + 491 / 240 * s + 24559 / 24000 * s ^ 2 - 629 / 320 * s ^ 3 - 178463 / 192000 * s ^ 4 - 5377 / 1920 * s ^ 5 + 198189 / 32000 * s ^ 6 - 6859 / 1920 * s ^ 7 + 130321 / 192000 * s ^ 8 | 1 => 491 / 240 - 65791 / 4000 * s - 16803 / 320 * s ^ 2 - 1020539 / 48000 * s ^ 3 - 4517 / 640 * s ^ 4 + 2788801 / 16000 * s ^ 5 - 292771 / 1920 * s ^ 6 + 75449 / 2000 * s ^ 7 | 2 => 24559 / 24000 - 16803 / 320 * s + 5440801 / 32000 * s ^ 2 + 1415 / 3 * s ^ 3 + 40803879 / 32000 * s ^ 4 - 1426387 / 640 * s ^ 5 + 7574141 / 9600 * s ^ 6 | 3 => -(629 / 320) - 1020539 / 48000 * s + 1415 / 3 * s ^ 2 + 6169057 / 8000 * s ^ 3 - 7654939 / 640 * s ^ 4 + 14792811 / 2000 * s ^ 5 | 4 => -(178463 / 192000) - 4517 / 640 * s + 40803879 / 32000 * s ^ 2 - 7654939 / 640 * s ^ 3 + 860039569 / 32000 * s ^ 4 | 5 => -(5377 / 1920) + 2788801 / 16000 * s - 1426387 / 640 * s ^ 2 + 14792811 / 2000 * s ^ 3 | 6 => 198189 / 32000 - 292771 / 1920 * s + 7574141 / 9600 * s ^ 2 | 7 => -(6859 / 1920) + 75449 / 2000 * s | 8 => 130321 / 192000 | _ => 0 : ℝ)) j s * (1 / ((2 * j + 1 : ℝ) * 4 ^ j)) =
      ∑ i ∈ Finset.range 9, (fun k : ℕ => (match k with | 0 => 9607514477984021 / 9635553607680000 | 1 => -55903820111 / 2952069120000 | 2 => 192910427869 / 984023040000 | 3 => -56338789 / 86016000 | 4 => -1579010773 / 2580480000 | 5 => 672353 / 1792000 | 6 => 7714931 / 2304000 | 7 => -6859 / 16000 | 8 => 130321 / 192000 | _ => 0 : ℝ)) i * s ^ i := by
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
  ring

private lemma hPoly_abs_le_one {u v : ℝ} (hu : u ∈ Set.Icc (-(1 / 2) : ℝ) (1 / 2))
    (hv : v ∈ Set.Icc (-(1 / 2) : ℝ) (1 / 2)) :
    |-(1 / 5 : ℝ) + 5 / 2 * (u ^ 2 + v ^ 2) - 19 / 10 * (u ^ 4 + v ^ 4) -
      132 / 5 * u ^ 2 * v ^ 2| ≤ 1 := by
  have hp0 : 0 ≤ u ^ 2 := sq_nonneg u
  have hq0 : 0 ≤ v ^ 2 := sq_nonneg v
  have hp1 : u ^ 2 ≤ 1 / 4 := by nlinarith [hu.1, hu.2]
  have hq1 : v ^ 2 ≤ 1 / 4 := by nlinarith [hv.1, hv.2]
  rw [abs_le]
  constructor
  · nlinarith [sq_nonneg (u ^ 2 - v ^ 2), mul_nonneg (sub_nonneg.mpr hp1) hp0,
      mul_nonneg (sub_nonneg.mpr hq1) hq0]
  · nlinarith [sq_nonneg (u ^ 2 - v ^ 2), mul_nonneg hp0 hq0]

private lemma integral_exp_H_le :
    ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1,
      Real.exp ((fun x : ℝ => 11 / 10 - 51 / 10 * (x - 1 / 2) ^ 2 + 25 / 10 * (x - 1 / 2) ^ 4) x + (fun x : ℝ => 11 / 10 - 51 / 10 * (x - 1 / 2) ^ 2 + 25 / 10 * (x - 1 / 2) ^ 4) y + (fun z : ℝ => -(7 / 10) + 38 / 10 * (z - 1) ^ 2 - 22 / 10 * (z - 1) ^ 4) (x + y) + (fun z : ℝ => -(7 / 10) + 38 / 10 * (z - 1) ^ 2 - 22 / 10 * (z - 1) ^ 4) (x + 1 - y) - 1) ≤
    5727386377970263 / 5748483686400000 := by
  let Huv : ℝ → ℝ → ℝ := fun u v ↦
    -(1 / 5 : ℝ) + 5 / 2 * (u ^ 2 + v ^ 2) - 19 / 10 * (u ^ 4 + v ^ 4) - 132 / 5 * u ^ 2 * v ^ 2
  have hH_eq : ∀ x y : ℝ,
      (fun x : ℝ => 11 / 10 - 51 / 10 * (x - 1 / 2) ^ 2 + 25 / 10 * (x - 1 / 2) ^ 4) x + (fun x : ℝ => 11 / 10 - 51 / 10 * (x - 1 / 2) ^ 2 + 25 / 10 * (x - 1 / 2) ^ 4) y + (fun z : ℝ => -(7 / 10) + 38 / 10 * (z - 1) ^ 2 - 22 / 10 * (z - 1) ^ 4) (x + y) + (fun z : ℝ => -(7 / 10) + 38 / 10 * (z - 1) ^ 2 - 22 / 10 * (z - 1) ^ 4) (x + 1 - y) - 1 =
        Huv (x - 1 / 2) (y - 1 / 2) := by
    intro x y; dsimp only [Huv]; ring
  simp_rw [hH_eq]
  have hshift_y : ∀ u : ℝ,
      ∫ y in (0 : ℝ)..1, Real.exp (Huv u (y - 1 / 2)) =
        ∫ v in (-(1 / 2) : ℝ)..(1 / 2), Real.exp (Huv u v) := by
    intro u
    have h := intervalIntegral.integral_comp_sub_right
      (f := fun v : ℝ ↦ Real.exp (Huv u v)) (d := (1 / 2 : ℝ)) (a := (0 : ℝ)) (b := 1)
    norm_num at h
    exact h
  simp_rw [hshift_y]
  have hshift_x := intervalIntegral.integral_comp_sub_right
    (f := fun u : ℝ ↦ ∫ v in (-(1 / 2) : ℝ)..(1 / 2), Real.exp (Huv u v))
    (d := (1 / 2 : ℝ)) (a := (0 : ℝ)) (b := 1)
  norm_num at hshift_x
  rw [hshift_x]
  have hinner : ∀ u ∈ Set.Icc (-(1 / 2) : ℝ) (1 / 2),
      ∫ v in (-(1 / 2) : ℝ)..(1 / 2), Real.exp (Huv u v) ≤
        ∑ i ∈ Finset.range 9, (fun k : ℕ => (match k with | 0 => 9607514477984021 / 9635553607680000 | 1 => -55903820111 / 2952069120000 | 2 => 192910427869 / 984023040000 | 3 => -56338789 / 86016000 | 4 => -1579010773 / 2580480000 | 5 => 672353 / 1792000 | 6 => 7714931 / 2304000 | 7 => -6859 / 16000 | 8 => 130321 / 192000 | _ => 0 : ℝ)) i * u ^ (2 * i) := by
    intro u hu
    have h1 : ∫ v in (-(1 / 2) : ℝ)..(1 / 2), Real.exp (Huv u v) ≤
        ∫ v in (-(1 / 2) : ℝ)..(1 / 2),
          ∑ j ∈ Finset.range 9, (fun (j : ℕ) (s : ℝ) => (match j with | 0 => 131 / 160 + 491 / 240 * s + 24559 / 24000 * s ^ 2 - 629 / 320 * s ^ 3 - 178463 / 192000 * s ^ 4 - 5377 / 1920 * s ^ 5 + 198189 / 32000 * s ^ 6 - 6859 / 1920 * s ^ 7 + 130321 / 192000 * s ^ 8 | 1 => 491 / 240 - 65791 / 4000 * s - 16803 / 320 * s ^ 2 - 1020539 / 48000 * s ^ 3 - 4517 / 640 * s ^ 4 + 2788801 / 16000 * s ^ 5 - 292771 / 1920 * s ^ 6 + 75449 / 2000 * s ^ 7 | 2 => 24559 / 24000 - 16803 / 320 * s + 5440801 / 32000 * s ^ 2 + 1415 / 3 * s ^ 3 + 40803879 / 32000 * s ^ 4 - 1426387 / 640 * s ^ 5 + 7574141 / 9600 * s ^ 6 | 3 => -(629 / 320) - 1020539 / 48000 * s + 1415 / 3 * s ^ 2 + 6169057 / 8000 * s ^ 3 - 7654939 / 640 * s ^ 4 + 14792811 / 2000 * s ^ 5 | 4 => -(178463 / 192000) - 4517 / 640 * s + 40803879 / 32000 * s ^ 2 - 7654939 / 640 * s ^ 3 + 860039569 / 32000 * s ^ 4 | 5 => -(5377 / 1920) + 2788801 / 16000 * s - 1426387 / 640 * s ^ 2 + 14792811 / 2000 * s ^ 3 | 6 => 198189 / 32000 - 292771 / 1920 * s + 7574141 / 9600 * s ^ 2 | 7 => -(6859 / 1920) + 75449 / 2000 * s | 8 => 130321 / 192000 | _ => 0 : ℝ)) j (u ^ 2) * v ^ (2 * j) := by
      apply intervalIntegral.integral_mono_on (by norm_num : (-(1 / 2) : ℝ) ≤ 1 / 2)
      · exact (by fun_prop : Continuous fun v : ℝ ↦ Real.exp (Huv u v)).intervalIntegrable _ _
      · exact (by fun_prop : Continuous fun v : ℝ ↦
          ∑ j ∈ Finset.range 9, (fun (j : ℕ) (s : ℝ) => (match j with | 0 => 131 / 160 + 491 / 240 * s + 24559 / 24000 * s ^ 2 - 629 / 320 * s ^ 3 - 178463 / 192000 * s ^ 4 - 5377 / 1920 * s ^ 5 + 198189 / 32000 * s ^ 6 - 6859 / 1920 * s ^ 7 + 130321 / 192000 * s ^ 8 | 1 => 491 / 240 - 65791 / 4000 * s - 16803 / 320 * s ^ 2 - 1020539 / 48000 * s ^ 3 - 4517 / 640 * s ^ 4 + 2788801 / 16000 * s ^ 5 - 292771 / 1920 * s ^ 6 + 75449 / 2000 * s ^ 7 | 2 => 24559 / 24000 - 16803 / 320 * s + 5440801 / 32000 * s ^ 2 + 1415 / 3 * s ^ 3 + 40803879 / 32000 * s ^ 4 - 1426387 / 640 * s ^ 5 + 7574141 / 9600 * s ^ 6 | 3 => -(629 / 320) - 1020539 / 48000 * s + 1415 / 3 * s ^ 2 + 6169057 / 8000 * s ^ 3 - 7654939 / 640 * s ^ 4 + 14792811 / 2000 * s ^ 5 | 4 => -(178463 / 192000) - 4517 / 640 * s + 40803879 / 32000 * s ^ 2 - 7654939 / 640 * s ^ 3 + 860039569 / 32000 * s ^ 4 | 5 => -(5377 / 1920) + 2788801 / 16000 * s - 1426387 / 640 * s ^ 2 + 14792811 / 2000 * s ^ 3 | 6 => 198189 / 32000 - 292771 / 1920 * s + 7574141 / 9600 * s ^ 2 | 7 => -(6859 / 1920) + 75449 / 2000 * s | 8 => 130321 / 192000 | _ => 0 : ℝ)) j (u ^ 2) * v ^ (2 * j)).intervalIntegrable _ _
      · intro v hv
        rw [← hPoly_expand u v]
        exact exp_le_poly4_of_abs_le_one (hPoly_abs_le_one hu hv)
    rw [integral_sum_even_pow_half] at h1
    have h2 := qPoly_sum_eq (u ^ 2)
    have hpow : ∀ i : ℕ, (u ^ 2) ^ i = u ^ (2 * i) := fun i ↦ by rw [← pow_mul]
    have h3 : (∑ i ∈ Finset.range 9, (fun k : ℕ => (match k with | 0 => 9607514477984021 / 9635553607680000 | 1 => -55903820111 / 2952069120000 | 2 => 192910427869 / 984023040000 | 3 => -56338789 / 86016000 | 4 => -1579010773 / 2580480000 | 5 => 672353 / 1792000 | 6 => 7714931 / 2304000 | 7 => -6859 / 16000 | 8 => 130321 / 192000 | _ => 0 : ℝ)) i * (u ^ 2) ^ i) =
        ∑ i ∈ Finset.range 9, (fun k : ℕ => (match k with | 0 => 9607514477984021 / 9635553607680000 | 1 => -55903820111 / 2952069120000 | 2 => 192910427869 / 984023040000 | 3 => -56338789 / 86016000 | 4 => -1579010773 / 2580480000 | 5 => 672353 / 1792000 | 6 => 7714931 / 2304000 | 7 => -6859 / 16000 | 8 => 130321 / 192000 | _ => 0 : ℝ)) i * u ^ (2 * i) :=
      Finset.sum_congr rfl (fun i _ => by rw [hpow])
    linarith
  have houter :
      ∫ u in (-(1 / 2) : ℝ)..(1 / 2), ∫ v in (-(1 / 2) : ℝ)..(1 / 2), Real.exp (Huv u v) ≤
      ∫ u in (-(1 / 2) : ℝ)..(1 / 2), ∑ i ∈ Finset.range 9, (fun k : ℕ => (match k with | 0 => 9607514477984021 / 9635553607680000 | 1 => -55903820111 / 2952069120000 | 2 => 192910427869 / 984023040000 | 3 => -56338789 / 86016000 | 4 => -1579010773 / 2580480000 | 5 => 672353 / 1792000 | 6 => 7714931 / 2304000 | 7 => -6859 / 16000 | 8 => 130321 / 192000 | _ => 0 : ℝ)) i * u ^ (2 * i) := by
    apply intervalIntegral.integral_mono_on (by norm_num : (-(1 / 2) : ℝ) ≤ 1 / 2)
    · exact (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        (by fun_prop) _ _).intervalIntegrable _ _
    · exact (by fun_prop : Continuous fun u : ℝ ↦
        ∑ i ∈ Finset.range 9, (fun k : ℕ => (match k with | 0 => 9607514477984021 / 9635553607680000 | 1 => -55903820111 / 2952069120000 | 2 => 192910427869 / 984023040000 | 3 => -56338789 / 86016000 | 4 => -1579010773 / 2580480000 | 5 => 672353 / 1792000 | 6 => 7714931 / 2304000 | 7 => -6859 / 16000 | 8 => 130321 / 192000 | _ => 0 : ℝ)) i * u ^ (2 * i)).intervalIntegrable _ _
    · exact hinner
  rw [integral_sum_even_pow_half] at houter
  calc _ ≤ ∑ i ∈ Finset.range 9, (fun k : ℕ => (match k with | 0 => 9607514477984021 / 9635553607680000 | 1 => -55903820111 / 2952069120000 | 2 => 192910427869 / 984023040000 | 3 => -56338789 / 86016000 | 4 => -1579010773 / 2580480000 | 5 => 672353 / 1792000 | 6 => 7714931 / 2304000 | 7 => -6859 / 16000 | 8 => 130321 / 192000 | _ => 0 : ℝ)) i * (1 / ((2 * i + 1 : ℝ) * 4 ^ i)) := houter
    _ = 5727386377970263 / 5748483686400000 := by
      norm_num [Finset.sum_range_succ]

/-- Uniform upper certificate (Simkin R2.H2): every step queenon score is at most `-1.9426 < -1.94`. -/
theorem upper_certificate :
    ∃ u : ℝ, u < -1.94 ∧ ∀ r ∈ ({r | ∃ N : ℕ, 0 < N ∧ ∃ A : Fin N → Fin N → ℝ, let f := fun x : ℝ ↦ x * Real.log x; let d := fun (b : Bool) (k : ℕ) ↦ 1 - (∑ i : Fin N, ∑ j : Fin N, if i.val + j.val + 1 = k then A i (if b then j.rev else j) else 0) / N; (∀ i j, 0 ≤ A i j) ∧ (∀ i, ∑ j, A i j = N) ∧ (∀ j, ∑ i, A i j = N) ∧ (∀ b (k : Fin (2 * N + 1)), 0 ≤ d b k.val) ∧ r = -3 - (∑ i, ∑ j, f (A i j)) / (N : ℝ) ^ 2 - (∑ b : Bool, ∑ k : Fin (2 * N), ∫ t in (0 : ℝ)..1, f ((1 - t) * d b k.val + t * d b (k.val + 1))) / N} : Set ℝ), r ≤ u := by
  refine ⟨-(119061998400496536240659477 / 61287907922841600000000000 : ℝ), by norm_num, ?_⟩
  intro r hr
  have hα : Continuous (fun x : ℝ => 11 / 10 - 51 / 10 * (x - 1 / 2) ^ 2 + 25 / 10 * (x - 1 / 2) ^ 4) := by beta_reduce; fun_prop
  have hγ : Continuous (fun z : ℝ => -(7 / 10) + 38 / 10 * (z - 1) ^ 2 - 22 / 10 * (z - 1) ^ 4) := by beta_reduce; fun_prop
  have hdual := duality_upper_bound hα hγ hr
  have h1 := integral_alphaPoly
  have h2 := integral_gammaPoly
  have h3 := integral_exp_gammaPoly_le
  have h4 := integral_exp_H_le
  linarith

/- Part 3: Explicit 12 x 12 Lower Witness (`∃ r ∈ ({r | ∃ N : ℕ, 0 < N ∧ ∃ A : Fin N → Fin N → ℝ, let f := fun x : ℝ ↦ x * Real.log x; let d := fun (b : Bool) (k : ℕ) ↦ 1 - (∑ i : Fin N, ∑ j : Fin N, if i.val + j.val + 1 = k then A i (if b then j.rev else j) else 0) / N; (∀ i j, 0 ≤ A i j) ∧ (∀ i, ∑ j, A i j = N) ∧ (∀ j, ∑ i, A i j = N) ∧ (∀ b (k : Fin (2 * N + 1)), 0 ≤ d b k.val) ∧ r = -3 - (∑ i, ∑ j, f (A i j)) / (N : ℝ) ^ 2 - (∑ b : Bool, ∑ k : Fin (2 * N), ∫ t in (0 : ℝ)..1, f ((1 - t) * d b k.val + t * d b (k.val + 1))) / N} : Set ℝ), -1.9449 < r`) -/

section LowerWitness
-- Adapted from @minimumnz PR #12951 (proofs/Green97.green_97.variants.simkin.R2.H3.lean)
-- https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/12951

open Finset Real


private lemma poly8_le_exp {q : ℝ} (hq : 0 ≤ q) : (fun q : ℝ => 1 + q + q ^ 2 / 2 + q ^ 3 / 6 + q ^ 4 / 24 + q ^ 5 / 120 + q ^ 6 / 720 + q ^ 7 / 5040 + q ^ 8 / 40320) q ≤ Real.exp q := by
  have h := Real.sum_le_exp_of_nonneg hq 9
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_one, Nat.cast_mul, pow_zero, pow_one, div_one, zero_add] at h
  beta_reduce
  linarith

private lemma exp_le_poly8_add {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    Real.exp q ≤ (fun q : ℝ => 1 + q + q ^ 2 / 2 + q ^ 3 / 6 + q ^ 4 / 24 + q ^ 5 / 120 + q ^ 6 / 720 + q ^ 7 / 5040 + q ^ 8 / 40320) q + q ^ 9 / 300000 := by
  have habs : |q| ≤ 1 := by rw [abs_of_nonneg hq0]; exact hq1
  have h := Real.exp_bound habs (show 0 < 9 by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat, pow_zero, pow_one, div_one, zero_add, abs_of_nonneg hq0] at h
  have hle := (abs_le.mp h).2
  have hcoef : q ^ 9 * (((9 : ℝ) + 1) / ((362880 : ℝ) * 9)) ≤ q ^ 9 / 300000 := by
    have hq9 : 0 ≤ q ^ 9 := pow_nonneg hq0 9
    have hc : ((9 : ℝ) + 1) / ((362880 : ℝ) * 9) ≤ 1 / 300000 := by norm_num
    calc q ^ 9 * (((9 : ℝ) + 1) / ((362880 : ℝ) * 9))
        ≤ q ^ 9 * (1 / 300000) := mul_le_mul_of_nonneg_left hc hq9
      _ = q ^ 9 / 300000 := by ring
  beta_reduce
  linarith

private lemma log_le_of_scale {x y q : ℝ} {s : ℕ} (hx : 0 < x) (hq : 0 ≤ q)
    (hmul : x * (2 : ℝ) ^ s = y) (hpoly : y ≤ (fun q : ℝ => 1 + q + q ^ 2 / 2 + q ^ 3 / 6 + q ^ 4 / 24 + q ^ 5 / 120 + q ^ 6 / 720 + q ^ 7 / 5040 + q ^ 8 / 40320) q) :
    Real.log x ≤ q - (s : ℝ) * (6931471803 / 10000000000 : ℝ) := by
  have hy_pos : 0 < y := by rw [← hmul]; positivity
  have hly : Real.log y ≤ q := by
    have := Real.log_le_log hy_pos (hpoly.trans (poly8_le_exp hq))
    rwa [Real.log_exp] at this
  have hlog := congrArg Real.log hmul
  rw [Real.log_mul hx.ne' (by positivity), Real.log_pow] at hlog
  have hl2 : (6931471803 / 10000000000 : ℝ) ≤ Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  have hs_mul : (s : ℝ) * (6931471803 / 10000000000 : ℝ) ≤ (s : ℝ) * Real.log 2 :=
    mul_le_mul_of_nonneg_left hl2 (Nat.cast_nonneg s)
  linarith

private lemma le_log_of_scale {x y q : ℝ} {s : ℕ} (hx : 0 < x) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hmul : x * (2 : ℝ) ^ s = y) (hpoly : (fun q : ℝ => 1 + q + q ^ 2 / 2 + q ^ 3 / 6 + q ^ 4 / 24 + q ^ 5 / 120 + q ^ 6 / 720 + q ^ 7 / 5040 + q ^ 8 / 40320) q + q ^ 9 / 300000 ≤ y) :
    q - (s : ℝ) * (6931471808 / 10000000000 : ℝ) ≤ Real.log x := by
  have hly : q ≤ Real.log y := by
    have := Real.log_le_log (Real.exp_pos q) ((exp_le_poly8_add hq0 hq1).trans hpoly)
    rwa [Real.log_exp] at this
  have hlog := congrArg Real.log hmul
  rw [Real.log_mul hx.ne' (by positivity), Real.log_pow] at hlog
  have hl2 : Real.log 2 ≤ (6931471808 / 10000000000 : ℝ) := by
    have := Real.log_two_lt_d9; linarith
  have hs_mul : (s : ℝ) * Real.log 2 ≤ (s : ℝ) * (6931471808 / 10000000000 : ℝ) :=
    mul_le_mul_of_nonneg_left hl2 (Nat.cast_nonneg s)
  linarith

private lemma integral_mul_log_linear {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) :
    ∫ t in (0 : ℝ)..1, ((1 - t) * a + t * b) * Real.log ((1 - t) * a + t * b) =
      ((b ^ 2 * Real.log b - a ^ 2 * Real.log a) / 2 - (b ^ 2 - a ^ 2) / 4) / (b - a) := by
  let L : ℝ → ℝ := fun t => (1 - t) * a + t * b
  let F : ℝ → ℝ := fun t => ((L t) ^ 2 * Real.log (L t) / 2 - (L t) ^ 2 / 4) / (b - a)
  have hba : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
  have hL_pos : ∀ t ∈ Set.uIcc (0 : ℝ) 1, 0 < L t := by
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    dsimp only [L]
    by_cases h0 : t = 0
    · subst h0; linarith
    · have ht0 : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm h0)
      have h1 : 0 ≤ (1 - t) * a := mul_nonneg (sub_nonneg.mpr ht.2) ha.le
      have h2 : 0 < t * b := mul_pos ht0 hb
      linarith
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt F (L t * Real.log (L t)) t := by
    intro t ht
    have hLp : 0 < L t := hL_pos t ht
    have hL' : HasDerivAt L (b - a) t := by
      have : L = fun s => a + (b - a) * s := by funext s; dsimp only [L]; ring
      rw [this]
      simpa using ((hasDerivAt_id t).const_mul (b - a)).const_add a
    have hsq : HasDerivAt (fun s => (L s) ^ 2) (2 * L t * (b - a)) t := by
      have h1 : HasDerivAt (fun s => L s * L s) ((b - a) * L t + L t * (b - a)) t := hL'.mul hL'
      have h2 : (fun s => (L s) ^ 2) = (fun s => L s * L s) := by funext s; ring
      have h3 : 2 * L t * (b - a) = (b - a) * L t + L t * (b - a) := by ring
      rw [h2, h3]
      exact h1
    have hlog : HasDerivAt (fun s => Real.log (L s)) ((b - a) / L t) t := by
      simpa [div_eq_mul_inv, mul_comm] using hL'.log hLp.ne'
    have hprod : HasDerivAt (fun s => (L s) ^ 2 * Real.log (L s))
        ((2 * L t * (b - a)) * Real.log (L t) + (L t) ^ 2 * ((b - a) / L t)) t :=
      hsq.mul hlog
    have hF : HasDerivAt F
        ((((2 * L t * (b - a)) * Real.log (L t) + (L t) ^ 2 * ((b - a) / L t)) / 2 -
          (2 * L t * (b - a)) / 4) / (b - a)) t :=
      ((hprod.div_const 2).sub (hsq.div_const 4)).div_const (b - a)
    convert hF using 1
    field_simp [hba, hLp.ne']
    ring
  have hcont : ContinuousOn (fun t => L t * Real.log (L t)) (Set.uIcc 0 1) := by
    have hLc : Continuous L := by fun_prop
    refine hLc.continuousOn.mul ?_
    intro t ht
    exact (Real.continuousAt_log (hL_pos t ht).ne').comp hLc.continuousAt |>.continuousWithinAt
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
  rw [hint]
  dsimp only [F, L]
  simp only [sub_zero, one_mul, zero_mul, add_zero, sub_self, zero_add]
  ring





private lemma row_sum_nat : ∀ i : Fin 12, ∑ j : Fin 12, (fun i j : Fin 12 => (![![582, 765, 955, 1127, 1252, 1319], ![765, 861, 993, 1083, 1137, 1161], ![955, 993, 987, 1018, 1024, 1023], ![1127, 1083, 1018, 939, 922, 911], ![1252, 1137, 1024, 922, 839, 826], ![1319, 1161, 1023, 911, 826, 760]] : Fin 6 → Fin 6 → ℕ) ((fun i : Fin 12 => (if h : i.val < 6 then ⟨i.val, h⟩ else ⟨11 - i.val, by omega⟩ : Fin 6)) i) ((fun i : Fin 12 => (if h : i.val < 6 then ⟨i.val, h⟩ else ⟨11 - i.val, by omega⟩ : Fin 6)) j)) i j = 12000 := by decide
private lemma col_sum_nat : ∀ j : Fin 12, ∑ i : Fin 12, (fun i j : Fin 12 => (![![582, 765, 955, 1127, 1252, 1319], ![765, 861, 993, 1083, 1137, 1161], ![955, 993, 987, 1018, 1024, 1023], ![1127, 1083, 1018, 939, 922, 911], ![1252, 1137, 1024, 922, 839, 826], ![1319, 1161, 1023, 911, 826, 760]] : Fin 6 → Fin 6 → ℕ) ((fun i : Fin 12 => (if h : i.val < 6 then ⟨i.val, h⟩ else ⟨11 - i.val, by omega⟩ : Fin 6)) i) ((fun i : Fin 12 => (if h : i.val < 6 then ⟨i.val, h⟩ else ⟨11 - i.val, by omega⟩ : Fin 6)) j)) i j = 12000 := by decide
private lemma diag_le_nat : ∀ (b : Bool) (k : Fin 25),
    (∑ i : Fin 12, ∑ j : Fin 12,
      if i.val + j.val + 1 = k.val then (fun i j : Fin 12 => (![![582, 765, 955, 1127, 1252, 1319], ![765, 861, 993, 1083, 1137, 1161], ![955, 993, 987, 1018, 1024, 1023], ![1127, 1083, 1018, 939, 922, 911], ![1252, 1137, 1024, 922, 839, 826], ![1319, 1161, 1023, 911, 826, 760]] : Fin 6 → Fin 6 → ℕ) ((fun i : Fin 12 => (if h : i.val < 6 then ⟨i.val, h⟩ else ⟨11 - i.val, by omega⟩ : Fin 6)) i) ((fun i : Fin 12 => (if h : i.val < 6 then ⟨i.val, h⟩ else ⟨11 - i.val, by omega⟩ : Fin 6)) j)) i (if b then j.rev else j) else 0) ≤ 12000 := by decide


private lemma d_nat_eq_table : ∀ (b : Bool) (k : Fin 25), (fun (b : Bool) (k : ℕ) => (12000 - ∑ i : Fin 12, ∑ j : Fin 12, if i.val + j.val + 1 = k then (fun i j : Fin 12 => (![![582, 765, 955, 1127, 1252, 1319], ![765, 861, 993, 1083, 1137, 1161], ![955, 993, 987, 1018, 1024, 1023], ![1127, 1083, 1018, 939, 922, 911], ![1252, 1137, 1024, 922, 839, 826], ![1319, 1161, 1023, 911, 826, 760]] : Fin 6 → Fin 6 → ℕ) ((fun i : Fin 12 => (if h : i.val < 6 then ⟨i.val, h⟩ else ⟨11 - i.val, by omega⟩ : Fin 6)) i) ((fun i : Fin 12 => (if h : i.val < 6 then ⟨i.val, h⟩ else ⟨11 - i.val, by omega⟩ : Fin 6)) j)) i (if b then j.rev else j) else 0 : ℕ)) b k.val = (![12000, 11418, 10470, 9229, 7760, 6343, 5052, 4053, 3284, 2765, 2402, 2192, 2064, 2192, 2402, 2765, 3284, 4053, 5052, 6343, 7760, 9229, 10470, 11418, 12000] : Fin 25 → ℕ) k := by decide

private lemma log_A_582 : Real.log (((291 : ℝ) / 500)) ≤ ((-5412831803 : ℝ) / 10000000000) := by
  have h := log_le_of_scale (x := ((291 : ℝ) / 500)) (y := ((291 : ℝ) / 250)) (q := ((18983 : ℝ) / 125000)) (s := 1) (by norm_num) (by norm_num) (by norm_num) (by beta_reduce; norm_num)
  linarith
private lemma log_A_760 : Real.log (((19 : ℝ) / 25)) ≤ ((-2744351803 : ℝ) / 10000000000) := by
  have h := log_le_of_scale (x := ((19 : ℝ) / 25)) (y := ((38 : ℝ) / 25)) (q := ((52339 : ℝ) / 125000)) (s := 1) (by norm_num) (by norm_num) (by norm_num) (by beta_reduce; norm_num)
  linarith
private lemma log_A_765 : Real.log (((153 : ℝ) / 200)) ≤ ((-2678781803 : ℝ) / 10000000000) := by
  have h := log_le_of_scale (x := ((153 : ℝ) / 200)) (y := ((153 : ℝ) / 100)) (q := ((425269 : ℝ) / 1000000)) (s := 1) (by norm_num) (by norm_num) (by norm_num) (by beta_reduce; norm_num)
  linarith
private lemma log_A_826 : Real.log (((413 : ℝ) / 500)) ≤ ((-1911591803 : ℝ) / 10000000000) := by
  have h := log_le_of_scale (x := ((413 : ℝ) / 500)) (y := ((413 : ℝ) / 250)) (q := ((125497 : ℝ) / 250000)) (s := 1) (by norm_num) (by norm_num) (by norm_num) (by beta_reduce; norm_num)
  linarith
private lemma log_A_839 : Real.log (((839 : ℝ) / 1000)) ≤ ((-1755431803 : ℝ) / 10000000000) := by
  have h := log_le_of_scale (x := ((839 : ℝ) / 1000)) (y := ((839 : ℝ) / 500)) (q := ((129401 : ℝ) / 250000)) (s := 1) (by norm_num) (by norm_num) (by norm_num) (by beta_reduce; norm_num)
  linarith
private lemma log_A_861 : Real.log (((861 : ℝ) / 1000)) ≤ ((-1496591803 : ℝ) / 10000000000) := by
  have h := log_le_of_scale (x := ((861 : ℝ) / 1000)) (y := ((861 : ℝ) / 500)) (q := ((8492 : ℝ) / 15625)) (s := 1) (by norm_num) (by norm_num) (by norm_num) (by beta_reduce; norm_num)
  linarith
private lemma log_A_911 : Real.log (((911 : ℝ) / 1000)) ≤ ((-932111803 : ℝ) / 10000000000) := by
  have h := log_le_of_scale (x := ((911 : ℝ) / 1000)) (y := ((911 : ℝ) / 500)) (q := ((9374 : ℝ) / 15625)) (s := 1) (by norm_num) (by norm_num) (by norm_num) (by beta_reduce; norm_num)
  linarith
private lemma log_A_922 : Real.log (((461 : ℝ) / 500)) ≤ ((-812081803 : ℝ) / 10000000000) := by
  have h := log_le_of_scale (x := ((461 : ℝ) / 500)) (y := ((461 : ℝ) / 250)) (q := ((611939 : ℝ) / 1000000)) (s := 1) (by norm_num) (by norm_num) (by norm_num) (by beta_reduce; norm_num)
  linarith
private lemma log_A_939 : Real.log (((939 : ℝ) / 1000)) ≤ ((-629381803 : ℝ) / 10000000000) := by
  have h := log_le_of_scale (x := ((939 : ℝ) / 1000)) (y := ((939 : ℝ) / 500)) (q := ((630209 : ℝ) / 1000000)) (s := 1) (by norm_num) (by norm_num) (by norm_num) (by beta_reduce; norm_num)
  linarith
private lemma log_A_955 : Real.log (((191 : ℝ) / 200)) ≤ ((-460421803 : ℝ) / 10000000000) := by
  have h := log_le_of_scale (x := ((191 : ℝ) / 200)) (y := ((191 : ℝ) / 100)) (q := ((129421 : ℝ) / 200000)) (s := 1) (by norm_num) (by norm_num) (by norm_num) (by beta_reduce; norm_num)
  linarith
private lemma log_A_987 : Real.log (((987 : ℝ) / 1000)) ≤ ((-130841803 : ℝ) / 10000000000) := by
  have h := log_le_of_scale (x := ((987 : ℝ) / 1000)) (y := ((987 : ℝ) / 500)) (q := ((680063 : ℝ) / 1000000)) (s := 1) (by norm_num) (by norm_num) (by norm_num) (by beta_reduce; norm_num)
  linarith
private lemma log_A_993 : Real.log (((993 : ℝ) / 1000)) ≤ ((-70231803 : ℝ) / 10000000000) := by
  have h := log_le_of_scale (x := ((993 : ℝ) / 1000)) (y := ((993 : ℝ) / 500)) (q := ((171531 : ℝ) / 250000)) (s := 1) (by norm_num) (by norm_num) (by norm_num) (by beta_reduce; norm_num)
  linarith
private lemma log_A_1018 : Real.log (((509 : ℝ) / 500)) ≤ ((17841 : ℝ) / 1000000) := by
  have h := log_le_of_scale (x := ((509 : ℝ) / 500)) (y := ((509 : ℝ) / 500)) (q := ((17841 : ℝ) / 1000000)) (s := 0) (by norm_num) (by norm_num) (by norm_num) (by beta_reduce; norm_num)
  linarith
private lemma log_A_1023 : Real.log (((1023 : ℝ) / 1000)) ≤ ((22741 : ℝ) / 1000000) := by
  have h := log_le_of_scale (x := ((1023 : ℝ) / 1000)) (y := ((1023 : ℝ) / 1000)) (q := ((22741 : ℝ) / 1000000)) (s := 0) (by norm_num) (by norm_num) (by norm_num) (by beta_reduce; norm_num)
  linarith
private lemma log_A_1024 : Real.log (((128 : ℝ) / 125)) ≤ ((11859 : ℝ) / 500000) := by
  have h := log_le_of_scale (x := ((128 : ℝ) / 125)) (y := ((128 : ℝ) / 125)) (q := ((11859 : ℝ) / 500000)) (s := 0) (by norm_num) (by norm_num) (by norm_num) (by beta_reduce; norm_num)
  linarith
private lemma log_A_1083 : Real.log (((1083 : ℝ) / 1000)) ≤ ((9967 : ℝ) / 125000) := by
  have h := log_le_of_scale (x := ((1083 : ℝ) / 1000)) (y := ((1083 : ℝ) / 1000)) (q := ((9967 : ℝ) / 125000)) (s := 0) (by norm_num) (by norm_num) (by norm_num) (by beta_reduce; norm_num)
  linarith
private lemma log_A_1127 : Real.log (((1127 : ℝ) / 1000)) ≤ ((119561 : ℝ) / 1000000) := by
  have h := log_le_of_scale (x := ((1127 : ℝ) / 1000)) (y := ((1127 : ℝ) / 1000)) (q := ((119561 : ℝ) / 1000000)) (s := 0) (by norm_num) (by norm_num) (by norm_num) (by beta_reduce; norm_num)
  linarith
private lemma log_A_1137 : Real.log (((1137 : ℝ) / 1000)) ≤ ((25679 : ℝ) / 200000) := by
  have h := log_le_of_scale (x := ((1137 : ℝ) / 1000)) (y := ((1137 : ℝ) / 1000)) (q := ((25679 : ℝ) / 200000)) (s := 0) (by norm_num) (by norm_num) (by norm_num) (by beta_reduce; norm_num)
  linarith
private lemma log_A_1161 : Real.log (((1161 : ℝ) / 1000)) ≤ ((149283 : ℝ) / 1000000) := by
  have h := log_le_of_scale (x := ((1161 : ℝ) / 1000)) (y := ((1161 : ℝ) / 1000)) (q := ((149283 : ℝ) / 1000000)) (s := 0) (by norm_num) (by norm_num) (by norm_num) (by beta_reduce; norm_num)
  linarith
private lemma log_A_1252 : Real.log (((313 : ℝ) / 250)) ≤ ((28093 : ℝ) / 125000) := by
  have h := log_le_of_scale (x := ((313 : ℝ) / 250)) (y := ((313 : ℝ) / 250)) (q := ((28093 : ℝ) / 125000)) (s := 0) (by norm_num) (by norm_num) (by norm_num) (by beta_reduce; norm_num)
  linarith
private lemma log_A_1319 : Real.log (((1319 : ℝ) / 1000)) ≤ ((443 : ℝ) / 1600) := by
  have h := log_le_of_scale (x := ((1319 : ℝ) / 1000)) (y := ((1319 : ℝ) / 1000)) (q := ((443 : ℝ) / 1600)) (s := 0) (by norm_num) (by norm_num) (by norm_num) (by beta_reduce; norm_num)
  linarith
private lemma log_d_ub_0 : Real.log ((1 : ℝ)) ≤ ((1 : ℝ) / 1000000) := by
  have h := log_le_of_scale (x := (1 : ℝ)) (y := (1 : ℝ)) (q := ((1 : ℝ) / 1000000)) (s := 0) (by norm_num) (by norm_num) (by norm_num) (by beta_reduce; norm_num)
  linarith
private lemma log_d_ub_1 : Real.log (((1903 : ℝ) / 2000)) ≤ ((-497141803 : ℝ) / 10000000000) := by
  have h := log_le_of_scale (x := ((1903 : ℝ) / 2000)) (y := ((1903 : ℝ) / 1000)) (q := ((643433 : ℝ) / 1000000)) (s := 1) (by norm_num) (by norm_num) (by norm_num) (by beta_reduce; norm_num)
  linarith
private lemma log_d_lb_1 : ((-15536619 : ℝ) / 312500000) ≤ Real.log (((1903 : ℝ) / 2000)) := by
  have h := le_log_of_scale (x := ((1903 : ℝ) / 2000)) (y := ((1903 : ℝ) / 1000)) (q := ((64343 : ℝ) / 100000)) (s := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by beta_reduce; norm_num)
  linarith
private lemma log_d_ub_2 : Real.log (((349 : ℝ) / 400)) ≤ ((-1363911803 : ℝ) / 10000000000) := by
  have h := log_le_of_scale (x := ((349 : ℝ) / 400)) (y := ((349 : ℝ) / 200)) (q := ((139189 : ℝ) / 250000)) (s := 1) (by norm_num) (by norm_num) (by norm_num) (by beta_reduce; norm_num)
  linarith
private lemma log_d_lb_2 : ((-85246363 : ℝ) / 625000000) ≤ Real.log (((349 : ℝ) / 400)) := by
  have h := le_log_of_scale (x := ((349 : ℝ) / 400)) (y := ((349 : ℝ) / 200)) (q := ((556753 : ℝ) / 1000000)) (s := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by beta_reduce; norm_num)
  linarith
private lemma log_d_ub_3 : Real.log (((9229 : ℝ) / 12000)) ≤ ((-2625541803 : ℝ) / 10000000000) := by
  have h := log_le_of_scale (x := ((9229 : ℝ) / 12000)) (y := ((9229 : ℝ) / 6000)) (q := ((430593 : ℝ) / 1000000)) (s := 1) (by norm_num) (by norm_num) (by norm_num) (by beta_reduce; norm_num)
  linarith
private lemma log_d_lb_3 : ((-82049119 : ℝ) / 312500000) ≤ Real.log (((9229 : ℝ) / 12000)) := by
  have h := le_log_of_scale (x := ((9229 : ℝ) / 12000)) (y := ((9229 : ℝ) / 6000)) (q := ((43059 : ℝ) / 100000)) (s := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by beta_reduce; norm_num)
  linarith
private lemma log_d_ub_4 : Real.log (((97 : ℝ) / 150)) ≤ ((-4359231803 : ℝ) / 10000000000) := by
  have h := log_le_of_scale (x := ((97 : ℝ) / 150)) (y := ((97 : ℝ) / 75)) (q := ((32153 : ℝ) / 125000)) (s := 1) (by norm_num) (by norm_num) (by norm_num) (by beta_reduce; norm_num)
  linarith
private lemma log_d_lb_4 : ((-272453863 : ℝ) / 625000000) ≤ Real.log (((97 : ℝ) / 150)) := by
  have h := le_log_of_scale (x := ((97 : ℝ) / 150)) (y := ((97 : ℝ) / 75)) (q := ((257221 : ℝ) / 1000000)) (s := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by beta_reduce; norm_num)
  linarith
private lemma log_d_ub_5 : Real.log (((6343 : ℝ) / 12000)) ≤ ((-6375531803 : ℝ) / 10000000000) := by
  have h := log_le_of_scale (x := ((6343 : ℝ) / 12000)) (y := ((6343 : ℝ) / 6000)) (q := ((27797 : ℝ) / 500000)) (s := 1) (by norm_num) (by norm_num) (by norm_num) (by beta_reduce; norm_num)
  linarith
private lemma log_d_lb_5 : ((-398472613 : ℝ) / 625000000) ≤ Real.log (((6343 : ℝ) / 12000)) := by
  have h := le_log_of_scale (x := ((6343 : ℝ) / 12000)) (y := ((6343 : ℝ) / 6000)) (q := ((55591 : ℝ) / 1000000)) (s := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by beta_reduce; norm_num)
  linarith
private lemma log_d_ub_6 : Real.log (((421 : ℝ) / 1000)) ≤ ((-4325606803 : ℝ) / 5000000000) := by
  have h := log_le_of_scale (x := ((421 : ℝ) / 1000)) (y := ((421 : ℝ) / 250)) (q := ((521173 : ℝ) / 1000000)) (s := 2) (by norm_num) (by norm_num) (by norm_num) (by beta_reduce; norm_num)
  linarith
private lemma log_d_lb_6 : ((-270351363 : ℝ) / 312500000) ≤ Real.log (((421 : ℝ) / 1000)) := by
  have h := le_log_of_scale (x := ((421 : ℝ) / 1000)) (y := ((421 : ℝ) / 250)) (q := ((52117 : ℝ) / 100000)) (s := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by beta_reduce; norm_num)
  linarith
private lemma log_d_ub_7 : Real.log (((1351 : ℝ) / 4000)) ≤ ((-5427236803 : ℝ) / 5000000000) := by
  have h := log_le_of_scale (x := ((1351 : ℝ) / 4000)) (y := ((1351 : ℝ) / 1000)) (q := ((300847 : ℝ) / 1000000)) (s := 2) (by norm_num) (by norm_num) (by norm_num) (by beta_reduce; norm_num)
  linarith
private lemma log_d_lb_7 : ((-169601619 : ℝ) / 156250000) ≤ Real.log (((1351 : ℝ) / 4000)) := by
  have h := le_log_of_scale (x := ((1351 : ℝ) / 4000)) (y := ((1351 : ℝ) / 1000)) (q := ((75211 : ℝ) / 250000)) (s := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by beta_reduce; norm_num)
  linarith
private lemma log_d_ub_8 : Real.log (((821 : ℝ) / 3000)) ≤ ((-6479216803 : ℝ) / 5000000000) := by
  have h := log_le_of_scale (x := ((821 : ℝ) / 3000)) (y := ((821 : ℝ) / 750)) (q := ((90451 : ℝ) / 1000000)) (s := 2) (by norm_num) (by norm_num) (by norm_num) (by beta_reduce; norm_num)
  linarith
private lemma log_d_lb_8 : ((-101237997 : ℝ) / 78125000) ≤ Real.log (((821 : ℝ) / 3000)) := by
  have h := le_log_of_scale (x := ((821 : ℝ) / 3000)) (y := ((821 : ℝ) / 750)) (q := ((5653 : ℝ) / 62500)) (s := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by beta_reduce; norm_num)
  linarith
private lemma log_d_ub_9 : Real.log (((553 : ℝ) / 2400)) ≤ ((-14678645409 : ℝ) / 10000000000) := by
  have h := log_le_of_scale (x := ((553 : ℝ) / 2400)) (y := ((553 : ℝ) / 300)) (q := ((611577 : ℝ) / 1000000)) (s := 3) (by norm_num) (by norm_num) (by norm_num) (by beta_reduce; norm_num)
  linarith
private lemma log_d_lb_9 : ((-458708607 : ℝ) / 312500000) ≤ Real.log (((553 : ℝ) / 2400)) := by
  have h := le_log_of_scale (x := ((553 : ℝ) / 2400)) (y := ((553 : ℝ) / 300)) (q := ((305787 : ℝ) / 500000)) (s := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by beta_reduce; norm_num)
  linarith
private lemma log_d_ub_10 : Real.log (((1201 : ℝ) / 6000)) ≤ ((-16086035409 : ℝ) / 10000000000) := by
  have h := log_le_of_scale (x := ((1201 : ℝ) / 6000)) (y := ((1201 : ℝ) / 750)) (q := ((235419 : ℝ) / 500000)) (s := 3) (by norm_num) (by norm_num) (by norm_num) (by beta_reduce; norm_num)
  linarith
private lemma log_d_lb_10 : ((-1005379089 : ℝ) / 625000000) ≤ Real.log (((1201 : ℝ) / 6000)) := by
  have h := le_log_of_scale (x := ((1201 : ℝ) / 6000)) (y := ((1201 : ℝ) / 750)) (q := ((94167 : ℝ) / 200000)) (s := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by beta_reduce; norm_num)
  linarith
private lemma log_d_ub_11 : Real.log (((137 : ℝ) / 750)) ≤ ((-17000905409 : ℝ) / 10000000000) := by
  have h := log_le_of_scale (x := ((137 : ℝ) / 750)) (y := ((548 : ℝ) / 375)) (q := ((379351 : ℝ) / 1000000)) (s := 3) (by norm_num) (by norm_num) (by norm_num) (by beta_reduce; norm_num)
  linarith
private lemma log_d_lb_11 : ((-16602476 : ℝ) / 9765625) ≤ Real.log (((137 : ℝ) / 750)) := by
  have h := le_log_of_scale (x := ((137 : ℝ) / 750)) (y := ((548 : ℝ) / 375)) (q := ((94837 : ℝ) / 250000)) (s := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by beta_reduce; norm_num)
  linarith
private lemma log_d_ub_12 : Real.log (((43 : ℝ) / 250)) ≤ ((-17602595409 : ℝ) / 10000000000) := by
  have h := log_le_of_scale (x := ((43 : ℝ) / 250)) (y := ((172 : ℝ) / 125)) (q := ((159591 : ℝ) / 500000)) (s := 3) (by norm_num) (by norm_num) (by norm_num) (by beta_reduce; norm_num)
  linarith
private lemma log_d_lb_12 : ((-1100164089 : ℝ) / 625000000) ≤ Real.log (((43 : ℝ) / 250)) := by
  have h := le_log_of_scale (x := ((43 : ℝ) / 250)) (y := ((172 : ℝ) / 125)) (q := ((319179 : ℝ) / 1000000)) (s := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by beta_reduce; norm_num)
  linarith


private lemma A_nat_mem : ∀ i j : Fin 12, (fun i j : Fin 12 => (![![582, 765, 955, 1127, 1252, 1319], ![765, 861, 993, 1083, 1137, 1161], ![955, 993, 987, 1018, 1024, 1023], ![1127, 1083, 1018, 939, 922, 911], ![1252, 1137, 1024, 922, 839, 826], ![1319, 1161, 1023, 911, 826, 760]] : Fin 6 → Fin 6 → ℕ) ((fun i : Fin 12 => (if h : i.val < 6 then ⟨i.val, h⟩ else ⟨11 - i.val, by omega⟩ : Fin 6)) i) ((fun i : Fin 12 => (if h : i.val < 6 then ⟨i.val, h⟩ else ⟨11 - i.val, by omega⟩ : Fin 6)) j)) i j ∈ ({582, 760, 765, 826, 839, 861, 911, 922, 939, 955, 987, 993, 1018, 1023, 1024, 1083, 1127, 1137, 1161, 1252, 1319} : Finset ℕ) := by decide

private lemma log_A_ub_int_spec (n : ℕ) (hn : n ∈ ({582, 760, 765, 826, 839, 861, 911, 922, 939, 955, 987, 993, 1018, 1023, 1024, 1083, 1127, 1137, 1161, 1252, 1319} : Finset ℕ)) :
    Real.log ((n : ℝ) / 1000) ≤ (((fun n : ℕ => (match n with | 582 => -5412831803 | 760 => -2744351803 | 765 => -2678781803 | 826 => -1911591803 | 839 => -1755431803 | 861 => -1496591803 | 911 => -932111803 | 922 => -812081803 | 939 => -629381803 | 955 => -460421803 | 987 => -130841803 | 993 => -70231803 | 1018 => 178410000 | 1023 => 227410000 | 1024 => 237180000 | 1083 => 797360000 | 1127 => 1195610000 | 1137 => 1283950000 | 1161 => 1492830000 | 1252 => 2247440000 | 1319 => 2768750000 | _ => 0 : ℤ)) n : ℤ) : ℝ) / 10000000000 := by
  fin_cases hn
  · simpa [] using (by have h := log_A_582; norm_num [] at h ⊢; linarith : Real.log ((582 : ℝ) / 1000) ≤ (((fun n : ℕ => (match n with | 582 => -5412831803 | 760 => -2744351803 | 765 => -2678781803 | 826 => -1911591803 | 839 => -1755431803 | 861 => -1496591803 | 911 => -932111803 | 922 => -812081803 | 939 => -629381803 | 955 => -460421803 | 987 => -130841803 | 993 => -70231803 | 1018 => 178410000 | 1023 => 227410000 | 1024 => 237180000 | 1083 => 797360000 | 1127 => 1195610000 | 1137 => 1283950000 | 1161 => 1492830000 | 1252 => 2247440000 | 1319 => 2768750000 | _ => 0 : ℤ)) 582 : ℤ) : ℝ) / 10000000000)
  · simpa [] using (by have h := log_A_760; norm_num [] at h ⊢; linarith : Real.log ((760 : ℝ) / 1000) ≤ (((fun n : ℕ => (match n with | 582 => -5412831803 | 760 => -2744351803 | 765 => -2678781803 | 826 => -1911591803 | 839 => -1755431803 | 861 => -1496591803 | 911 => -932111803 | 922 => -812081803 | 939 => -629381803 | 955 => -460421803 | 987 => -130841803 | 993 => -70231803 | 1018 => 178410000 | 1023 => 227410000 | 1024 => 237180000 | 1083 => 797360000 | 1127 => 1195610000 | 1137 => 1283950000 | 1161 => 1492830000 | 1252 => 2247440000 | 1319 => 2768750000 | _ => 0 : ℤ)) 760 : ℤ) : ℝ) / 10000000000)
  · simpa [] using (by have h := log_A_765; norm_num [] at h ⊢; linarith : Real.log ((765 : ℝ) / 1000) ≤ (((fun n : ℕ => (match n with | 582 => -5412831803 | 760 => -2744351803 | 765 => -2678781803 | 826 => -1911591803 | 839 => -1755431803 | 861 => -1496591803 | 911 => -932111803 | 922 => -812081803 | 939 => -629381803 | 955 => -460421803 | 987 => -130841803 | 993 => -70231803 | 1018 => 178410000 | 1023 => 227410000 | 1024 => 237180000 | 1083 => 797360000 | 1127 => 1195610000 | 1137 => 1283950000 | 1161 => 1492830000 | 1252 => 2247440000 | 1319 => 2768750000 | _ => 0 : ℤ)) 765 : ℤ) : ℝ) / 10000000000)
  · simpa [] using (by have h := log_A_826; norm_num [] at h ⊢; linarith : Real.log ((826 : ℝ) / 1000) ≤ (((fun n : ℕ => (match n with | 582 => -5412831803 | 760 => -2744351803 | 765 => -2678781803 | 826 => -1911591803 | 839 => -1755431803 | 861 => -1496591803 | 911 => -932111803 | 922 => -812081803 | 939 => -629381803 | 955 => -460421803 | 987 => -130841803 | 993 => -70231803 | 1018 => 178410000 | 1023 => 227410000 | 1024 => 237180000 | 1083 => 797360000 | 1127 => 1195610000 | 1137 => 1283950000 | 1161 => 1492830000 | 1252 => 2247440000 | 1319 => 2768750000 | _ => 0 : ℤ)) 826 : ℤ) : ℝ) / 10000000000)
  · simpa [] using (by have h := log_A_839; norm_num [] at h ⊢; linarith : Real.log ((839 : ℝ) / 1000) ≤ (((fun n : ℕ => (match n with | 582 => -5412831803 | 760 => -2744351803 | 765 => -2678781803 | 826 => -1911591803 | 839 => -1755431803 | 861 => -1496591803 | 911 => -932111803 | 922 => -812081803 | 939 => -629381803 | 955 => -460421803 | 987 => -130841803 | 993 => -70231803 | 1018 => 178410000 | 1023 => 227410000 | 1024 => 237180000 | 1083 => 797360000 | 1127 => 1195610000 | 1137 => 1283950000 | 1161 => 1492830000 | 1252 => 2247440000 | 1319 => 2768750000 | _ => 0 : ℤ)) 839 : ℤ) : ℝ) / 10000000000)
  · simpa [] using (by have h := log_A_861; norm_num [] at h ⊢; linarith : Real.log ((861 : ℝ) / 1000) ≤ (((fun n : ℕ => (match n with | 582 => -5412831803 | 760 => -2744351803 | 765 => -2678781803 | 826 => -1911591803 | 839 => -1755431803 | 861 => -1496591803 | 911 => -932111803 | 922 => -812081803 | 939 => -629381803 | 955 => -460421803 | 987 => -130841803 | 993 => -70231803 | 1018 => 178410000 | 1023 => 227410000 | 1024 => 237180000 | 1083 => 797360000 | 1127 => 1195610000 | 1137 => 1283950000 | 1161 => 1492830000 | 1252 => 2247440000 | 1319 => 2768750000 | _ => 0 : ℤ)) 861 : ℤ) : ℝ) / 10000000000)
  · simpa [] using (by have h := log_A_911; norm_num [] at h ⊢; linarith : Real.log ((911 : ℝ) / 1000) ≤ (((fun n : ℕ => (match n with | 582 => -5412831803 | 760 => -2744351803 | 765 => -2678781803 | 826 => -1911591803 | 839 => -1755431803 | 861 => -1496591803 | 911 => -932111803 | 922 => -812081803 | 939 => -629381803 | 955 => -460421803 | 987 => -130841803 | 993 => -70231803 | 1018 => 178410000 | 1023 => 227410000 | 1024 => 237180000 | 1083 => 797360000 | 1127 => 1195610000 | 1137 => 1283950000 | 1161 => 1492830000 | 1252 => 2247440000 | 1319 => 2768750000 | _ => 0 : ℤ)) 911 : ℤ) : ℝ) / 10000000000)
  · simpa [] using (by have h := log_A_922; norm_num [] at h ⊢; linarith : Real.log ((922 : ℝ) / 1000) ≤ (((fun n : ℕ => (match n with | 582 => -5412831803 | 760 => -2744351803 | 765 => -2678781803 | 826 => -1911591803 | 839 => -1755431803 | 861 => -1496591803 | 911 => -932111803 | 922 => -812081803 | 939 => -629381803 | 955 => -460421803 | 987 => -130841803 | 993 => -70231803 | 1018 => 178410000 | 1023 => 227410000 | 1024 => 237180000 | 1083 => 797360000 | 1127 => 1195610000 | 1137 => 1283950000 | 1161 => 1492830000 | 1252 => 2247440000 | 1319 => 2768750000 | _ => 0 : ℤ)) 922 : ℤ) : ℝ) / 10000000000)
  · simpa [] using (by have h := log_A_939; norm_num [] at h ⊢; linarith : Real.log ((939 : ℝ) / 1000) ≤ (((fun n : ℕ => (match n with | 582 => -5412831803 | 760 => -2744351803 | 765 => -2678781803 | 826 => -1911591803 | 839 => -1755431803 | 861 => -1496591803 | 911 => -932111803 | 922 => -812081803 | 939 => -629381803 | 955 => -460421803 | 987 => -130841803 | 993 => -70231803 | 1018 => 178410000 | 1023 => 227410000 | 1024 => 237180000 | 1083 => 797360000 | 1127 => 1195610000 | 1137 => 1283950000 | 1161 => 1492830000 | 1252 => 2247440000 | 1319 => 2768750000 | _ => 0 : ℤ)) 939 : ℤ) : ℝ) / 10000000000)
  · simpa [] using (by have h := log_A_955; norm_num [] at h ⊢; linarith : Real.log ((955 : ℝ) / 1000) ≤ (((fun n : ℕ => (match n with | 582 => -5412831803 | 760 => -2744351803 | 765 => -2678781803 | 826 => -1911591803 | 839 => -1755431803 | 861 => -1496591803 | 911 => -932111803 | 922 => -812081803 | 939 => -629381803 | 955 => -460421803 | 987 => -130841803 | 993 => -70231803 | 1018 => 178410000 | 1023 => 227410000 | 1024 => 237180000 | 1083 => 797360000 | 1127 => 1195610000 | 1137 => 1283950000 | 1161 => 1492830000 | 1252 => 2247440000 | 1319 => 2768750000 | _ => 0 : ℤ)) 955 : ℤ) : ℝ) / 10000000000)
  · simpa [] using (by have h := log_A_987; norm_num [] at h ⊢; linarith : Real.log ((987 : ℝ) / 1000) ≤ (((fun n : ℕ => (match n with | 582 => -5412831803 | 760 => -2744351803 | 765 => -2678781803 | 826 => -1911591803 | 839 => -1755431803 | 861 => -1496591803 | 911 => -932111803 | 922 => -812081803 | 939 => -629381803 | 955 => -460421803 | 987 => -130841803 | 993 => -70231803 | 1018 => 178410000 | 1023 => 227410000 | 1024 => 237180000 | 1083 => 797360000 | 1127 => 1195610000 | 1137 => 1283950000 | 1161 => 1492830000 | 1252 => 2247440000 | 1319 => 2768750000 | _ => 0 : ℤ)) 987 : ℤ) : ℝ) / 10000000000)
  · simpa [] using (by have h := log_A_993; norm_num [] at h ⊢; linarith : Real.log ((993 : ℝ) / 1000) ≤ (((fun n : ℕ => (match n with | 582 => -5412831803 | 760 => -2744351803 | 765 => -2678781803 | 826 => -1911591803 | 839 => -1755431803 | 861 => -1496591803 | 911 => -932111803 | 922 => -812081803 | 939 => -629381803 | 955 => -460421803 | 987 => -130841803 | 993 => -70231803 | 1018 => 178410000 | 1023 => 227410000 | 1024 => 237180000 | 1083 => 797360000 | 1127 => 1195610000 | 1137 => 1283950000 | 1161 => 1492830000 | 1252 => 2247440000 | 1319 => 2768750000 | _ => 0 : ℤ)) 993 : ℤ) : ℝ) / 10000000000)
  · simpa [] using (by have h := log_A_1018; norm_num [] at h ⊢; linarith : Real.log ((1018 : ℝ) / 1000) ≤ (((fun n : ℕ => (match n with | 582 => -5412831803 | 760 => -2744351803 | 765 => -2678781803 | 826 => -1911591803 | 839 => -1755431803 | 861 => -1496591803 | 911 => -932111803 | 922 => -812081803 | 939 => -629381803 | 955 => -460421803 | 987 => -130841803 | 993 => -70231803 | 1018 => 178410000 | 1023 => 227410000 | 1024 => 237180000 | 1083 => 797360000 | 1127 => 1195610000 | 1137 => 1283950000 | 1161 => 1492830000 | 1252 => 2247440000 | 1319 => 2768750000 | _ => 0 : ℤ)) 1018 : ℤ) : ℝ) / 10000000000)
  · simpa [] using (by have h := log_A_1023; norm_num [] at h ⊢; linarith : Real.log ((1023 : ℝ) / 1000) ≤ (((fun n : ℕ => (match n with | 582 => -5412831803 | 760 => -2744351803 | 765 => -2678781803 | 826 => -1911591803 | 839 => -1755431803 | 861 => -1496591803 | 911 => -932111803 | 922 => -812081803 | 939 => -629381803 | 955 => -460421803 | 987 => -130841803 | 993 => -70231803 | 1018 => 178410000 | 1023 => 227410000 | 1024 => 237180000 | 1083 => 797360000 | 1127 => 1195610000 | 1137 => 1283950000 | 1161 => 1492830000 | 1252 => 2247440000 | 1319 => 2768750000 | _ => 0 : ℤ)) 1023 : ℤ) : ℝ) / 10000000000)
  · simpa [] using (by have h := log_A_1024; norm_num [] at h ⊢; linarith : Real.log ((1024 : ℝ) / 1000) ≤ (((fun n : ℕ => (match n with | 582 => -5412831803 | 760 => -2744351803 | 765 => -2678781803 | 826 => -1911591803 | 839 => -1755431803 | 861 => -1496591803 | 911 => -932111803 | 922 => -812081803 | 939 => -629381803 | 955 => -460421803 | 987 => -130841803 | 993 => -70231803 | 1018 => 178410000 | 1023 => 227410000 | 1024 => 237180000 | 1083 => 797360000 | 1127 => 1195610000 | 1137 => 1283950000 | 1161 => 1492830000 | 1252 => 2247440000 | 1319 => 2768750000 | _ => 0 : ℤ)) 1024 : ℤ) : ℝ) / 10000000000)
  · simpa [] using (by have h := log_A_1083; norm_num [] at h ⊢; linarith : Real.log ((1083 : ℝ) / 1000) ≤ (((fun n : ℕ => (match n with | 582 => -5412831803 | 760 => -2744351803 | 765 => -2678781803 | 826 => -1911591803 | 839 => -1755431803 | 861 => -1496591803 | 911 => -932111803 | 922 => -812081803 | 939 => -629381803 | 955 => -460421803 | 987 => -130841803 | 993 => -70231803 | 1018 => 178410000 | 1023 => 227410000 | 1024 => 237180000 | 1083 => 797360000 | 1127 => 1195610000 | 1137 => 1283950000 | 1161 => 1492830000 | 1252 => 2247440000 | 1319 => 2768750000 | _ => 0 : ℤ)) 1083 : ℤ) : ℝ) / 10000000000)
  · simpa [] using (by have h := log_A_1127; norm_num [] at h ⊢; linarith : Real.log ((1127 : ℝ) / 1000) ≤ (((fun n : ℕ => (match n with | 582 => -5412831803 | 760 => -2744351803 | 765 => -2678781803 | 826 => -1911591803 | 839 => -1755431803 | 861 => -1496591803 | 911 => -932111803 | 922 => -812081803 | 939 => -629381803 | 955 => -460421803 | 987 => -130841803 | 993 => -70231803 | 1018 => 178410000 | 1023 => 227410000 | 1024 => 237180000 | 1083 => 797360000 | 1127 => 1195610000 | 1137 => 1283950000 | 1161 => 1492830000 | 1252 => 2247440000 | 1319 => 2768750000 | _ => 0 : ℤ)) 1127 : ℤ) : ℝ) / 10000000000)
  · simpa [] using (by have h := log_A_1137; norm_num [] at h ⊢; linarith : Real.log ((1137 : ℝ) / 1000) ≤ (((fun n : ℕ => (match n with | 582 => -5412831803 | 760 => -2744351803 | 765 => -2678781803 | 826 => -1911591803 | 839 => -1755431803 | 861 => -1496591803 | 911 => -932111803 | 922 => -812081803 | 939 => -629381803 | 955 => -460421803 | 987 => -130841803 | 993 => -70231803 | 1018 => 178410000 | 1023 => 227410000 | 1024 => 237180000 | 1083 => 797360000 | 1127 => 1195610000 | 1137 => 1283950000 | 1161 => 1492830000 | 1252 => 2247440000 | 1319 => 2768750000 | _ => 0 : ℤ)) 1137 : ℤ) : ℝ) / 10000000000)
  · simpa [] using (by have h := log_A_1161; norm_num [] at h ⊢; linarith : Real.log ((1161 : ℝ) / 1000) ≤ (((fun n : ℕ => (match n with | 582 => -5412831803 | 760 => -2744351803 | 765 => -2678781803 | 826 => -1911591803 | 839 => -1755431803 | 861 => -1496591803 | 911 => -932111803 | 922 => -812081803 | 939 => -629381803 | 955 => -460421803 | 987 => -130841803 | 993 => -70231803 | 1018 => 178410000 | 1023 => 227410000 | 1024 => 237180000 | 1083 => 797360000 | 1127 => 1195610000 | 1137 => 1283950000 | 1161 => 1492830000 | 1252 => 2247440000 | 1319 => 2768750000 | _ => 0 : ℤ)) 1161 : ℤ) : ℝ) / 10000000000)
  · simpa [] using (by have h := log_A_1252; norm_num [] at h ⊢; linarith : Real.log ((1252 : ℝ) / 1000) ≤ (((fun n : ℕ => (match n with | 582 => -5412831803 | 760 => -2744351803 | 765 => -2678781803 | 826 => -1911591803 | 839 => -1755431803 | 861 => -1496591803 | 911 => -932111803 | 922 => -812081803 | 939 => -629381803 | 955 => -460421803 | 987 => -130841803 | 993 => -70231803 | 1018 => 178410000 | 1023 => 227410000 | 1024 => 237180000 | 1083 => 797360000 | 1127 => 1195610000 | 1137 => 1283950000 | 1161 => 1492830000 | 1252 => 2247440000 | 1319 => 2768750000 | _ => 0 : ℤ)) 1252 : ℤ) : ℝ) / 10000000000)
  · simpa [] using (by have h := log_A_1319; norm_num [] at h ⊢; linarith : Real.log ((1319 : ℝ) / 1000) ≤ (((fun n : ℕ => (match n with | 582 => -5412831803 | 760 => -2744351803 | 765 => -2678781803 | 826 => -1911591803 | 839 => -1755431803 | 861 => -1496591803 | 911 => -932111803 | 922 => -812081803 | 939 => -629381803 | 955 => -460421803 | 987 => -130841803 | 993 => -70231803 | 1018 => 178410000 | 1023 => 227410000 | 1024 => 237180000 | 1083 => 797360000 | 1127 => 1195610000 | 1137 => 1283950000 | 1161 => 1492830000 | 1252 => 2247440000 | 1319 => 2768750000 | _ => 0 : ℤ)) 1319 : ℤ) : ℝ) / 10000000000)

private lemma sum_A_int_le :
    (∑ i : Fin 12, ∑ j : Fin 12, ((fun i j : Fin 12 => (![![582, 765, 955, 1127, 1252, 1319], ![765, 861, 993, 1083, 1137, 1161], ![955, 993, 987, 1018, 1024, 1023], ![1127, 1083, 1018, 939, 922, 911], ![1252, 1137, 1024, 922, 839, 826], ![1319, 1161, 1023, 911, 826, 760]] : Fin 6 → Fin 6 → ℕ) ((fun i : Fin 12 => (if h : i.val < 6 then ⟨i.val, h⟩ else ⟨11 - i.val, by omega⟩ : Fin 6)) i) ((fun i : Fin 12 => (if h : i.val < 6 then ⟨i.val, h⟩ else ⟨11 - i.val, by omega⟩ : Fin 6)) j)) i j : ℤ) * (fun n : ℕ => (match n with | 582 => -5412831803 | 760 => -2744351803 | 765 => -2678781803 | 826 => -1911591803 | 839 => -1755431803 | 861 => -1496591803 | 911 => -932111803 | 922 => -812081803 | 939 => -629381803 | 955 => -460421803 | 987 => -130841803 | 993 => -70231803 | 1018 => 178410000 | 1023 => 227410000 | 1024 => 237180000 | 1083 => 797360000 | 1127 => 1195610000 | 1137 => 1283950000 | 1161 => 1492830000 | 1252 => 2247440000 | 1319 => 2768750000 | _ => 0 : ℤ)) ((fun i j : Fin 12 => (![![582, 765, 955, 1127, 1252, 1319], ![765, 861, 993, 1083, 1137, 1161], ![955, 993, 987, 1018, 1024, 1023], ![1127, 1083, 1018, 939, 922, 911], ![1252, 1137, 1024, 922, 839, 826], ![1319, 1161, 1023, 911, 826, 760]] : Fin 6 → Fin 6 → ℕ) ((fun i : Fin 12 => (if h : i.val < 6 then ⟨i.val, h⟩ else ⟨11 - i.val, by omega⟩ : Fin 6)) i) ((fun i : Fin 12 => (if h : i.val < 6 then ⟨i.val, h⟩ else ⟨11 - i.val, by omega⟩ : Fin 6)) j)) i j)) ≤ 19460894925056 := by
  decide

private lemma sum_A_bound_gen (a : Fin 12 → Fin 12 → ℕ) (L : ℕ → ℤ)
    (hspec : ∀ i j, Real.log ((a i j : ℝ) / 1000) ≤ ((L (a i j) : ℤ) : ℝ) / 10000000000)
    (hint : (∑ i : Fin 12, ∑ j : Fin 12, (a i j : ℤ) * L (a i j)) ≤ 19460894925056) :
    ∑ i : Fin 12, ∑ j : Fin 12, ((a i j : ℝ) / 1000) * Real.log ((a i j : ℝ) / 1000) ≤ ((76019120801 : ℝ) / 39062500000) := by
  have hcell : ∀ i j : Fin 12, ((a i j : ℝ) / 1000) * Real.log ((a i j : ℝ) / 1000) ≤
      ((a i j : ℝ) / 1000) * (((L (a i j) : ℤ) : ℝ) / 10000000000) := fun i j =>
    mul_le_mul_of_nonneg_left (hspec i j) (by positivity)
  have hsum_eq : (∑ i : Fin 12, ∑ j : Fin 12,
      ((a i j : ℝ) / 1000) * (((L (a i j) : ℤ) : ℝ) / 10000000000)) =
      ((∑ i : Fin 12, ∑ j : Fin 12, (a i j : ℤ) * L (a i j) : ℤ) : ℝ) / 10000000000000 := by
    rw [Int.cast_sum, Finset.sum_div]
    apply Finset.sum_congr rfl; intro i _
    rw [Int.cast_sum, Finset.sum_div]
    apply Finset.sum_congr rfl; intro j _
    push_cast
    ring
  calc ∑ i : Fin 12, ∑ j : Fin 12, ((a i j : ℝ) / 1000) * Real.log ((a i j : ℝ) / 1000)
      ≤ ∑ i : Fin 12, ∑ j : Fin 12,
          ((a i j : ℝ) / 1000) * (((L (a i j) : ℤ) : ℝ) / 10000000000) :=
        sum_le_sum fun i _ => sum_le_sum fun j _ => hcell i j
    _ = ((∑ i : Fin 12, ∑ j : Fin 12, (a i j : ℤ) * L (a i j) : ℤ) : ℝ) / 10000000000000 := hsum_eq
    _ ≤ (19460894925056 : ℝ) / 10000000000000 := by
        apply div_le_div_of_nonneg_right _ (by norm_num)
        exact_mod_cast hint
    _ = ((76019120801 : ℝ) / 39062500000) := by norm_num

private lemma sum_A_bound :
    ∑ i : Fin 12, ∑ j : Fin 12, (((fun i j : Fin 12 => (![![582, 765, 955, 1127, 1252, 1319], ![765, 861, 993, 1083, 1137, 1161], ![955, 993, 987, 1018, 1024, 1023], ![1127, 1083, 1018, 939, 922, 911], ![1252, 1137, 1024, 922, 839, 826], ![1319, 1161, 1023, 911, 826, 760]] : Fin 6 → Fin 6 → ℕ) ((fun i : Fin 12 => (if h : i.val < 6 then ⟨i.val, h⟩ else ⟨11 - i.val, by omega⟩ : Fin 6)) i) ((fun i : Fin 12 => (if h : i.val < 6 then ⟨i.val, h⟩ else ⟨11 - i.val, by omega⟩ : Fin 6)) j)) i j : ℝ) / 1000) * Real.log (((fun i j : Fin 12 => (![![582, 765, 955, 1127, 1252, 1319], ![765, 861, 993, 1083, 1137, 1161], ![955, 993, 987, 1018, 1024, 1023], ![1127, 1083, 1018, 939, 922, 911], ![1252, 1137, 1024, 922, 839, 826], ![1319, 1161, 1023, 911, 826, 760]] : Fin 6 → Fin 6 → ℕ) ((fun i : Fin 12 => (if h : i.val < 6 then ⟨i.val, h⟩ else ⟨11 - i.val, by omega⟩ : Fin 6)) i) ((fun i : Fin 12 => (if h : i.val < 6 then ⟨i.val, h⟩ else ⟨11 - i.val, by omega⟩ : Fin 6)) j)) i j : ℝ) / 1000) ≤ ((76019120801 : ℝ) / 39062500000) :=
  sum_A_bound_gen (fun i j : Fin 12 => (![![582, 765, 955, 1127, 1252, 1319], ![765, 861, 993, 1083, 1137, 1161], ![955, 993, 987, 1018, 1024, 1023], ![1127, 1083, 1018, 939, 922, 911], ![1252, 1137, 1024, 922, 839, 826], ![1319, 1161, 1023, 911, 826, 760]] : Fin 6 → Fin 6 → ℕ) ((fun i : Fin 12 => (if h : i.val < 6 then ⟨i.val, h⟩ else ⟨11 - i.val, by omega⟩ : Fin 6)) i) ((fun i : Fin 12 => (if h : i.val < 6 then ⟨i.val, h⟩ else ⟨11 - i.val, by omega⟩ : Fin 6)) j)) (fun n : ℕ => (match n with | 582 => -5412831803 | 760 => -2744351803 | 765 => -2678781803 | 826 => -1911591803 | 839 => -1755431803 | 861 => -1496591803 | 911 => -932111803 | 922 => -812081803 | 939 => -629381803 | 955 => -460421803 | 987 => -130841803 | 993 => -70231803 | 1018 => 178410000 | 1023 => 227410000 | 1024 => 237180000 | 1083 => 797360000 | 1127 => 1195610000 | 1137 => 1283950000 | 1161 => 1492830000 | 1252 => 2247440000 | 1319 => 2768750000 | _ => 0 : ℤ)) (fun i j => log_A_ub_int_spec ((fun i j : Fin 12 => (![![582, 765, 955, 1127, 1252, 1319], ![765, 861, 993, 1083, 1137, 1161], ![955, 993, 987, 1018, 1024, 1023], ![1127, 1083, 1018, 939, 922, 911], ![1252, 1137, 1024, 922, 839, 826], ![1319, 1161, 1023, 911, 826, 760]] : Fin 6 → Fin 6 → ℕ) ((fun i : Fin 12 => (if h : i.val < 6 then ⟨i.val, h⟩ else ⟨11 - i.val, by omega⟩ : Fin 6)) i) ((fun i : Fin 12 => (if h : i.val < 6 then ⟨i.val, h⟩ else ⟨11 - i.val, by omega⟩ : Fin 6)) j)) i j) (A_nat_mem i j)) sum_A_int_le

private lemma int_d_0 :
    ∫ t in (0 : ℝ)..1, ((1 - t) * ((1 : ℝ)) + t * (((1903 : ℝ) / 2000))) * Real.log ((1 - t) * ((1 : ℝ)) + t * (((1903 : ℝ) / 2000))) ≤ ((-2889141873829 : ℝ) / 121250000000000) := by
  rw [integral_mul_log_linear (by norm_num) (by norm_num) (by norm_num)]
  have ha := log_d_ub_0
  have hb := log_d_lb_1
  ring_nf
  linarith

private lemma int_d_rev_0 :
    ∫ t in (0 : ℝ)..1, ((1 - t) * (((1903 : ℝ) / 2000)) + t * ((1 : ℝ))) * Real.log ((1 - t) * (((1903 : ℝ) / 2000)) + t * ((1 : ℝ))) ≤ ((-2889141873829 : ℝ) / 121250000000000) := by
  rw [integral_mul_log_linear (by norm_num) (by norm_num) (by norm_num)]
  have ha := log_d_ub_0
  have hb := log_d_lb_1
  ring_nf
  linarith

private lemma int_d_1 :
    ∫ t in (0 : ℝ)..1, ((1 - t) * (((1903 : ℝ) / 2000)) + t * (((349 : ℝ) / 400))) * Real.log ((1 - t) * (((1903 : ℝ) / 2000)) + t * (((349 : ℝ) / 400))) ≤ ((-529036895755227 : ℝ) / 6320000000000000) := by
  rw [integral_mul_log_linear (by norm_num) (by norm_num) (by norm_num)]
  have ha := log_d_ub_1
  have hb := log_d_lb_2
  ring_nf
  linarith

private lemma int_d_rev_1 :
    ∫ t in (0 : ℝ)..1, ((1 - t) * (((349 : ℝ) / 400)) + t * (((1903 : ℝ) / 2000))) * Real.log ((1 - t) * (((349 : ℝ) / 400)) + t * (((1903 : ℝ) / 2000))) ≤ ((-529036895755227 : ℝ) / 6320000000000000) := by
  rw [integral_mul_log_linear (by norm_num) (by norm_num) (by norm_num)]
  have ha := log_d_ub_1
  have hb := log_d_lb_2
  ring_nf
  linarith

private lemma int_d_2 :
    ∫ t in (0 : ℝ)..1, ((1 - t) * (((349 : ℝ) / 400)) + t * (((9229 : ℝ) / 12000))) * Real.log ((1 - t) * (((349 : ℝ) / 400)) + t * (((9229 : ℝ) / 12000))) ≤ ((-12028480828430843 : ℝ) / 74460000000000000) := by
  rw [integral_mul_log_linear (by norm_num) (by norm_num) (by norm_num)]
  have ha := log_d_ub_2
  have hb := log_d_lb_3
  ring_nf
  linarith

private lemma int_d_rev_2 :
    ∫ t in (0 : ℝ)..1, ((1 - t) * (((9229 : ℝ) / 12000)) + t * (((349 : ℝ) / 400))) * Real.log ((1 - t) * (((9229 : ℝ) / 12000)) + t * (((349 : ℝ) / 400))) ≤ ((-12028480828430843 : ℝ) / 74460000000000000) := by
  rw [integral_mul_log_linear (by norm_num) (by norm_num) (by norm_num)]
  have ha := log_d_ub_2
  have hb := log_d_lb_3
  ring_nf
  linarith

private lemma int_d_3 :
    ∫ t in (0 : ℝ)..1, ((1 - t) * (((9229 : ℝ) / 12000)) + t * (((97 : ℝ) / 150))) * Real.log ((1 - t) * (((9229 : ℝ) / 12000)) + t * (((97 : ℝ) / 150))) ≤ ((-85908976543236323 : ℝ) / 352560000000000000) := by
  rw [integral_mul_log_linear (by norm_num) (by norm_num) (by norm_num)]
  have ha := log_d_ub_3
  have hb := log_d_lb_4
  ring_nf
  linarith

private lemma int_d_rev_3 :
    ∫ t in (0 : ℝ)..1, ((1 - t) * (((97 : ℝ) / 150)) + t * (((9229 : ℝ) / 12000))) * Real.log ((1 - t) * (((97 : ℝ) / 150)) + t * (((9229 : ℝ) / 12000))) ≤ ((-85908976543236323 : ℝ) / 352560000000000000) := by
  rw [integral_mul_log_linear (by norm_num) (by norm_num) (by norm_num)]
  have ha := log_d_ub_3
  have hb := log_d_lb_4
  ring_nf
  linarith

private lemma int_d_4 :
    ∫ t in (0 : ℝ)..1, ((1 - t) * (((97 : ℝ) / 150)) + t * (((6343 : ℝ) / 12000))) * Real.log ((1 - t) * (((97 : ℝ) / 150)) + t * (((6343 : ℝ) / 12000))) ≤ ((-6619382253715963 : ℝ) / 21255000000000000) := by
  rw [integral_mul_log_linear (by norm_num) (by norm_num) (by norm_num)]
  have ha := log_d_ub_4
  have hb := log_d_lb_5
  ring_nf
  linarith

private lemma int_d_rev_4 :
    ∫ t in (0 : ℝ)..1, ((1 - t) * (((6343 : ℝ) / 12000)) + t * (((97 : ℝ) / 150))) * Real.log ((1 - t) * (((6343 : ℝ) / 12000)) + t * (((97 : ℝ) / 150))) ≤ ((-6619382253715963 : ℝ) / 21255000000000000) := by
  rw [integral_mul_log_linear (by norm_num) (by norm_num) (by norm_num)]
  have ha := log_d_ub_4
  have hb := log_d_lb_5
  ring_nf
  linarith

private lemma int_d_5 :
    ∫ t in (0 : ℝ)..1, ((1 - t) * (((6343 : ℝ) / 12000)) + t * (((421 : ℝ) / 1000))) * Real.log ((1 - t) * (((6343 : ℝ) / 12000)) + t * (((421 : ℝ) / 1000))) ≤ ((-109262503707181483 : ℝ) / 309840000000000000) := by
  rw [integral_mul_log_linear (by norm_num) (by norm_num) (by norm_num)]
  have ha := log_d_ub_5
  have hb := log_d_lb_6
  ring_nf
  linarith

private lemma int_d_rev_5 :
    ∫ t in (0 : ℝ)..1, ((1 - t) * (((421 : ℝ) / 1000)) + t * (((6343 : ℝ) / 12000))) * Real.log ((1 - t) * (((421 : ℝ) / 1000)) + t * (((6343 : ℝ) / 12000))) ≤ ((-109262503707181483 : ℝ) / 309840000000000000) := by
  rw [integral_mul_log_linear (by norm_num) (by norm_num) (by norm_num)]
  have ha := log_d_ub_5
  have hb := log_d_lb_6
  ring_nf
  linarith

private lemma int_d_6 :
    ∫ t in (0 : ℝ)..1, ((1 - t) * (((421 : ℝ) / 1000)) + t * (((1351 : ℝ) / 4000))) * Real.log ((1 - t) * (((421 : ℝ) / 1000)) + t * (((1351 : ℝ) / 4000))) ≤ ((-61095125983937 : ℝ) / 166500000000000) := by
  rw [integral_mul_log_linear (by norm_num) (by norm_num) (by norm_num)]
  have ha := log_d_ub_6
  have hb := log_d_lb_7
  ring_nf
  linarith

private lemma int_d_rev_6 :
    ∫ t in (0 : ℝ)..1, ((1 - t) * (((1351 : ℝ) / 4000)) + t * (((421 : ℝ) / 1000))) * Real.log ((1 - t) * (((1351 : ℝ) / 4000)) + t * (((421 : ℝ) / 1000))) ≤ ((-61095125983937 : ℝ) / 166500000000000) := by
  rw [integral_mul_log_linear (by norm_num) (by norm_num) (by norm_num)]
  have ha := log_d_ub_6
  have hb := log_d_lb_7
  ring_nf
  linarith

private lemma int_d_7 :
    ∫ t in (0 : ℝ)..1, ((1 - t) * (((1351 : ℝ) / 4000)) + t * (((821 : ℝ) / 3000))) * Real.log ((1 - t) * (((1351 : ℝ) / 4000)) + t * (((821 : ℝ) / 3000))) ≤ ((-33381278667113579 : ℝ) / 92280000000000000) := by
  rw [integral_mul_log_linear (by norm_num) (by norm_num) (by norm_num)]
  have ha := log_d_ub_7
  have hb := log_d_lb_8
  ring_nf
  linarith

private lemma int_d_rev_7 :
    ∫ t in (0 : ℝ)..1, ((1 - t) * (((821 : ℝ) / 3000)) + t * (((1351 : ℝ) / 4000))) * Real.log ((1 - t) * (((821 : ℝ) / 3000)) + t * (((1351 : ℝ) / 4000))) ≤ ((-33381278667113579 : ℝ) / 92280000000000000) := by
  rw [integral_mul_log_linear (by norm_num) (by norm_num) (by norm_num)]
  have ha := log_d_ub_7
  have hb := log_d_lb_8
  ring_nf
  linarith

private lemma int_d_8 :
    ∫ t in (0 : ℝ)..1, ((1 - t) * (((821 : ℝ) / 3000)) + t * (((553 : ℝ) / 2400))) * Real.log ((1 - t) * (((821 : ℝ) / 3000)) + t * (((553 : ℝ) / 2400))) ≤ ((-337715839227337 : ℝ) / 973125000000000) := by
  rw [integral_mul_log_linear (by norm_num) (by norm_num) (by norm_num)]
  have ha := log_d_ub_8
  have hb := log_d_lb_9
  ring_nf
  linarith

private lemma int_d_rev_8 :
    ∫ t in (0 : ℝ)..1, ((1 - t) * (((553 : ℝ) / 2400)) + t * (((821 : ℝ) / 3000))) * Real.log ((1 - t) * (((553 : ℝ) / 2400)) + t * (((821 : ℝ) / 3000))) ≤ ((-337715839227337 : ℝ) / 973125000000000) := by
  rw [integral_mul_log_linear (by norm_num) (by norm_num) (by norm_num)]
  have ha := log_d_ub_8
  have hb := log_d_lb_9
  ring_nf
  linarith

private lemma int_d_9 :
    ∫ t in (0 : ℝ)..1, ((1 - t) * (((553 : ℝ) / 2400)) + t * (((1201 : ℝ) / 6000))) * Real.log ((1 - t) * (((553 : ℝ) / 2400)) + t * (((1201 : ℝ) / 6000))) ≤ ((-3198824936938881 : ℝ) / 9680000000000000) := by
  rw [integral_mul_log_linear (by norm_num) (by norm_num) (by norm_num)]
  have ha := log_d_ub_9
  have hb := log_d_lb_10
  ring_nf
  linarith

private lemma int_d_rev_9 :
    ∫ t in (0 : ℝ)..1, ((1 - t) * (((1201 : ℝ) / 6000)) + t * (((553 : ℝ) / 2400))) * Real.log ((1 - t) * (((1201 : ℝ) / 6000)) + t * (((553 : ℝ) / 2400))) ≤ ((-3198824936938881 : ℝ) / 9680000000000000) := by
  rw [integral_mul_log_linear (by norm_num) (by norm_num) (by norm_num)]
  have ha := log_d_ub_9
  have hb := log_d_lb_10
  ring_nf
  linarith

private lemma int_d_10 :
    ∫ t in (0 : ℝ)..1, ((1 - t) * (((1201 : ℝ) / 6000)) + t * (((137 : ℝ) / 750))) * Real.log ((1 - t) * (((1201 : ℝ) / 6000)) + t * (((137 : ℝ) / 750))) ≤ ((-159465716548057 : ℝ) / 504000000000000) := by
  rw [integral_mul_log_linear (by norm_num) (by norm_num) (by norm_num)]
  have ha := log_d_ub_10
  have hb := log_d_lb_11
  ring_nf
  linarith

private lemma int_d_rev_10 :
    ∫ t in (0 : ℝ)..1, ((1 - t) * (((137 : ℝ) / 750)) + t * (((1201 : ℝ) / 6000))) * Real.log ((1 - t) * (((137 : ℝ) / 750)) + t * (((1201 : ℝ) / 6000))) ≤ ((-159465716548057 : ℝ) / 504000000000000) := by
  rw [integral_mul_log_linear (by norm_num) (by norm_num) (by norm_num)]
  have ha := log_d_ub_10
  have hb := log_d_lb_11
  ring_nf
  linarith

private lemma int_d_11 :
    ∫ t in (0 : ℝ)..1, ((1 - t) * (((137 : ℝ) / 750)) + t * (((43 : ℝ) / 250))) * Real.log ((1 - t) * (((137 : ℝ) / 750)) + t * (((43 : ℝ) / 250))) ≤ ((-36804703940737 : ℝ) / 120000000000000) := by
  rw [integral_mul_log_linear (by norm_num) (by norm_num) (by norm_num)]
  have ha := log_d_ub_11
  have hb := log_d_lb_12
  ring_nf
  linarith

private lemma int_d_rev_11 :
    ∫ t in (0 : ℝ)..1, ((1 - t) * (((43 : ℝ) / 250)) + t * (((137 : ℝ) / 750))) * Real.log ((1 - t) * (((43 : ℝ) / 250)) + t * (((137 : ℝ) / 750))) ≤ ((-36804703940737 : ℝ) / 120000000000000) := by
  rw [integral_mul_log_linear (by norm_num) (by norm_num) (by norm_num)]
  have ha := log_d_ub_11
  have hb := log_d_lb_12
  ring_nf
  linarith

set_option maxHeartbeats 1200000 in
theorem lower_witness :
    ∃ r ∈ ({r | ∃ N : ℕ, 0 < N ∧ ∃ A : Fin N → Fin N → ℝ, let f := fun x : ℝ ↦ x * Real.log x; let d := fun (b : Bool) (k : ℕ) ↦ 1 - (∑ i : Fin N, ∑ j : Fin N, if i.val + j.val + 1 = k then A i (if b then j.rev else j) else 0) / N; (∀ i j, 0 ≤ A i j) ∧ (∀ i, ∑ j, A i j = N) ∧ (∀ j, ∑ i, A i j = N) ∧ (∀ b (k : Fin (2 * N + 1)), 0 ≤ d b k.val) ∧ r = -3 - (∑ i, ∑ j, f (A i j)) / (N : ℝ) ^ 2 - (∑ b : Bool, ∑ k : Fin (2 * N), ∫ t in (0 : ℝ)..1, f ((1 - t) * d b k.val + t * d b (k.val + 1))) / N} : Set ℝ), -1.9449 < r := by
  let A : Fin 12 → Fin 12 → ℝ := fun i j => ((fun i j : Fin 12 => (![![582, 765, 955, 1127, 1252, 1319], ![765, 861, 993, 1083, 1137, 1161], ![955, 993, 987, 1018, 1024, 1023], ![1127, 1083, 1018, 939, 922, 911], ![1252, 1137, 1024, 922, 839, 826], ![1319, 1161, 1023, 911, 826, 760]] : Fin 6 → Fin 6 → ℕ) ((fun i : Fin 12 => (if h : i.val < 6 then ⟨i.val, h⟩ else ⟨11 - i.val, by omega⟩ : Fin 6)) i) ((fun i : Fin 12 => (if h : i.val < 6 then ⟨i.val, h⟩ else ⟨11 - i.val, by omega⟩ : Fin 6)) j)) i j : ℝ) / 1000
  let f : ℝ → ℝ := fun x => x * Real.log x
  let d : Bool → ℕ → ℝ := fun b k =>
    1 - (∑ i : Fin 12, ∑ j : Fin 12,
      if i.val + j.val + 1 = k then A i (if b then j.rev else j) else 0) / 12
  let r : ℝ := -3 - (∑ i : Fin 12, ∑ j : Fin 12, f (A i j)) / (12 : ℝ) ^ 2 -
    (∑ b : Bool, ∑ k : Fin 24, ∫ t in (0 : ℝ)..1,
      f ((1 - t) * d b k.val + t * d b (k.val + 1))) / 12
  have hd_eq : ∀ (b : Bool) (k : Fin 25), d b k.val = ((![12000, 11418, 10470, 9229, 7760, 6343, 5052, 4053, 3284, 2765, 2402, 2192, 2064, 2192, 2402, 2765, 3284, 4053, 5052, 6343, 7760, 9229, 10470, 11418, 12000] : Fin 25 → ℕ) k : ℝ) / 12000 := by
    intro b k
    dsimp only [d, A]
    have hle := diag_le_nat b k
    have hsum : (∑ i : Fin 12, ∑ j : Fin 12,
        if i.val + j.val + 1 = k.val then (((fun i j : Fin 12 => (![![582, 765, 955, 1127, 1252, 1319], ![765, 861, 993, 1083, 1137, 1161], ![955, 993, 987, 1018, 1024, 1023], ![1127, 1083, 1018, 939, 922, 911], ![1252, 1137, 1024, 922, 839, 826], ![1319, 1161, 1023, 911, 826, 760]] : Fin 6 → Fin 6 → ℕ) ((fun i : Fin 12 => (if h : i.val < 6 then ⟨i.val, h⟩ else ⟨11 - i.val, by omega⟩ : Fin 6)) i) ((fun i : Fin 12 => (if h : i.val < 6 then ⟨i.val, h⟩ else ⟨11 - i.val, by omega⟩ : Fin 6)) j)) i (if b then j.rev else j) : ℝ) / 1000) else 0) =
        ((∑ i : Fin 12, ∑ j : Fin 12,
          if i.val + j.val + 1 = k.val then (fun i j : Fin 12 => (![![582, 765, 955, 1127, 1252, 1319], ![765, 861, 993, 1083, 1137, 1161], ![955, 993, 987, 1018, 1024, 1023], ![1127, 1083, 1018, 939, 922, 911], ![1252, 1137, 1024, 922, 839, 826], ![1319, 1161, 1023, 911, 826, 760]] : Fin 6 → Fin 6 → ℕ) ((fun i : Fin 12 => (if h : i.val < 6 then ⟨i.val, h⟩ else ⟨11 - i.val, by omega⟩ : Fin 6)) i) ((fun i : Fin 12 => (if h : i.val < 6 then ⟨i.val, h⟩ else ⟨11 - i.val, by omega⟩ : Fin 6)) j)) i (if b then j.rev else j) else 0 : ℕ) : ℝ) / 1000 := by
      rw [Nat.cast_sum, Finset.sum_div]
      apply Finset.sum_congr rfl; intro i _
      rw [Nat.cast_sum, Finset.sum_div]
      apply Finset.sum_congr rfl; intro j _
      split_ifs <;> simp
    rw [hsum, div_div, show (1000 : ℝ) * 12 = 12000 by norm_num]
    have hsub : ((![12000, 11418, 10470, 9229, 7760, 6343, 5052, 4053, 3284, 2765, 2402, 2192, 2064, 2192, 2402, 2765, 3284, 4053, 5052, 6343, 7760, 9229, 10470, 11418, 12000] : Fin 25 → ℕ) k : ℝ) = (12000 : ℝ) -
        ((∑ i : Fin 12, ∑ j : Fin 12,
          if i.val + j.val + 1 = k.val then (fun i j : Fin 12 => (![![582, 765, 955, 1127, 1252, 1319], ![765, 861, 993, 1083, 1137, 1161], ![955, 993, 987, 1018, 1024, 1023], ![1127, 1083, 1018, 939, 922, 911], ![1252, 1137, 1024, 922, 839, 826], ![1319, 1161, 1023, 911, 826, 760]] : Fin 6 → Fin 6 → ℕ) ((fun i : Fin 12 => (if h : i.val < 6 then ⟨i.val, h⟩ else ⟨11 - i.val, by omega⟩ : Fin 6)) i) ((fun i : Fin 12 => (if h : i.val < 6 then ⟨i.val, h⟩ else ⟨11 - i.val, by omega⟩ : Fin 6)) j)) i (if b then j.rev else j) else 0 : ℕ) : ℝ) := by
      have hnat := d_nat_eq_table b k
      dsimp only [] at hnat
      rw [← hnat, Nat.cast_sub hle]
      simp only [Nat.cast_ofNat]
    rw [hsub, sub_div, div_self (by norm_num : (12000 : ℝ) ≠ 0)]
  refine ⟨r, ⟨12, by norm_num, A, ?_, ?_, ?_, ?_, rfl⟩, ?_⟩
  · intro i j; dsimp only [A]; positivity
  · intro i
    dsimp only [A]
    rw [← Finset.sum_div]
    have h : (∑ j : Fin 12, ((fun i j : Fin 12 => (![![582, 765, 955, 1127, 1252, 1319], ![765, 861, 993, 1083, 1137, 1161], ![955, 993, 987, 1018, 1024, 1023], ![1127, 1083, 1018, 939, 922, 911], ![1252, 1137, 1024, 922, 839, 826], ![1319, 1161, 1023, 911, 826, 760]] : Fin 6 → Fin 6 → ℕ) ((fun i : Fin 12 => (if h : i.val < 6 then ⟨i.val, h⟩ else ⟨11 - i.val, by omega⟩ : Fin 6)) i) ((fun i : Fin 12 => (if h : i.val < 6 then ⟨i.val, h⟩ else ⟨11 - i.val, by omega⟩ : Fin 6)) j)) i j : ℝ)) = 12000 := by exact_mod_cast row_sum_nat i
    rw [h]; norm_num
  · intro j
    dsimp only [A]
    rw [← Finset.sum_div]
    have h : (∑ i : Fin 12, ((fun i j : Fin 12 => (![![582, 765, 955, 1127, 1252, 1319], ![765, 861, 993, 1083, 1137, 1161], ![955, 993, 987, 1018, 1024, 1023], ![1127, 1083, 1018, 939, 922, 911], ![1252, 1137, 1024, 922, 839, 826], ![1319, 1161, 1023, 911, 826, 760]] : Fin 6 → Fin 6 → ℕ) ((fun i : Fin 12 => (if h : i.val < 6 then ⟨i.val, h⟩ else ⟨11 - i.val, by omega⟩ : Fin 6)) i) ((fun i : Fin 12 => (if h : i.val < 6 then ⟨i.val, h⟩ else ⟨11 - i.val, by omega⟩ : Fin 6)) j)) i j : ℝ)) = 12000 := by exact_mod_cast col_sum_nat j
    rw [h]; norm_num
  · intro b k
    change 0 ≤ d b k.val
    rw [hd_eq b k]; positivity
  ·
    have hsum_int : ∀ b : Bool,
        ∑ k : Fin 24, ∫ t in (0 : ℝ)..1, f ((1 - t) * d b k.val + t * d b (k.val + 1)) ≤ ((-147809600682664895195852314115805512593 : ℝ) / 23051290904263358923414665937500000000) := by
      intro b
      have hterm : ∀ k : Fin 24,
          ∫ t in (0 : ℝ)..1, f ((1 - t) * d b k.val + t * d b (k.val + 1)) ≤
            match k.val with

              | 0 => ((-2889141873829 : ℝ) / 121250000000000)
              | 1 => ((-529036895755227 : ℝ) / 6320000000000000)
              | 2 => ((-12028480828430843 : ℝ) / 74460000000000000)
              | 3 => ((-85908976543236323 : ℝ) / 352560000000000000)
              | 4 => ((-6619382253715963 : ℝ) / 21255000000000000)
              | 5 => ((-109262503707181483 : ℝ) / 309840000000000000)
              | 6 => ((-61095125983937 : ℝ) / 166500000000000)
              | 7 => ((-33381278667113579 : ℝ) / 92280000000000000)
              | 8 => ((-337715839227337 : ℝ) / 973125000000000)
              | 9 => ((-3198824936938881 : ℝ) / 9680000000000000)
              | 10 => ((-159465716548057 : ℝ) / 504000000000000)
              | 11 => ((-36804703940737 : ℝ) / 120000000000000)
              | 23 => ((-2889141873829 : ℝ) / 121250000000000)
              | 22 => ((-529036895755227 : ℝ) / 6320000000000000)
              | 21 => ((-12028480828430843 : ℝ) / 74460000000000000)
              | 20 => ((-85908976543236323 : ℝ) / 352560000000000000)
              | 19 => ((-6619382253715963 : ℝ) / 21255000000000000)
              | 18 => ((-109262503707181483 : ℝ) / 309840000000000000)
              | 17 => ((-61095125983937 : ℝ) / 166500000000000)
              | 16 => ((-33381278667113579 : ℝ) / 92280000000000000)
              | 15 => ((-337715839227337 : ℝ) / 973125000000000)
              | 14 => ((-3198824936938881 : ℝ) / 9680000000000000)
              | 13 => ((-159465716548057 : ℝ) / 504000000000000)
              | 12 => ((-36804703940737 : ℝ) / 120000000000000)
              | _ => 0 := by
        intro k
        have h1 : d b k.val = ((![12000, 11418, 10470, 9229, 7760, 6343, 5052, 4053, 3284, 2765, 2402, 2192, 2064, 2192, 2402, 2765, 3284, 4053, 5052, 6343, 7760, 9229, 10470, 11418, 12000] : Fin 25 → ℕ) ⟨k.val, by omega⟩ : ℝ) / 12000 := hd_eq b ⟨k.val, by omega⟩
        have h2 : d b (k.val + 1) = ((![12000, 11418, 10470, 9229, 7760, 6343, 5052, 4053, 3284, 2765, 2402, 2192, 2064, 2192, 2402, 2765, 3284, 4053, 5052, 6343, 7760, 9229, 10470, 11418, 12000] : Fin 25 → ℕ) ⟨k.val + 1, by omega⟩ : ℝ) / 12000 := hd_eq b ⟨k.val + 1, by omega⟩
        rw [h1, h2]
        dsimp only [f]
        fin_cases k <;> simp only []

        · simpa [show (12000 : ℝ) / 12000 = (1 : ℝ) by norm_num, show (11418 : ℝ) / 12000 = ((1903 : ℝ) / 2000) by norm_num] using int_d_0
        · simpa [show (11418 : ℝ) / 12000 = ((1903 : ℝ) / 2000) by norm_num, show (10470 : ℝ) / 12000 = ((349 : ℝ) / 400) by norm_num] using int_d_1
        · simpa [show (10470 : ℝ) / 12000 = ((349 : ℝ) / 400) by norm_num, show (9229 : ℝ) / 12000 = ((9229 : ℝ) / 12000) by norm_num] using int_d_2
        · simpa [show (9229 : ℝ) / 12000 = ((9229 : ℝ) / 12000) by norm_num, show (7760 : ℝ) / 12000 = ((97 : ℝ) / 150) by norm_num] using int_d_3
        · simpa [show (7760 : ℝ) / 12000 = ((97 : ℝ) / 150) by norm_num, show (6343 : ℝ) / 12000 = ((6343 : ℝ) / 12000) by norm_num] using int_d_4
        · simpa [show (6343 : ℝ) / 12000 = ((6343 : ℝ) / 12000) by norm_num, show (5052 : ℝ) / 12000 = ((421 : ℝ) / 1000) by norm_num] using int_d_5
        · simpa [show (5052 : ℝ) / 12000 = ((421 : ℝ) / 1000) by norm_num, show (4053 : ℝ) / 12000 = ((1351 : ℝ) / 4000) by norm_num] using int_d_6
        · simpa [show (4053 : ℝ) / 12000 = ((1351 : ℝ) / 4000) by norm_num, show (3284 : ℝ) / 12000 = ((821 : ℝ) / 3000) by norm_num] using int_d_7
        · simpa [show (3284 : ℝ) / 12000 = ((821 : ℝ) / 3000) by norm_num, show (2765 : ℝ) / 12000 = ((553 : ℝ) / 2400) by norm_num] using int_d_8
        · simpa [show (2765 : ℝ) / 12000 = ((553 : ℝ) / 2400) by norm_num, show (2402 : ℝ) / 12000 = ((1201 : ℝ) / 6000) by norm_num] using int_d_9
        · simpa [show (2402 : ℝ) / 12000 = ((1201 : ℝ) / 6000) by norm_num, show (2192 : ℝ) / 12000 = ((137 : ℝ) / 750) by norm_num] using int_d_10
        · simpa [show (2192 : ℝ) / 12000 = ((137 : ℝ) / 750) by norm_num, show (2064 : ℝ) / 12000 = ((43 : ℝ) / 250) by norm_num] using int_d_11
        · simpa [show (2064 : ℝ) / 12000 = ((43 : ℝ) / 250) by norm_num, show (2192 : ℝ) / 12000 = ((137 : ℝ) / 750) by norm_num] using int_d_rev_11
        · simpa [show (2192 : ℝ) / 12000 = ((137 : ℝ) / 750) by norm_num, show (2402 : ℝ) / 12000 = ((1201 : ℝ) / 6000) by norm_num] using int_d_rev_10
        · simpa [show (2402 : ℝ) / 12000 = ((1201 : ℝ) / 6000) by norm_num, show (2765 : ℝ) / 12000 = ((553 : ℝ) / 2400) by norm_num] using int_d_rev_9
        · simpa [show (2765 : ℝ) / 12000 = ((553 : ℝ) / 2400) by norm_num, show (3284 : ℝ) / 12000 = ((821 : ℝ) / 3000) by norm_num] using int_d_rev_8
        · simpa [show (3284 : ℝ) / 12000 = ((821 : ℝ) / 3000) by norm_num, show (4053 : ℝ) / 12000 = ((1351 : ℝ) / 4000) by norm_num] using int_d_rev_7
        · simpa [show (4053 : ℝ) / 12000 = ((1351 : ℝ) / 4000) by norm_num, show (5052 : ℝ) / 12000 = ((421 : ℝ) / 1000) by norm_num] using int_d_rev_6
        · simpa [show (5052 : ℝ) / 12000 = ((421 : ℝ) / 1000) by norm_num, show (6343 : ℝ) / 12000 = ((6343 : ℝ) / 12000) by norm_num] using int_d_rev_5
        · simpa [show (6343 : ℝ) / 12000 = ((6343 : ℝ) / 12000) by norm_num, show (7760 : ℝ) / 12000 = ((97 : ℝ) / 150) by norm_num] using int_d_rev_4
        · simpa [show (7760 : ℝ) / 12000 = ((97 : ℝ) / 150) by norm_num, show (9229 : ℝ) / 12000 = ((9229 : ℝ) / 12000) by norm_num] using int_d_rev_3
        · simpa [show (9229 : ℝ) / 12000 = ((9229 : ℝ) / 12000) by norm_num, show (10470 : ℝ) / 12000 = ((349 : ℝ) / 400) by norm_num] using int_d_rev_2
        · simpa [show (10470 : ℝ) / 12000 = ((349 : ℝ) / 400) by norm_num, show (11418 : ℝ) / 12000 = ((1903 : ℝ) / 2000) by norm_num] using int_d_rev_1
        · simpa [show (11418 : ℝ) / 12000 = ((1903 : ℝ) / 2000) by norm_num, show (12000 : ℝ) / 12000 = (1 : ℝ) by norm_num] using int_d_rev_0
      calc ∑ k : Fin 24, ∫ t in (0 : ℝ)..1, f ((1 - t) * d b k.val + t * d b (k.val + 1))
          ≤ ∑ k : Fin 24, match k.val with

              | 0 => ((-2889141873829 : ℝ) / 121250000000000)
              | 1 => ((-529036895755227 : ℝ) / 6320000000000000)
              | 2 => ((-12028480828430843 : ℝ) / 74460000000000000)
              | 3 => ((-85908976543236323 : ℝ) / 352560000000000000)
              | 4 => ((-6619382253715963 : ℝ) / 21255000000000000)
              | 5 => ((-109262503707181483 : ℝ) / 309840000000000000)
              | 6 => ((-61095125983937 : ℝ) / 166500000000000)
              | 7 => ((-33381278667113579 : ℝ) / 92280000000000000)
              | 8 => ((-337715839227337 : ℝ) / 973125000000000)
              | 9 => ((-3198824936938881 : ℝ) / 9680000000000000)
              | 10 => ((-159465716548057 : ℝ) / 504000000000000)
              | 11 => ((-36804703940737 : ℝ) / 120000000000000)
              | 23 => ((-2889141873829 : ℝ) / 121250000000000)
              | 22 => ((-529036895755227 : ℝ) / 6320000000000000)
              | 21 => ((-12028480828430843 : ℝ) / 74460000000000000)
              | 20 => ((-85908976543236323 : ℝ) / 352560000000000000)
              | 19 => ((-6619382253715963 : ℝ) / 21255000000000000)
              | 18 => ((-109262503707181483 : ℝ) / 309840000000000000)
              | 17 => ((-61095125983937 : ℝ) / 166500000000000)
              | 16 => ((-33381278667113579 : ℝ) / 92280000000000000)
              | 15 => ((-337715839227337 : ℝ) / 973125000000000)
              | 14 => ((-3198824936938881 : ℝ) / 9680000000000000)
              | 13 => ((-159465716548057 : ℝ) / 504000000000000)
              | 12 => ((-36804703940737 : ℝ) / 120000000000000)
              | _ => 0 := sum_le_sum fun k _ => hterm k
        _ = ((-147809600682664895195852314115805512593 : ℝ) / 23051290904263358923414665937500000000) := by norm_num [Fin.sum_univ_succ]
    have hA_ub : ∑ i : Fin 12, ∑ j : Fin 12, f (A i j) ≤ ((76019120801 : ℝ) / 39062500000) := sum_A_bound
    have hbool : ∑ b : Bool, ∑ k : Fin 24,
        ∫ t in (0 : ℝ)..1, f ((1 - t) * d b k.val + t * d b (k.val + 1)) ≤ 2 * (((-147809600682664895195852314115805512593 : ℝ) / 23051290904263358923414665937500000000)) := by
      rw [Fintype.sum_bool]
      linarith [hsum_int true, hsum_int false]
    dsimp only [r]
    linarith

end LowerWitness

private lemma glue_aux (S : Set ℝ) (rate : ℕ → ℝ)
    (h1 : ∀ u : ℝ, (∀ t ∈ S, t ≤ u) → ∀ a : ℝ, Real.exp u < a → ∀ᶠ n : ℕ in atTop, rate n < a)
    (h2 : ∀ t ∈ S, ∀ a : ℝ, a < Real.exp t → ∀ᶠ n : ℕ in atTop, a < rate n)
    (hlw : ∃ r ∈ S, -1.9449 < r) (huc : ∃ u : ℝ, u < -1.94 ∧ ∀ r ∈ S, r ≤ u) :
    ∃ α : ℝ, 1.94 < α ∧ α < 1.9449 ∧ Tendsto rate atTop (𝓝 (Real.exp (-α))) := by
  obtain ⟨t0, ht0, hlow⟩ := hlw
  obtain ⟨u0, hu0, hupper⟩ := huc
  have hne : S.Nonempty := ⟨t0, ht0⟩
  have hbdd : BddAbove S := ⟨u0, hupper⟩
  have hs1 : ∀ t ∈ S, t ≤ sSup S := fun t ht => le_csSup hbdd ht
  have hsu : sSup S ≤ u0 := csSup_le hne hupper
  have hts : t0 ≤ sSup S := hs1 t0 ht0
  refine ⟨-sSup S, by linarith, by linarith, ?_⟩
  rw [neg_neg]
  refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => h1 (sSup S) hs1 a ha⟩
  by_cases hapos : 0 < a
  · have hlog : Real.log a < sSup S := by
      rw [Real.log_lt_iff_lt_exp hapos]; exact ha
    obtain ⟨t, ht, hlt⟩ := exists_lt_of_lt_csSup hne hlog
    exact h2 t ht a (by rw [← Real.log_lt_iff_lt_exp hapos]; exact hlt)
  · exact h2 t0 ht0 a (lt_of_le_of_lt (not_lt.mp hapos) (Real.exp_pos t0))

/-- Entropy upper bound (Simkin 2023, Sections 3 and 4): any upper bound u of the
finite-grid entropy scores S bounds the limsup of the queens rate by exp u. -/
def H1 : Prop :=
  let S : Set ℝ := {r | ∃ N : ℕ, 0 < N ∧ ∃ A : Fin N → Fin N → ℝ,
    let f := fun x : ℝ ↦ x * Real.log x
    let d := fun (b : Bool) (k : ℕ) ↦ 1 - (∑ i : Fin N, ∑ j : Fin N,
      if i.val + j.val + 1 = k then A i (if b then j.rev else j) else 0) / N
    (∀ i j, 0 ≤ A i j) ∧ (∀ i, ∑ j, A i j = N) ∧ (∀ j, ∑ i, A i j = N) ∧
    (∀ b (k : Fin (2*N+1)), 0 ≤ d b k.val) ∧ r = -3 - (∑ i, ∑ j, f (A i j)) / (N : ℝ)^2 -
      (∑ b : Bool, ∑ k : Fin (2*N), ∫ t in (0:ℝ)..1,
        f ((1-t) * d b k.val + t * d b (k.val+1))) / N}
  ∀ u : ℝ, (∀ t ∈ S, t ≤ u) → ∀ a : ℝ, Real.exp u < a →
    ∀ᶠ n : ℕ in atTop, (Green97.numQueens n : ℝ) ^ ((1 : ℝ) / n) / n < a

/-- Constructive lower bound (Simkin 2023, Section 5: random greedy plus absorber):
every finite-grid entropy score t bounds the liminf of the queens rate by exp t. -/
def H2 : Prop :=
  let S : Set ℝ := {r | ∃ N : ℕ, 0 < N ∧ ∃ A : Fin N → Fin N → ℝ,
    let f := fun x : ℝ ↦ x * Real.log x
    let d := fun (b : Bool) (k : ℕ) ↦ 1 - (∑ i : Fin N, ∑ j : Fin N,
      if i.val + j.val + 1 = k then A i (if b then j.rev else j) else 0) / N
    (∀ i j, 0 ≤ A i j) ∧ (∀ i, ∑ j, A i j = N) ∧ (∀ j, ∑ i, A i j = N) ∧
    (∀ b (k : Fin (2*N+1)), 0 ≤ d b k.val) ∧ r = -3 - (∑ i, ∑ j, f (A i j)) / (N : ℝ)^2 -
      (∑ b : Bool, ∑ k : Fin (2*N), ∫ t in (0:ℝ)..1,
        f ((1-t) * d b k.val + t * d b (k.val+1))) / N}
  ∀ t ∈ S, ∀ a : ℝ, a < Real.exp t →
    ∀ᶠ n : ℕ in atTop, a < (Green97.numQueens n : ℝ) ^ ((1 : ℝ) / n) / n

theorem main : H1 → H2 → type_of% @Green97.green_97.variants.simkin := by
  intro h1 h2
  exact glue_aux _ _ h1 h2 lower_witness upper_certificate

end OMA.R_Green97_green_97_variants_simkin_R3
