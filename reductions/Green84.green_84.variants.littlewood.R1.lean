import FormalConjectures.GreensOpenProblems.«84»

-- Reduction Green84.green_84.variants.littlewood.R1 of Ben Green's Open Problem 84 — littlewood
-- Credit: @ChadySaba
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Reduction of Littlewood's ultraflat real polynomial conjecture (Green's Problem 84)

Splits the proof into four independent components following the continuous-wave and
defect-sensitive rounding construction:
- `H1`: Real defect-sensitive rounding on `[0, N)` (discrepancy bound).
- `H2`: Signed interval packing on the circle.
- `H3`: Balanced real auxiliary trigonometric polynomial on a higher-dimensional torus.
- `H4`: Continuous ultraflat wave synthesis and gap joining from the packed auxiliary data.

`main` proves the projection, Parseval defect bound, and rounding step.
-/

namespace OMA.R_Green84_green_84_variants_littlewood_R1

open Filter
open scoped ExponentialSum Finset Topology

def H1 : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N → ∀ X : ℕ → ℝ, (∀ k < N, |X k| ≤ 1) →
    ∃ ε : ℕ → ℤ, (∀ k < N, ε k = 1 ∨ ε k = -1) ∧
      let μ := (∑ k ∈ Finset.range N, (1 - |X k|)) / 2
      ∀ θ : ℝ, ‖∑ k ∈ Finset.range N, ((ε k : ℂ) - (X k : ℂ)) * e (k * θ)‖ ≤
        C * (1 + √(μ * Real.log (80 * N / μ)))

def H2 : Prop :=
  ∀ r m : ℕ, 2 ≤ r → ∀ a : Fin r → Fin m → ℤ,
    (∀ i, ∃ k, a i k ≠ 0) →
    (∀ i j, i ≠ j → ∀ t : ℝ, ¬ ∀ k, (a j k : ℝ) = t * (a i k : ℝ)) →
    ∀ w : Fin r → ℝ, (∀ i, 0 < w i) → 2 * ∑ i, w i < 1 →
      ∃ H : ℕ, 1 ≤ H ∧ ∃ θ : Fin H → Fin m → ℝ,
        ∀ e₁ e₂ : Bool, ∀ i j : Fin r, ∀ h s : Fin H, (e₁, i, h) ≠ (e₂, j, s) →
          ∀ q : ℤ, (w i + w j) / (2 * H) <
            |(if e₁ then (1 : ℝ) else -1) * (∑ k, (a i k : ℝ) * θ h k) -
             (if e₂ then (1 : ℝ) else -1) * (∑ k, (a j k : ℝ) * θ s k) - q|

def H3 : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 < δ → δ < 1 / 100 →
    ∃ r m : ℕ, 2 ≤ r ∧ 2 ≤ m ∧ ∃ (a : Fin r → Fin m → ℤ) (c : Fin r → ℂ) (v : Fin m → ℝ),
      (∀ i, ∃ k, a i k ≠ 0) ∧
      (∀ i j, i ≠ j → ∀ t : ℝ, ¬ ∀ k, (a j k : ℝ) = t * (a i k : ℝ)) ∧
      (∀ y : Fin m → ℝ,
        2 * |(∑ i, c i * e (∑ k, (a i k : ℝ) * y k)).re| ≤ 1 + δ) ∧
      (∀ i, 0 < |∑ k, (a i k : ℝ) * v k|) ∧
      1 - C * δ ≤ 2 * ∑ i, |∑ k, (a i k : ℝ) * v k| ∧
      2 * ∑ i, |∑ k, (a i k : ℝ) * v k| < 1 ∧
      ∀ i, 1 ≤ ‖c i‖ / √|∑ k, (a i k : ℝ) * v k| ∧
        ‖c i‖ / √|∑ k, (a i k : ℝ) * v k| ≤ 1 + C * δ

def H4 : Prop :=
  ∀ C₁ : ℝ, 0 < C₁ → ∃ C₂ : ℝ, 0 < C₂ ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧
    ∀ δ : ℝ, 0 < δ → δ < δ₀ →
    ∀ (r m : ℕ) (a : Fin r → Fin m → ℤ) (c : Fin r → ℂ) (v : Fin m → ℝ),
      2 ≤ r → 2 ≤ m →
      (∀ i, ∃ k, a i k ≠ 0) →
      (∀ i j, i ≠ j → ∀ t : ℝ, ¬ ∀ k, (a j k : ℝ) = t * (a i k : ℝ)) →
      (∀ y : Fin m → ℝ, 2 * |(∑ i, c i * e (∑ k, (a i k : ℝ) * y k)).re| ≤ 1 + δ) →
      (∀ i, 0 < |∑ k, (a i k : ℝ) * v k|) →
      1 - C₁ * δ ≤ 2 * ∑ i, |∑ k, (a i k : ℝ) * v k| →
      2 * ∑ i, |∑ k, (a i k : ℝ) * v k| < 1 →
      (∀ i, 1 ≤ ‖c i‖ / √|∑ k, (a i k : ℝ) * v k| ∧
        ‖c i‖ / √|∑ k, (a i k : ℝ) * v k| ≤ 1 + C₁ * δ) →
      ∀ (H : ℕ) (θ : Fin H → Fin m → ℝ), 1 ≤ H →
      (∀ e₁ e₂ : Bool, ∀ i j : Fin r, ∀ h s : Fin H, (e₁, i, h) ≠ (e₂, j, s) →
        ∀ q : ℤ, (|∑ k, (a i k : ℝ) * v k| + |∑ k, (a j k : ℝ) * v k|) / (2 * H) <
          |(if e₁ then (1 : ℝ) else -1) * (∑ k, (a i k : ℝ) * θ h k) -
           (if e₂ then (1 : ℝ) else -1) * (∑ k, (a j k : ℝ) * θ s k) - q|) →
      ∃ N₀ : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ, N₀ ≤ N →
        ∃ (B : ℝ → ℂ) (b : ℤ → ℝ),
          (∀ t : ℝ, 1 ≤ ‖B t‖ ∧ ‖B t‖ ≤ 1 + C₂ * δ) ∧
          (∀ k : ℕ, k < N → √N * |b k| ≤ 1 + C₂ * √δ) ∧
          Summable (fun k : ℤ ↦ |b k|) ∧
          (∀ t : ℝ, HasSum (fun k : ℤ ↦ (b k : ℂ) * e (k * t)) (B t)) ∧
          (∑' k : {k : ℤ // k < 0 ∨ (N : ℤ) ≤ k}, |b k.val|) ≤ K / N

lemma norm_additiveChar (x : ℝ) : ‖e x‖ = 1 := by
  change ‖Complex.exp ((2 * Real.pi * x : ℝ) * Complex.I)‖ = 1
  exact Complex.norm_exp_ofReal_mul_I _

lemma additiveChar_add (x y : ℝ) : e (x + y) = e x * e y := by
  change Complex.exp ((2 * Real.pi * (x + y) : ℝ) * Complex.I) =
    Complex.exp ((2 * Real.pi * x : ℝ) * Complex.I) *
      Complex.exp ((2 * Real.pi * y : ℝ) * Complex.I)
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma additiveChar_mul_conj (x y : ℝ) :
    e x * starRingEnd ℂ (e y) = e (x - y) := by
  change Complex.exp ((2 * Real.pi * x : ℝ) * Complex.I) *
      starRingEnd ℂ (Complex.exp ((2 * Real.pi * y : ℝ) * Complex.I)) =
    Complex.exp ((2 * Real.pi * (x - y) : ℝ) * Complex.I)
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

lemma intervalIntegral_additiveChar_int (n : ℤ) :
    (∫ t in (0 : ℝ)..1, e (n * t)) = if n = 0 then 1 else 0 := by
  split_ifs with hn
  · subst hn
    simp only [Int.cast_zero, zero_mul]
    have he0 : e (0 : ℝ) = 1 := by
      change Complex.exp (((2 * Real.pi * (0 : ℝ) : ℝ) : ℂ) * Complex.I) = 1
      simp
    simp only [he0, intervalIntegral.integral_const, sub_zero, one_smul]
  · let c : ℂ := 2 * Real.pi * (n : ℂ) * Complex.I
    have hc : c ≠ 0 :=
      mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
        (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) (Int.cast_ne_zero.mpr hn)) Complex.I_ne_zero
    have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
        HasDerivAt (fun x : ℝ ↦ Complex.exp (c * (x : ℂ)) / c) (e (n * t)) t := by
      intro t _
      have hl : HasDerivAt (fun x : ℝ ↦ c * (x : ℂ)) c t := by
        simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).const_mul c
      have he : HasDerivAt (fun x : ℝ ↦ Complex.exp (c * (x : ℂ)))
          (Complex.exp (c * (t : ℂ)) * c) t := hl.cexp
      have hd : HasDerivAt (fun x : ℝ ↦ Complex.exp (c * (x : ℂ)) / c)
          (Complex.exp (c * (t : ℂ)) * c / c) t := he.div_const c
      rw [mul_div_cancel_right₀ _ hc] at hd
      have h_eq : Complex.exp (c * (t : ℂ)) = e (n * t) := by
        dsimp [c]
        unfold additiveChar
        congr 1
        push_cast
        ring
      rwa [h_eq] at hd
    have hint : IntervalIntegrable (fun t : ℝ ↦ e (n * t)) MeasureTheory.volume 0 1 := by
      apply Continuous.intervalIntegrable
      unfold additiveChar
      fun_prop
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
    have h1 : Complex.exp (c * ((1 : ℝ) : ℂ)) = 1 := by
      rw [show c * ((1 : ℝ) : ℂ) = (n : ℤ) * (2 * Real.pi * Complex.I) by
        dsimp [c]; ring, Complex.exp_int_mul_two_pi_mul_I]
    have h0 : Complex.exp (c * ((0 : ℝ) : ℂ)) = 1 := by simp
    rw [h1, h0, sub_self]

lemma parseval_fin_range (N : ℕ) (X : ℕ → ℝ) :
    (∫ t in (0 : ℝ)..1, ‖∑ k ∈ Finset.range N, (X k : ℂ) * e (k * t)‖ ^ 2) =
      ∑ k ∈ Finset.range N, (X k) ^ 2 := by
  have hcast : ((∫ t in (0 : ℝ)..1,
      ‖∑ k ∈ Finset.range N, (X k : ℂ) * e (k * t)‖ ^ 2 : ℝ) : ℂ) =
      ∫ t in (0 : ℝ)..1, ((‖∑ k ∈ Finset.range N, (X k : ℂ) * e (k * t)‖ ^ 2 : ℝ) : ℂ) :=
    (intervalIntegral.integral_ofReal).symm
  apply Complex.ofReal_injective
  rw [hcast]
  have hnorm (t : ℝ) :
      ((‖∑ k ∈ Finset.range N, (X k : ℂ) * e (k * t)‖ ^ 2 : ℝ) : ℂ) =
      ∑ j ∈ Finset.range N, ∑ k ∈ Finset.range N,
        ((X j * X k : ℝ) : ℂ) * e ((((j : ℤ) - (k : ℤ) : ℤ) : ℝ) * t) := by
    let S := ∑ k ∈ Finset.range N, (X k : ℂ) * e (k * t)
    have hsq : ((‖S‖ ^ 2 : ℝ) : ℂ) = S * starRingEnd ℂ S := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
    rw [hsq]
    dsimp [S]
    simp only [map_sum, map_mul, Complex.conj_ofReal, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    calc
      (X j : ℂ) * e (j * t) * ((X k : ℂ) * starRingEnd ℂ (e (k * t)))
          = ((X j * X k : ℝ) : ℂ) * (e (j * t) * starRingEnd ℂ (e (k * t))) := by
            push_cast; ring
      _ = ((X j * X k : ℝ) : ℂ) * e ((((j : ℤ) - (k : ℤ) : ℤ) : ℝ) * t) := by
            rw [additiveChar_mul_conj]
            congr 2
            push_cast
            ring
  simp_rw [hnorm]
  rw [intervalIntegral.integral_finsetSum]
  · have hinner (j : ℕ) :
        (∫ t in (0 : ℝ)..1, ∑ k ∈ Finset.range N,
          ((X j * X k : ℝ) : ℂ) * e ((((j : ℤ) - (k : ℤ) : ℤ) : ℝ) * t)) =
        ∑ k ∈ Finset.range N,
          ((X j * X k : ℝ) : ℂ) * ∫ t in (0 : ℝ)..1, e ((((j : ℤ) - (k : ℤ) : ℤ) : ℝ) * t) := by
      rw [intervalIntegral.integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro k _
        exact intervalIntegral.integral_const_mul _ _
      · intro k _
        apply Continuous.intervalIntegrable
        unfold additiveChar
        fun_prop
    simp_rw [hinner, intervalIntegral_additiveChar_int]
    have hdiag (j : ℕ) (hj : j ∈ Finset.range N) :
        (∑ k ∈ Finset.range N,
          ((X j * X k : ℝ) : ℂ) * if (j : ℤ) - (k : ℤ) = 0 then (1 : ℂ) else 0) =
        ((X j ^ 2 : ℝ) : ℂ) := by
      rw [Finset.sum_eq_single j]
      · rw [if_pos (sub_self _), mul_one, pow_two]
      · intro k _ hkj
        have hne : (j : ℤ) - (k : ℤ) ≠ 0 := by omega
        simp [hne]
      · intro hnj
        exact (hnj hj).elim
    rw [Finset.sum_congr rfl (fun j hj ↦ hdiag j hj)]
    push_cast
    rfl
  · intro j _
    apply Continuous.intervalIntegrable
    apply continuous_finsetSum
    intro k _
    unfold additiveChar
    fun_prop

lemma entropy_monotone_bound {q N μ : ℝ} (hq0 : 0 < q) (hq : q ≤ 1 / 2)
    (hN : 0 < N) (hμ0 : 0 ≤ μ) (hμb : μ ≤ q * N) :
    μ * Real.log (80 * N / μ) ≤ q * N * Real.log (80 / q) := by
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at this
    exact this
  have hL : 1 ≤ Real.log (80 / q) := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 4)
      (show 4 ≤ 80 / q by apply (le_div_iff₀ hq0).mpr; linarith)
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow] at hh
    norm_num at hh
    linarith
  by_cases hz : μ = 0
  · rw [hz, zero_mul]
    positivity
  have hμp : 0 < μ := lt_of_le_of_ne hμ0 (Ne.symm hz)
  have hsplit : Real.log (80 * N / μ) = Real.log (80 / q) + Real.log (q * N / μ) := by
    rw [← Real.log_mul (by positivity : 80 / q ≠ 0) (by positivity : q * N / μ ≠ 0)]
    congr 1
    field_simp
  have hs : μ * Real.log (q * N / μ) ≤ q * N - μ := by
    calc
      μ * Real.log (q * N / μ) ≤ μ * (q * N / μ - 1) :=
        mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (by positivity)) hμ0
      _ = q * N - μ := by field_simp
  have hm := mul_le_mul_of_nonneg_right hμb (sub_nonneg.mpr hL)
  rw [hsplit, mul_add]
  nlinarith

lemma small_delta_budget {C_round C₂ δ₀ : ℝ}
    (_hCr : 0 < C_round) (hC₂ : 0 < C₂) (hδ₀ : 0 < δ₀) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ < δ₀ ∧ δ < 1 / 100 ∧
      let S := 1 + C₂ * √δ
      let q := (1 - S⁻¹ ^ 2) / 2 + δ
      let E := C_round * √(q * Real.log (80 / q))
      0 < q ∧ q ≤ 1 / 2 ∧
      (1 + C₂ * δ) / S + E < 1 + ε ∧
      1 - ε < S⁻¹ - E := by
  let S (x : ℝ) : ℝ := 1 + C₂ * √x
  let q (x : ℝ) : ℝ := (1 - (S x)⁻¹ ^ 2) / 2 + x
  let G (x : ℝ) : ℝ := C_round * √(q x * Real.log 80 - q x * Real.log (q x))
  let U (x : ℝ) : ℝ := (1 + C₂ * x) / S x + G x
  let L (x : ℝ) : ℝ := (S x)⁻¹ - G x
  have hS_cont : ContinuousAt S 0 := by
    dsimp [S]
    exact continuousAt_const.add (continuousAt_const.mul Real.continuous_sqrt.continuousAt)
  have hS0 : S 0 = 1 := by simp [S]
  have hq_cont : ContinuousAt q 0 := by
    dsimp [q]
    have hinv : ContinuousAt (fun x ↦ (S x)⁻¹) 0 := hS_cont.inv₀ (by rw [hS0]; norm_num)
    exact ((continuousAt_const.sub (hinv.pow 2)).div_const 2).add continuousAt_id
  have hq0 : q 0 = 0 := by norm_num [q, S]
  have hG_cont : ContinuousAt G 0 := by
    dsimp [G]
    have harg : ContinuousAt (fun y : ℝ ↦ y * Real.log 80 - y * Real.log y) (q 0) := by
      rw [hq0]
      exact (continuousAt_id.mul continuousAt_const).sub Real.continuous_mul_log.continuousAt
    have hcomp : ContinuousAt (fun x : ℝ ↦ q x * Real.log 80 - q x * Real.log (q x)) 0 :=
      ContinuousAt.comp harg hq_cont
    exact continuousAt_const.mul (Real.continuous_sqrt.continuousAt.comp hcomp)
  have hG0 : G 0 = 0 := by simp [G, hq0]
  have hU_cont : ContinuousAt U 0 :=
    ((continuousAt_const.add (continuousAt_const.mul continuousAt_id)).div hS_cont
      (by rw [hS0]; norm_num)).add hG_cont
  have hL_cont : ContinuousAt L 0 :=
    (hS_cont.inv₀ (by rw [hS0]; norm_num)).sub hG_cont
  have hU0 : U 0 = 1 := by simp [U, hS0, hG0]
  have hL0 : L 0 = 1 := by simp [L, hS0, hG0]
  have hev : ∀ᶠ x : ℝ in 𝓝 0, q x < 1 / 2 ∧ U x < 1 + ε ∧ 1 - ε < L x := by
    exact (hq_cont.eventually (gt_mem_nhds (by rw [hq0]; norm_num : q 0 < 1 / 2))).and
      ((hU_cont.eventually (gt_mem_nhds (by rw [hU0]; linarith))).and
        (hL_cont.eventually (lt_mem_nhds (by rw [hL0]; linarith))))
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hev
  let δ := min (r / 2) (min (δ₀ / 2) (1 / 200))
  have hδ : 0 < δ := lt_min (by positivity) (lt_min (by positivity) (by norm_num))
  have hδr : δ < r := (min_le_left _ _).trans_lt (by linarith)
  have hδ_lt_δ₀ : δ < δ₀ := (min_le_right _ _).trans_lt ((min_le_left _ _).trans_lt (by linarith))
  have hδ_100 : δ < 1 / 100 := (min_le_right _ _).trans_lt ((min_le_right _ _).trans_lt (by norm_num))
  have hd : dist δ (0 : ℝ) < r := by
    simpa [Real.dist_eq, abs_of_pos hδ] using hδr
  obtain ⟨hq_half, hU_lt, hL_gt⟩ := hball hd
  have hS1 : 1 < S δ := by
    dsimp [S]
    have : 0 < C₂ * √δ := mul_pos hC₂ (Real.sqrt_pos.mpr hδ)
    linarith
  have hq_pos : 0 < q δ := by
    dsimp [q]
    have hinv1 : (S δ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hS1
    have hinv0 : 0 ≤ (S δ)⁻¹ := (inv_pos.mpr (by linarith)).le
    have hsq : (S δ)⁻¹ ^ 2 < 1 := by nlinarith
    linarith
  have hG_eq : G δ = C_round * √(q δ * Real.log (80 / q δ)) := by
    dsimp [G]
    rw [Real.log_div (by norm_num : (80 : ℝ) ≠ 0) hq_pos.ne', mul_sub]
  refine ⟨δ, hδ, hδ_lt_δ₀, hδ_100, hq_pos, hq_half.le, ?_, ?_⟩
  · simpa only [U, S, q, hG_eq] using hU_lt
  · simpa only [L, S, q, hG_eq] using hL_gt

theorem main : H1 → H2 → H3 → H4 → type_of% @Green84.green_84.variants.littlewood := by
  intro h1 h2 h3 h4 ε hε
  obtain ⟨C_round, hCr, hround⟩ := h1
  obtain ⟨C₁, hC₁, haux⟩ := h3
  obtain ⟨C₂, hC₂, δ₀, hδ₀, hwave⟩ := h4 C₁ hC₁
  obtain ⟨δ, hδ, hδ_lt_δ₀, hδ_100, hq_pos, hq_half, hU_lt, hL_gt⟩ :=
    small_delta_budget hCr hC₂ hδ₀ hε
  let S : ℝ := 1 + C₂ * √δ
  let q : ℝ := (1 - S⁻¹ ^ 2) / 2 + δ
  let E : ℝ := C_round * √(q * Real.log (80 / q))
  have hS : 1 ≤ S := by
    dsimp [S]
    nlinarith [mul_nonneg hC₂.le (Real.sqrt_nonneg δ)]
  have hS_pos : 0 < S := by linarith
  obtain ⟨r, m, hr2, hm2, a, c, v, ha0, hnp, hF, hw_pos, hw_lo, hw_hi, hc⟩ := haux δ hδ hδ_100
  obtain ⟨H, hH1, θ, hpack⟩ := h2 r m hr2 a ha0 hnp
    (fun i ↦ |∑ k, (a i k : ℝ) * v k|) hw_pos hw_hi
  obtain ⟨N₀, K, hK0, hB⟩ := hwave δ hδ hδ_lt_δ₀ r m a c v hr2 hm2 ha0 hnp
    hF hw_pos hw_lo hw_hi hc H θ hH1 hpack
  have hinvN : Tendsto (fun N : ℕ ↦ K / (N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat K
  have hsqrtN : Tendsto (fun N : ℕ ↦ 1 / √(N : ℝ)) atTop (𝓝 0) := by
    exact (tendsto_inv_atTop_zero.comp
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)).congr
      (fun N ↦ (one_div _).symm)
  have hrem_tend : Tendsto (fun N : ℕ ↦ (K / (N : ℝ)) / S + C_round * (1 / √(N : ℝ)))
      atTop (𝓝 0) := by
    simpa using (hinvN.div_const S).add (hsqrtN.const_mul C_round)
  have hq_lim : Tendsto (fun N : ℕ ↦ (1 - ((1 - K / (N : ℝ)) / S) ^ 2) / 2)
      atTop (𝓝 ((1 - S⁻¹ ^ 2) / 2)) := by
    have h1N : Tendsto (fun N : ℕ ↦ (1 - K / (N : ℝ)) / S) atTop (𝓝 (S⁻¹)) := by
      have ht := ((tendsto_const_nhds (x := (1 : ℝ))).sub hinvN).div_const S
      simpa only [sub_zero, one_div] using ht
    exact ((tendsto_const_nhds.sub (h1N.pow 2)).div_const 2)
  have hmargin : 0 < min (1 + ε - ((1 + C₂ * δ) / S + E)) (S⁻¹ - E - (1 - ε)) :=
    lt_min (sub_pos.mpr hU_lt) (sub_pos.mpr hL_gt)
  have hq_gap : (1 - S⁻¹ ^ 2) / 2 < q := by dsimp [q]; linarith
  filter_upwards [eventually_ge_atTop (max N₀ 1),
    hinvN.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
    hq_lim.eventually (gt_mem_nhds hq_gap),
    hrem_tend.eventually (gt_mem_nhds hmargin)] with N hN_ge hK_half hq_ev hrem_ev
  have hN0 : N₀ ≤ N := (le_max_left _ _).trans hN_ge
  have hN1 : 1 ≤ N := (le_max_right _ _).trans hN_ge
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hNs : 0 < √(N : ℝ) := Real.sqrt_pos.mpr hNr
  obtain ⟨B, b, hB_mod, hb_coef, hb_sum, hB_has, hb_tail⟩ := hB N hN0
  let P (t : ℝ) : ℂ := ∑ k ∈ Finset.range N, (b (k : ℤ) : ℂ) * e ((k : ℝ) * t)
  have hB_sub_P (t : ℝ) : ‖B t - P t‖ ≤ K / N := by
    let s : Finset ℤ := Finset.image Int.ofNat (Finset.range N)
    have hmem_s (k : ℤ) : k ∉ s ↔ k < 0 ∨ (N : ℤ) ≤ k := by
      simp only [s, Finset.mem_image, Finset.mem_range, not_exists, not_and]
      constructor
      · intro hk
        by_cases hk0 : 0 ≤ k
        · right
          by_contra hlt
          have hkt : (k.toNat : ℤ) = k := Int.toNat_of_nonneg hk0
          exact hk k.toNat (by omega) hkt
        · left
          omega
      · intro hk m hm hm_eq
        change (m : ℤ) = k at hm_eq
        omega
    have hsum_t : Summable (fun k : ℤ ↦ (b k : ℂ) * e (k * t)) := by
      apply Summable.of_norm
      simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_additiveChar, mul_one]
        using hb_sum
    have hsplit := hsum_t.sum_add_tsum_compl (s := s)
    rw [(hB_has t).tsum_eq] at hsplit
    have hs_eq : ∑ k ∈ s, (b k : ℂ) * e (k * t) = P t := by
      dsimp [s, P]
      rw [Finset.sum_image]
      · apply Finset.sum_congr rfl
        intro k _
        simp
      · intro x _ y _ hxy
        exact Int.ofNat.inj hxy
    rw [hs_eq] at hsplit
    have hdiff : B t - P t = ∑' k : {k : ℤ // k ∉ s}, (b k.val : ℂ) * e (k.val * t) := by
      have h1 : B t - P t = ∑' x : ↑(↑s : Set ℤ)ᶜ, (b x.val : ℂ) * e ((x.val : ℝ) * t) := by
        rw [← hsplit]
        ring
      exact h1
    rw [hdiff]
    have hcompl_sum : Summable (fun k : {k : ℤ // k ∉ s} ↦ |b k.val|) :=
      hb_sum.subtype _
    have hnorm_sum : Summable (fun k : {k : ℤ // k ∉ s} ↦ ‖(b k.val : ℂ) * e (k.val * t)‖) := by
      simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_additiveChar, mul_one]
        using hcompl_sum
    have hle := norm_tsum_le_tsum_norm hnorm_sum
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_additiveChar, mul_one] at hle
    let heqv : {k : ℤ // k ∉ s} ≃ {k : ℤ // k < 0 ∨ (N : ℤ) ≤ k} :=
      Equiv.subtypeEquivRight hmem_s
    have htsum_eq : (∑' k : {k : ℤ // k ∉ s}, |b k.val|) =
        ∑' k : {k : ℤ // k < 0 ∨ (N : ℤ) ≤ k}, |b k.val| :=
      Equiv.tsum_eq heqv (fun k : {k : ℤ // k < 0 ∨ (N : ℤ) ≤ k} ↦ |b k.val|)
    exact hle.trans (htsum_eq ▸ hb_tail)
  let X (k : ℕ) : ℝ := if k < N then √(N : ℝ) / S * b k else 0
  have hX_le (k : ℕ) (hk : k < N) : |X k| ≤ 1 := by
    simp only [X, hk, ↓reduceIte, abs_mul, abs_div, abs_of_pos hNs, abs_of_pos hS_pos]
    rw [div_mul_eq_mul_div]
    exact (div_le_one hS_pos).mpr (hb_coef k hk)
  let UX (t : ℝ) : ℂ := ∑ k ∈ Finset.range N, (X k : ℂ) * e (k * t)
  have hUX_eq (t : ℝ) : UX t = (√(N : ℝ) / S : ℂ) * P t := by
    dsimp [UX, P]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : k < N := Finset.mem_range.mp hk
    simp only [X, hk', ↓reduceIte]
    push_cast
    ring
  have hUX_bounds (t : ℝ) :
      √(N : ℝ) * ((1 - K / N) / S) ≤ ‖UX t‖ ∧
        ‖UX t‖ ≤ √(N : ℝ) * ((1 + C₂ * δ + K / N) / S) := by
    rw [hUX_eq, norm_mul, Complex.norm_div, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hNs, abs_of_pos hS_pos]
    have hP_lo : 1 - K / N ≤ ‖P t‖ := by
      have := norm_sub_norm_le (B t) (P t)
      have h1 := (hB_mod t).1
      have h2 := hB_sub_P t
      linarith
    have hP_hi : ‖P t‖ ≤ 1 + C₂ * δ + K / N := by
      have := norm_sub_norm_le (P t) (B t)
      rw [norm_sub_rev] at this
      have h1 := (hB_mod t).2
      have h2 := hB_sub_P t
      linarith
    constructor
    · calc
        √(N : ℝ) * ((1 - K / N) / S) = (√(N : ℝ) / S) * (1 - K / N) := by ring
        _ ≤ (√(N : ℝ) / S) * ‖P t‖ :=
          mul_le_mul_of_nonneg_left hP_lo (div_nonneg hNs.le hS_pos.le)
    · calc
        (√(N : ℝ) / S) * ‖P t‖ ≤ (√(N : ℝ) / S) * (1 + C₂ * δ + K / N) :=
          mul_le_mul_of_nonneg_left hP_hi (div_nonneg hNs.le hS_pos.le)
        _ = √(N : ℝ) * ((1 + C₂ * δ + K / N) / S) := by ring
  have hParseval : (N : ℝ) * ((1 - K / N) / S) ^ 2 ≤ ∑ k ∈ Finset.range N, (X k) ^ 2 := by
    rw [← parseval_fin_range N X]
    have hint : IntervalIntegrable (fun t : ℝ ↦ ‖UX t‖ ^ 2) MeasureTheory.volume 0 1 := by
      apply Continuous.intervalIntegrable
      have hcont : Continuous UX := by
        apply continuous_finsetSum
        intro k _
        unfold additiveChar
        fun_prop
      exact hcont.norm.pow 2
    have hconst : (N : ℝ) * ((1 - K / N) / S) ^ 2 =
        ∫ _t in (0 : ℝ)..1, (N : ℝ) * ((1 - K / N) / S) ^ 2 := by
      simp
    rw [hconst]
    apply intervalIntegral.integral_mono_on (by norm_num) intervalIntegrable_const hint
    intro t _
    have hlo := (hUX_bounds t).1
    have hpos_lo : 0 ≤ √(N : ℝ) * ((1 - K / N) / S) :=
      mul_nonneg hNs.le (div_nonneg (by linarith) hS_pos.le)
    have hsq := sq_le_sq₀ hpos_lo (norm_nonneg _) |>.mpr hlo
    rw [mul_pow, Real.sq_sqrt hNr.le] at hsq
    exact hsq
  let μ : ℝ := (∑ k ∈ Finset.range N, (1 - |X k|)) / 2
  have hμ0 : 0 ≤ μ := div_nonneg (Finset.sum_nonneg fun k hk ↦
    sub_nonneg.mpr (hX_le k (Finset.mem_range.mp hk))) (by norm_num)
  have hμ_le : μ ≤ q * N := by
    have hsum_le : (∑ k ∈ Finset.range N, (1 - |X k|)) ≤
        ∑ k ∈ Finset.range N, (1 - (X k) ^ 2) := by
      apply Finset.sum_le_sum
      intro k hk
      have hk' := hX_le k (Finset.mem_range.mp hk)
      have hh := mul_nonneg (abs_nonneg (X k)) (sub_nonneg.mpr hk')
      nlinarith only [hh, sq_abs (X k)]
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
      at hsum_le
    have hμ_eq : μ = ((N : ℝ) - ∑ k ∈ Finset.range N, |X k|) / 2 := by
      dsimp [μ]
      simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    have hμ_energy : μ ≤ (N : ℝ) * ((1 - ((1 - K / N) / S) ^ 2) / 2) := by
      nlinarith only [hμ_eq, hsum_le, hParseval]
    exact hμ_energy.trans (by
      rw [mul_comm (N : ℝ) ((1 - ((1 - K / N) / S) ^ 2) / 2)]
      exact mul_le_mul_of_nonneg_right hq_ev.le hNr.le)
  have hentr := entropy_monotone_bound hq_pos hq_half hNr hμ0 hμ_le
  obtain ⟨ε_seq, hε_seq, hε_round⟩ := hround N hN1 X hX_le
  let f : ℕ → ℤ := fun n ↦ if n = 0 then 1 else ε_seq (n - 1)
  refine ⟨f, ?_, ?_⟩
  · intro n hn
    rw [Finset.mem_Icc] at hn
    have hn0 : n ≠ 0 := by omega
    have hn1 : n - 1 < N := by omega
    simpa [f, hn0] using hε_seq (n - 1) hn1
  · intro θ
    have hfourier : Green84.fourierSum N f θ =
        e θ * ∑ k ∈ Finset.range N, (ε_seq k : ℂ) * e (k * θ) := by
      dsimp [Green84.fourierSum]
      rw [Finset.mul_sum]
      have hbi : ∑ n ∈ Finset.Icc 1 N, (f n : ℂ) * e ((n : ℝ) * θ) =
          ∑ k ∈ Finset.range N, (f (k + 1) : ℂ) * e (((k + 1 : ℕ) : ℝ) * θ) := by
        refine Finset.sum_bij (fun n _ ↦ n - 1) ?_ ?_ ?_ ?_
        · intro n hn
          rw [Finset.mem_Icc] at hn
          rw [Finset.mem_range]
          omega
        · intro n₁ hn₁ n₂ hn₂ h
          rw [Finset.mem_Icc] at hn₁ hn₂
          omega
        · intro k hk
          rw [Finset.mem_range] at hk
          refine ⟨k + 1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
        · intro n hn
          rw [Finset.mem_Icc] at hn
          have h1 : n - 1 + 1 = n := by omega
          rw [h1]
      rw [hbi]
      apply Finset.sum_congr rfl
      intro k _
      have hk0 : k + 1 ≠ 0 := Nat.succ_ne_zero k
      simp only [f, hk0, ↓reduceIte, Nat.add_sub_cancel]
      have hadd : e (((k + 1 : ℕ) : ℝ) * θ) = e θ * e ((k : ℝ) * θ) := by
        rw [← additiveChar_add]
        congr 1
        push_cast
        ring
      rw [hadd]
      ring
    have hnorm_eq : ‖Green84.fourierSum N f θ‖ =
        ‖∑ k ∈ Finset.range N, (ε_seq k : ℂ) * e (k * θ)‖ := by
      rw [hfourier, norm_mul, norm_additiveChar, one_mul]
    have hround_err : ‖(∑ k ∈ Finset.range N, (ε_seq k : ℂ) * e (k * θ)) - UX θ‖ ≤
        C_round + E * √(N : ℝ) := by
      have hsub : (∑ k ∈ Finset.range N, (ε_seq k : ℂ) * e (k * θ)) - UX θ =
          ∑ k ∈ Finset.range N, ((ε_seq k : ℂ) - (X k : ℂ)) * e (k * θ) := by
        dsimp [UX]
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro k _
        ring
      rw [hsub]
      refine (hε_round θ).trans ?_
      have hsqrt_le : √(μ * Real.log (80 * (N : ℝ) / μ)) ≤ √(q * Real.log (80 / q)) * √(N : ℝ) := by
        apply (Real.sqrt_le_left (by positivity)).mpr
        rw [mul_pow, Real.sq_sqrt (mul_nonneg hq_pos.le
          (Real.log_nonneg ((le_div_iff₀ hq_pos).mpr (by linarith)))), Real.sq_sqrt hNr.le]
        nlinarith only [hentr]
      have hstep : C_round * (1 + √(μ * Real.log (80 * (N : ℝ) / μ))) ≤
          C_round + E * √(N : ℝ) := by
        have h1 := mul_le_mul_of_nonneg_left
          (by linarith only [hsqrt_le] :
            1 + √(μ * Real.log (80 * (N : ℝ) / μ)) ≤ 1 + √(q * Real.log (80 / q)) * √(N : ℝ))
          hCr.le
        calc
          C_round * (1 + √(μ * Real.log (80 * (N : ℝ) / μ)))
              ≤ C_round * (1 + √(q * Real.log (80 / q)) * √(N : ℝ)) := h1
          _ = C_round + E * √(N : ℝ) := by dsimp [E]; ring
      exact hstep
    have htri1 : ‖Green84.fourierSum N f θ‖ - ‖UX θ‖ ≤ C_round + E * √(N : ℝ) := by
      rw [hnorm_eq]
      exact (norm_sub_norm_le _ _).trans hround_err
    have htri2 : ‖UX θ‖ - ‖Green84.fourierSum N f θ‖ ≤ C_round + E * √(N : ℝ) := by
      rw [hnorm_eq]
      exact ((norm_sub_norm_le _ _).trans (by rw [norm_sub_rev]; exact hround_err))
    have hUX_b := hUX_bounds θ
    have hup_rem : (K / (N : ℝ)) / S + C_round * (1 / √(N : ℝ)) <
        1 + ε - ((1 + C₂ * δ) / S + E) :=
      lt_of_lt_of_le hrem_ev (min_le_left _ _)
    have hlo_rem : (K / (N : ℝ)) / S + C_round * (1 / √(N : ℝ)) <
        S⁻¹ - E - (1 - ε) :=
      lt_of_lt_of_le hrem_ev (min_le_right _ _)
    have hCeq : C_round = (C_round * (1 / √(N : ℝ))) * √(N : ℝ) := by
      field_simp
    have hup : ‖Green84.fourierSum N f θ‖ - √(N : ℝ) ≤ ε * √(N : ℝ) := by
      have h1' : ‖Green84.fourierSum N f θ‖ ≤
          ((1 + C₂ * δ) / S + E + (K / (N : ℝ)) / S + C_round * (1 / √(N : ℝ))) * √(N : ℝ) := by
        have hstep1 : ‖Green84.fourierSum N f θ‖ ≤ ‖UX θ‖ + (C_round + E * √(N : ℝ)) := by
          linarith only [htri1]
        have hstep2 : ‖UX θ‖ + (C_round + E * √(N : ℝ)) ≤
            √(N : ℝ) * ((1 + C₂ * δ + K / (N : ℝ)) / S) +
              ((C_round * (1 / √(N : ℝ))) * √(N : ℝ) + E * √(N : ℝ)) := by
          rw [← hCeq]
          linarith only [hUX_b.2]
        have hstep3 : √(N : ℝ) * ((1 + C₂ * δ + K / (N : ℝ)) / S) +
              ((C_round * (1 / √(N : ℝ))) * √(N : ℝ) + E * √(N : ℝ)) =
            ((1 + C₂ * δ) / S + E + (K / (N : ℝ)) / S + C_round * (1 / √(N : ℝ))) * √(N : ℝ) := by
          ring
        linarith only [hstep1, hstep2, hstep3]
      have h2' : ((1 + C₂ * δ) / S + E + (K / (N : ℝ)) / S + C_round * (1 / √(N : ℝ))) * √(N : ℝ) ≤
          (1 + ε) * √(N : ℝ) :=
        mul_le_mul_of_nonneg_right (by linarith only [hup_rem]) hNs.le
      linarith only [h1', h2']
    have hlo : -(ε * √(N : ℝ)) ≤ ‖Green84.fourierSum N f θ‖ - √(N : ℝ) := by
      have h1' : (S⁻¹ - E - (K / (N : ℝ)) / S - C_round * (1 / √(N : ℝ))) * √(N : ℝ) ≤
          ‖Green84.fourierSum N f θ‖ := by
        have hstep1 : (S⁻¹ - E - (K / (N : ℝ)) / S - C_round * (1 / √(N : ℝ))) * √(N : ℝ) =
            √(N : ℝ) * ((1 - K / (N : ℝ)) / S) -
              ((C_round * (1 / √(N : ℝ))) * √(N : ℝ) + E * √(N : ℝ)) := by
          ring
        have hstep2 : √(N : ℝ) * ((1 - K / (N : ℝ)) / S) -
              ((C_round * (1 / √(N : ℝ))) * √(N : ℝ) + E * √(N : ℝ)) ≤
            ‖UX θ‖ - (C_round + E * √(N : ℝ)) := by
          rw [← hCeq]
          linarith only [hUX_b.1]
        have hstep3 : ‖UX θ‖ - (C_round + E * √(N : ℝ)) ≤ ‖Green84.fourierSum N f θ‖ := by
          linarith only [htri2]
        linarith only [hstep1, hstep2, hstep3]
      have h2' : (1 - ε) * √(N : ℝ) ≤
          (S⁻¹ - E - (K / (N : ℝ)) / S - C_round * (1 / √(N : ℝ))) * √(N : ℝ) :=
        mul_le_mul_of_nonneg_right (by linarith only [hlo_rem]) hNs.le
      linarith only [h1', h2']
    exact abs_le.mpr ⟨hlo, hup⟩

end OMA.R_Green84_green_84_variants_littlewood_R1
