import FormalConjectures.Wikipedia.ChowlaLiouvilleConjecture
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-!
# Reduction of `ChowlaLiouvilleConjecture.chowla_liouville_conjecture.variants.averaged_two_point_uniform`

Following H. Davenport (*On some infinite series involving arithmetical functions II*, Quart. J.
Math. Oxford 8 (1937), 313–320) and K. Matomäki, M. Radziwiłł, and T. Tao (*An averaged form of
Chowla's conjecture*, Algebra & Number Theory 9 (2015), 2167–2196, Theorem 1.1), we reduce the
uniform shift-averaged two-point Chowla theorem across all growing scales `H(N) → ∞`, `H(N) ≤ N`
to two independent classical pillars in analytic number theory:
1. `H1`: **Davenport's uniform exponential-sum bound for the Liouville function** (1937): there
   exists `C > 0` such that for all `N ≥ 2` and all `θ : ℝ`,
   `‖∑ n ∈ Icc 1 N, λ(n) e(n θ)‖ ≤ C * N / (log N)²`.
2. `H2`: **Matomäki–Radziwiłł–Tao small-shift averaged two-point Chowla bound** (2015): for every
   `ε > 0`, there exist `H₀, N₀` such that for all `N ≥ N₀` and all `H` with `H₀ ≤ H` and
   `H ≤ N / log N`, the shift-averaged two-point correlation over `1 ≤ h ≤ H` is strictly less
   than `ε`.

Inside `main`, we prove from scratch:
- Orthogonality of characters `θ ↦ exp(2πi k θ)` on `[0, 1]` via the Fundamental Theorem of
  Calculus (`intervalIntegral.integral_eq_sub_of_hasDerivAt`).
- Parseval's identity for arbitrary finite real-coefficient trigonometric polynomials on `[0, 1]`.
- Convolution-square extraction:
  `∑ h ∈ Icc 1 H, (∑ n ∈ Icc 1 N, λ(n) λ(n + h))² ≤ ∫_0^1 ‖S₁(θ)‖² ‖S₂(θ)‖² dθ`.
- Cauchy–Schwarz (`Finset.sq_sum_le_card_mul_sum_sq`) combined with `H1` and Parseval on `S₂`
  yielding the large-shift bound `A(N, H)² ≤ 2 C² / (log N)³` whenever `N / log N < H ≤ N`.
- Regime splitting between `H(N) ≤ N / log N` (handled by `H2`) and `N / log N < H(N) ≤ N`
  (handled by `H1` + Parseval), establishing `Tendsto ... atTop (nhds 0)`.

Credit: @tkaiman
-/

namespace OMA.R_ChowlaLiouvilleConjecture_chowla_liouville_conjecture_variants_averaged_two_point_uniform_R1

open Filter Finset MeasureTheory Real
open scoped BigOperators Topology

private noncomputable def eChar (k : ℤ) (θ : ℝ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * (θ : ℂ))

private lemma eChar_continuous (k : ℤ) : Continuous (eChar k) := by
  unfold eChar
  fun_prop

private lemma eChar_conj (k : ℤ) (θ : ℝ) : starRingEnd ℂ (eChar k θ) = eChar (-k) θ := by
  unfold eChar
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat, map_intCast, Int.cast_neg]
  ring

private lemma eChar_mul (k l : ℤ) (θ : ℝ) : eChar k θ * eChar l θ = eChar (k + l) θ := by
  unfold eChar
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private lemma eChar_neg_arg (k : ℤ) (θ : ℝ) : eChar (-k) θ = eChar k (-θ) := by
  unfold eChar
  congr 1
  push_cast
  ring

private lemma integral_eChar (k : ℤ) :
    ∫ θ in (0 : ℝ)..1, eChar k θ = if k = 0 then (1 : ℂ) else 0 := by
  by_cases hk : k = 0
  · subst hk
    simp [eChar]
  · rw [if_neg hk]
    let c : ℂ := 2 * Real.pi * Complex.I * (k : ℂ)
    have hc : c ≠ 0 := by
      dsimp [c]
      refine mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero ?_) Complex.I_ne_zero) ?_
      · exact Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
      · exact Int.cast_ne_zero.mpr hk
    let F : ℝ → ℂ := fun θ => Complex.exp (c * (θ : ℂ)) / c
    have hderiv : ∀ θ ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt F (eChar k θ) θ := by
      intro θ _
      have h1 : HasDerivAt (fun t : ℝ => c * (t : ℂ)) c θ := by
        simpa using (Complex.ofRealCLM.hasDerivAt (x := θ)).const_mul c
      have h2 : HasDerivAt (fun t : ℝ => Complex.exp (c * (t : ℂ)))
          (Complex.exp (c * (θ : ℂ)) * c) θ := h1.cexp
      have h3 : HasDerivAt F (Complex.exp (c * (θ : ℂ)) * c / c) θ := h2.div_const c
      rwa [mul_div_cancel_right₀ _ hc] at h3
    have hint : IntervalIntegrable (eChar k) volume 0 1 :=
      (eChar_continuous k).intervalIntegrable 0 1
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
    have h1 : Complex.exp c = 1 := by
      have heq : c = (k : ℂ) * (2 * Real.pi * Complex.I) := by dsimp [c]; ring
      rw [heq]
      exact Complex.exp_int_mul_two_pi_mul_I k
    simp [F, h1]

private lemma parseval_trig (S : Finset ℤ) (a : ℤ → ℝ) :
    ∫ θ in (0 : ℝ)..1, ‖∑ k ∈ S, (a k : ℂ) * eChar k θ‖ ^ 2 = ∑ k ∈ S, (a k) ^ 2 := by
  have hC : ((∫ θ in (0 : ℝ)..1, ‖∑ k ∈ S, (a k : ℂ) * eChar k θ‖ ^ 2 : ℝ) : ℂ) =
      ((∑ k ∈ S, (a k) ^ 2 : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    have hpoint : ∀ θ : ℝ,
        ((‖∑ k ∈ S, (a k : ℂ) * eChar k θ‖ ^ 2 : ℝ) : ℂ) =
          ∑ k ∈ S, ∑ l ∈ S, ((a k * a l : ℝ) : ℂ) * eChar (k - l) θ := by
      intro θ
      set z : ℂ := ∑ k ∈ S, (a k : ℂ) * eChar k θ
      have hnz : ((‖z‖ ^ 2 : ℝ) : ℂ) = z * starRingEnd ℂ z := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
      rw [hnz]
      dsimp [z]
      rw [map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [map_mul, Complex.conj_ofReal, eChar_conj]
      have hmul : (a k : ℂ) * eChar k θ * ((a l : ℂ) * eChar (-l) θ) =
          ((a k * a l : ℝ) : ℂ) * (eChar k θ * eChar (-l) θ) := by
        push_cast; ring
      rw [hmul, eChar_mul, ← sub_eq_add_neg]
    simp_rw [hpoint]
    rw [intervalIntegral.integral_finsetSum]
    · have hinner : ∀ k ∈ S,
          ∫ θ in (0 : ℝ)..1, ∑ l ∈ S, ((a k * a l : ℝ) : ℂ) * eChar (k - l) θ =
            ((a k ^ 2 : ℝ) : ℂ) := by
        intro k hk
        rw [intervalIntegral.integral_finsetSum]
        · have hterm : ∀ l ∈ S,
              ∫ θ in (0 : ℝ)..1, ((a k * a l : ℝ) : ℂ) * eChar (k - l) θ =
                if l = k then ((a k ^ 2 : ℝ) : ℂ) else 0 := by
            intro l _
            rw [intervalIntegral.integral_const_mul, integral_eChar]
            by_cases hlk : l = k
            · subst hlk
              simp [sq]
            · have hne : k - l ≠ 0 := sub_ne_zero.mpr (Ne.symm hlk)
              simp [hlk, hne]
          rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' S k, if_pos hk]
        · intro l _
          exact ((continuous_const.mul (eChar_continuous (k - l)))).intervalIntegrable 0 1
      rw [Finset.sum_congr rfl hinner]
      push_cast
      rfl
    · intro k _
      refine (continuous_finsetSum S fun l _ =>
        continuous_const.mul (eChar_continuous (k - l))).intervalIntegrable 0 1
  exact Complex.ofReal_inj.mp hC

private lemma liouville_sq_eq_one {n : ℕ} (hn : n ≠ 0) :
    ((ArithmeticFunction.liouville n : ℝ)) ^ 2 = 1 := by
  rw [ArithmeticFunction.liouville_apply hn]
  push_cast
  rw [← pow_mul, mul_comm, pow_mul]
  norm_num

/-- **Davenport's (1937) uniform exponential-sum bound for the Liouville function**:
there exists `C > 0` such that for all `N ≥ 2` and all `θ : ℝ`,
`‖∑ n ∈ Icc 1 N, λ(n) * exp(2πi n θ)‖ ≤ C * N / (log N)²`. -/
def H1 : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (N : ℕ), 2 ≤ N → ∀ θ : ℝ,
      ‖∑ n ∈ Finset.Icc 1 N,
        (ArithmeticFunction.liouville n : ℂ) *
          Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * (θ : ℂ))‖ ≤
        C * (N : ℝ) / (Real.log (N : ℝ)) ^ 2

/-- **Matomäki–Radziwiłł–Tao (2015, Theorem 1.1) small-shift averaged two-point Chowla bound**:
for every `ε > 0`, there exist `H₀, N₀` such that for all `N ≥ N₀` and all `H` with `H₀ ≤ H` and
`(H : ℝ) ≤ N / log N`, the shift average over `1 ≤ h ≤ H` of
`|(1 / N) ∑ n ∈ Icc 1 N, λ(n) λ(n + h)|` is strictly less than `ε`. -/
def H2 : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ H₀ N₀ : ℕ, ∀ (N H : ℕ), N₀ ≤ N → H₀ ≤ H → (H : ℝ) ≤ (N : ℝ) / Real.log (N : ℝ) →
      (∑ h ∈ Finset.Icc 1 H,
        |∑ n ∈ Finset.Icc 1 N,
          (ArithmeticFunction.liouville n * ArithmeticFunction.liouville (n + h) : ℝ)| /
            (N : ℝ)) / (H : ℝ) < ε

theorem main :
    H1 → H2 →
      type_of% @ChowlaLiouvilleConjecture.chowla_liouville_conjecture.variants.averaged_two_point_uniform := by
  intro h1 h2 H hH_top hH_le
  obtain ⟨C, hCpos, hDav⟩ := h1
  -- Step 1: Parseval + Cauchy–Schwarz + Davenport bound for all N ≥ 2, 1 ≤ H₀ ≤ N
  have hlarge : ∀ (N M : ℕ), 2 ≤ N → 1 ≤ M → M ≤ N →
      ((∑ h ∈ Finset.Icc 1 M,
        |∑ n ∈ Finset.Icc 1 N,
          (ArithmeticFunction.liouville n * ArithmeticFunction.liouville (n + h) : ℝ)| /
            (N : ℝ)) / (M : ℝ)) ^ 2 ≤
        (C / (Real.log (N : ℝ)) ^ 2) ^ 2 * (((N : ℝ) + (M : ℝ)) / (M : ℝ)) := by
    intro N M hN2 hM1 hMN
    let lam : ℕ → ℝ := fun n => (ArithmeticFunction.liouville n : ℝ)
    let c : ℕ → ℝ := fun h => ∑ n ∈ Finset.Icc 1 N, lam n * lam (n + h)
    have hNpos : (0 : ℝ) < (N : ℝ) := by positivity
    have hMpos : (0 : ℝ) < (M : ℝ) := by positivity
    -- Cauchy–Schwarz on `Icc 1 M`
    have hCS : (∑ h ∈ Finset.Icc 1 M, |c h| / (N : ℝ)) ^ 2 ≤
        (M : ℝ) * ∑ h ∈ Finset.Icc 1 M, (|c h| / (N : ℝ)) ^ 2 := by
      have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.Icc 1 M)
        (fun _ => (1 : ℝ)) (fun h => |c h| / (N : ℝ))
      simpa [Nat.card_Icc] using h
    -- Build trigonometric polynomials `S₁` and `S₂`
    let S₁ : ℝ → ℂ := fun θ => ∑ n ∈ Finset.Icc 1 N, (lam n : ℂ) * eChar (-(n : ℤ)) θ
    let S₂ : ℝ → ℂ := fun θ => ∑ m ∈ Finset.Icc 1 (N + M), (lam m : ℂ) * eChar (m : ℤ) θ
    let K : Finset ℤ := Finset.Icc (1 - (N : ℤ)) ((N + M : ℕ) : ℤ)
    let d : ℤ → ℝ := fun k =>
      ∑ n ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 (N + M),
        if (m : ℤ) - (n : ℤ) = k then lam n * lam m else 0
    have hprod : ∀ θ : ℝ, S₁ θ * S₂ θ = ∑ k ∈ K, (d k : ℂ) * eChar k θ := by
      intro θ
      dsimp [S₁, S₂]
      rw [Finset.sum_mul]
      have hexp : ∑ n ∈ Finset.Icc 1 N, (lam n : ℂ) * eChar (-(n : ℤ)) θ *
          ∑ m ∈ Finset.Icc 1 (N + M), (lam m : ℂ) * eChar (m : ℤ) θ =
          ∑ n ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 (N + M),
            ((lam n * lam m : ℝ) : ℂ) * eChar ((m : ℤ) - (n : ℤ)) θ := by
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun m _ => ?_
        have hm : (lam n : ℂ) * eChar (-(n : ℤ)) θ * ((lam m : ℂ) * eChar (m : ℤ) θ) =
            ((lam n * lam m : ℝ) : ℂ) * (eChar (-(n : ℤ)) θ * eChar (m : ℤ) θ) := by
          push_cast; ring
        rw [hm, eChar_mul, neg_add_eq_sub]
      rw [hexp]
      have hgroup : ∑ k ∈ K, (d k : ℂ) * eChar k θ =
          ∑ n ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 (N + M),
            ∑ k ∈ K, (if (m : ℤ) - (n : ℤ) = k then ((lam n * lam m : ℝ) : ℂ) * eChar k θ else 0) := by
        calc ∑ k ∈ K, (d k : ℂ) * eChar k θ
            = ∑ k ∈ K, ∑ n ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 (N + M),
                (if (m : ℤ) - (n : ℤ) = k then ((lam n * lam m : ℝ) : ℂ) * eChar k θ else 0) := by
                  refine Finset.sum_congr rfl fun k _ => ?_
                  dsimp [d]
                  push_cast
                  rw [Finset.sum_mul]
                  refine Finset.sum_congr rfl fun n _ => ?_
                  rw [Finset.sum_mul]
                  refine Finset.sum_congr rfl fun m _ => ?_
                  split_ifs <;> simp
          _ = ∑ n ∈ Finset.Icc 1 N, ∑ k ∈ K, ∑ m ∈ Finset.Icc 1 (N + M),
                (if (m : ℤ) - (n : ℤ) = k then ((lam n * lam m : ℝ) : ℂ) * eChar k θ else 0) :=
                Finset.sum_comm
          _ = ∑ n ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 (N + M), ∑ k ∈ K,
                (if (m : ℤ) - (n : ℤ) = k then ((lam n * lam m : ℝ) : ℂ) * eChar k θ else 0) := by
                refine Finset.sum_congr rfl fun n _ => Finset.sum_comm
      rw [hgroup]
      refine Finset.sum_congr rfl fun n hn => Finset.sum_congr rfl fun m hm => ?_
      rw [Finset.mem_Icc] at hn hm
      have hmemK : (m : ℤ) - (n : ℤ) ∈ K := by
        rw [Finset.mem_Icc]
        omega
      rw [Finset.sum_ite_eq K ((m : ℤ) - (n : ℤ)), if_pos hmemK]
    -- Identify `d (h : ℤ) = c h` for `h ∈ Icc 1 M`
    have hd_eq : ∀ h ∈ Finset.Icc 1 M, d (h : ℤ) = c h := by
      intro h hh
      rw [Finset.mem_Icc] at hh
      dsimp [d, c]
      refine Finset.sum_congr rfl fun n hn => ?_
      rw [Finset.mem_Icc] at hn
      have hmem : n + h ∈ Finset.Icc 1 (N + M) := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      have hcond : ∀ m ∈ Finset.Icc 1 (N + M),
          (if (m : ℤ) - (n : ℤ) = (h : ℤ) then lam n * lam m else 0) =
            if m = n + h then lam n * lam m else 0 := by
        intro m _
        have hiff : ((m : ℤ) - (n : ℤ) = (h : ℤ)) ↔ m = n + h := by omega
        simp [hiff]
      rw [Finset.sum_congr rfl hcond, Finset.sum_ite_eq' (Finset.Icc 1 (N + M)) (n + h),
        if_pos hmem]
    -- Parseval on `S₁ * S₂`
    have hsum_c_le : ∑ h ∈ Finset.Icc 1 M, (c h) ^ 2 ≤
        ∫ θ in (0 : ℝ)..1, ‖S₁ θ‖ ^ 2 * ‖S₂ θ‖ ^ 2 := by
      have hsub : Finset.image (fun h : ℕ => (h : ℤ)) (Finset.Icc 1 M) ⊆ K := by
        intro k hk
        obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hk
        rw [Finset.mem_Icc] at hh ⊢
        omega
      have h1 : ∑ h ∈ Finset.Icc 1 M, (c h) ^ 2 ≤ ∑ k ∈ K, (d k) ^ 2 := by
        have himg : ∑ h ∈ Finset.Icc 1 M, (c h) ^ 2 =
            ∑ k ∈ (Finset.Icc 1 M).image (fun h : ℕ => (h : ℤ)), (d k) ^ 2 := by
          rw [Finset.sum_image (by intro x _ y _ hxy; exact Int.ofNat.inj hxy)]
          refine Finset.sum_congr rfl fun h hh => by rw [hd_eq h hh]
        rw [himg]
        exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => sq_nonneg _
      have h2 : ∑ k ∈ K, (d k) ^ 2 = ∫ θ in (0 : ℝ)..1, ‖S₁ θ * S₂ θ‖ ^ 2 := by
        rw [← parseval_trig K d]
        refine intervalIntegral.integral_congr fun θ _ => ?_
        rw [hprod θ]
      have h3 : ∫ θ in (0 : ℝ)..1, ‖S₁ θ * S₂ θ‖ ^ 2 =
          ∫ θ in (0 : ℝ)..1, ‖S₁ θ‖ ^ 2 * ‖S₂ θ‖ ^ 2 := by
        refine intervalIntegral.integral_congr fun θ _ => ?_
        rw [norm_mul, mul_pow]
      linarith
    -- Parseval on `S₂`
    have hS2_int : ∫ θ in (0 : ℝ)..1, ‖S₂ θ‖ ^ 2 = ((N + M : ℕ) : ℝ) := by
      let S₂_set : Finset ℤ := (Finset.Icc 1 (N + M)).image (fun m : ℕ => (m : ℤ))
      let a₂ : ℤ → ℝ := fun k => lam k.toNat
      have hS2_eq : ∀ θ : ℝ, S₂ θ = ∑ k ∈ S₂_set, (a₂ k : ℂ) * eChar k θ := by
        intro θ
        dsimp [S₂, S₂_set, a₂]
        rw [Finset.sum_image (by intro x _ y _ hxy; exact Int.ofNat.inj hxy)]
        refine Finset.sum_congr rfl fun m _ => by simp
      simp_rw [hS2_eq]
      rw [parseval_trig S₂_set a₂]
      dsimp [S₂_set, a₂]
      rw [Finset.sum_image (by intro x _ y _ hxy; exact Int.ofNat.inj hxy)]
      have hone : ∀ m ∈ Finset.Icc 1 (N + M), (lam (Int.toNat (m : ℤ))) ^ 2 = (1 : ℝ) := by
        intro m hm
        rw [Finset.mem_Icc] at hm
        simpa [lam] using liouville_sq_eq_one (by omega : m ≠ 0)
      rw [Finset.sum_congr rfl hone, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, mul_one]
      have : N + M + 1 - 1 = N + M := by omega
      rw [this]
    -- Pointwise Davenport bound on `S₁ θ`
    have hS1_bound : ∀ θ : ℝ, ‖S₁ θ‖ ≤ C * (N : ℝ) / (Real.log (N : ℝ)) ^ 2 := by
      intro θ
      have hS1_eq : S₁ θ = ∑ n ∈ Finset.Icc 1 N,
          (ArithmeticFunction.liouville n : ℂ) *
            Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * ((-θ : ℝ) : ℂ)) := by
        dsimp [S₁, lam]
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [eChar_neg_arg]
        rfl
      rw [hS1_eq]
      exact hDav N hN2 (-θ)
    have hcont_S1 : Continuous (fun θ : ℝ => ‖S₁ θ‖ ^ 2) := by
      have h1 : Continuous S₁ := continuous_finsetSum _ fun n _ =>
        continuous_const.mul (eChar_continuous (-(n : ℤ)))
      exact (continuous_norm.comp h1).pow 2
    have hcont_S2 : Continuous (fun θ : ℝ => ‖S₂ θ‖ ^ 2) := by
      have h2 : Continuous S₂ := continuous_finsetSum _ fun m _ =>
        continuous_const.mul (eChar_continuous (m : ℤ))
      exact (continuous_norm.comp h2).pow 2
    have hint_bound : ∫ θ in (0 : ℝ)..1, ‖S₁ θ‖ ^ 2 * ‖S₂ θ‖ ^ 2 ≤
        (C * (N : ℝ) / (Real.log (N : ℝ)) ^ 2) ^ 2 * ((N + M : ℕ) : ℝ) := by
      rw [← hS2_int, ← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_mono_on (by norm_num)
        ((hcont_S1.mul hcont_S2).intervalIntegrable 0 1)
        ((continuous_const.mul hcont_S2).intervalIntegrable 0 1) fun θ _ => ?_
      have hb : ‖S₁ θ‖ ^ 2 ≤ (C * (N : ℝ) / (Real.log (N : ℝ)) ^ 2) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (hS1_bound θ) 2
      exact mul_le_mul_of_nonneg_right hb (sq_nonneg _)
    -- Assemble Cauchy–Schwarz + Parseval + Davenport
    have hsum_sq : ∑ h ∈ Finset.Icc 1 M, (c h) ^ 2 ≤
        (C * (N : ℝ) / (Real.log (N : ℝ)) ^ 2) ^ 2 * ((N : ℝ) + (M : ℝ)) := by
      have hcast : ((N + M : ℕ) : ℝ) = (N : ℝ) + (M : ℝ) := by push_cast; rfl
      rw [hcast] at hint_bound
      exact hsum_c_le.trans hint_bound
    have hdiv_sq : ∑ h ∈ Finset.Icc 1 M, (|c h| / (N : ℝ)) ^ 2 =
        (∑ h ∈ Finset.Icc 1 M, (c h) ^ 2) / (N : ℝ) ^ 2 := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun h _ => ?_
      rw [div_pow, sq_abs]
    have hLHS_le : ((∑ h ∈ Finset.Icc 1 M, |c h| / (N : ℝ)) / (M : ℝ)) ^ 2 ≤
        (∑ h ∈ Finset.Icc 1 M, (c h) ^ 2) / ((M : ℝ) * (N : ℝ) ^ 2) := by
      rw [div_pow, div_le_div_iff₀ (pow_pos hMpos 2) (by positivity)]
      have hCS' : (∑ h ∈ Finset.Icc 1 M, |c h| / (N : ℝ)) ^ 2 * (N : ℝ) ^ 2 ≤
          (M : ℝ) * ∑ h ∈ Finset.Icc 1 M, (c h) ^ 2 := by
        rw [hdiv_sq] at hCS
        have := mul_le_mul_of_nonneg_right hCS (sq_nonneg (N : ℝ))
        have hne : (N : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 hNpos.ne'
        calc (∑ h ∈ Finset.Icc 1 M, |c h| / (N : ℝ)) ^ 2 * (N : ℝ) ^ 2
            ≤ (M : ℝ) * ((∑ h ∈ Finset.Icc 1 M, (c h) ^ 2) / (N : ℝ) ^ 2) * (N : ℝ) ^ 2 := this
          _ = (M : ℝ) * ∑ h ∈ Finset.Icc 1 M, (c h) ^ 2 := by field_simp [hne]
      nlinarith
    have hRHS_eq : (C * (N : ℝ) / (Real.log (N : ℝ)) ^ 2) ^ 2 * ((N : ℝ) + (M : ℝ)) /
        ((M : ℝ) * (N : ℝ) ^ 2) =
        (C / (Real.log (N : ℝ)) ^ 2) ^ 2 * (((N : ℝ) + (M : ℝ)) / (M : ℝ)) := by
      have hne : (N : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 hNpos.ne'
      have hMne : (M : ℝ) ≠ 0 := hMpos.ne'
      field_simp [hne, hMne]
    calc ((∑ h ∈ Finset.Icc 1 M, |c h| / (N : ℝ)) / (M : ℝ)) ^ 2
        ≤ (∑ h ∈ Finset.Icc 1 M, (c h) ^ 2) / ((M : ℝ) * (N : ℝ) ^ 2) := hLHS_le
      _ ≤ (C * (N : ℝ) / (Real.log (N : ℝ)) ^ 2) ^ 2 * ((N : ℝ) + (M : ℝ)) /
            ((M : ℝ) * (N : ℝ) ^ 2) :=
          div_le_div_of_nonneg_right hsum_sq (by positivity)
      _ = (C / (Real.log (N : ℝ)) ^ 2) ^ 2 * (((N : ℝ) + (M : ℝ)) / (M : ℝ)) := hRHS_eq
  -- Step 2: Combine `H2` (when `H N ≤ N / log N`) and `hlarge` (when `N / log N < H N ≤ N`)
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨H₀, N₀, hSmall⟩ := h2 ε hε
  have hevH : ∀ᶠ N in Filter.atTop, max H₀ 1 ≤ H N :=
    hH_top.eventually (Filter.eventually_ge_atTop (max H₀ 1))
  have hlog_top : Tendsto (fun N : ℕ => Real.log (N : ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hevLog : ∀ᶠ N : ℕ in Filter.atTop, max 2 (2 * C ^ 2 / ε ^ 2 + 1) ≤ Real.log (N : ℝ) :=
    hlog_top.eventually (Filter.eventually_ge_atTop _)
  have hevAll : ∀ᶠ N : ℕ in Filter.atTop,
      max N₀ 2 ≤ N ∧ max H₀ 1 ≤ H N ∧ H N ≤ N ∧
        max 2 (2 * C ^ 2 / ε ^ 2 + 1) ≤ Real.log (N : ℝ) := by
    filter_upwards [Filter.eventually_ge_atTop (max N₀ 2), hevH, hH_le, hevLog] with N h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  rw [Filter.eventually_atTop] at hevAll
  obtain ⟨N₁, hN₁⟩ := hevAll
  refine ⟨N₁, fun N hN => ?_⟩
  obtain ⟨hN_ge, hH_ge, hHN, hlog_ge⟩ := hN₁ N hN
  have hN_N0 : N₀ ≤ N := le_trans (le_max_left _ _) hN_ge
  have hN_2 : 2 ≤ N := le_trans (le_max_right _ _) hN_ge
  have hH_H0 : H₀ ≤ H N := le_trans (le_max_left _ _) hH_ge
  have hH_1 : 1 ≤ H N := le_trans (le_max_right _ _) hH_ge
  have hlog2 : (2 : ℝ) ≤ Real.log (N : ℝ) := le_trans (le_max_left _ _) hlog_ge
  have hlog_big : 2 * C ^ 2 / ε ^ 2 + 1 ≤ Real.log (N : ℝ) := le_trans (le_max_right _ _) hlog_ge
  have hlog_pos : 0 < Real.log (N : ℝ) := by linarith
  set val : ℝ :=
    (∑ h ∈ Finset.Icc 1 (H N),
      |∑ n ∈ Finset.Icc 1 N,
        (ArithmeticFunction.liouville n * ArithmeticFunction.liouville (n + h) : ℝ)| /
          (N : ℝ)) / (H N : ℝ)
  have hval_nn : 0 ≤ val := by
    dsimp [val]
    refine div_nonneg (Finset.sum_nonneg fun h _ => div_nonneg (abs_nonneg _) (Nat.cast_nonneg _))
      (Nat.cast_nonneg _)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hval_nn]
  by_cases hreg : (H N : ℝ) ≤ (N : ℝ) / Real.log (N : ℝ)
  · exact hSmall N (H N) hN_N0 hH_H0 hreg
  · push Not at hreg
    have hsq := hlarge N (H N) hN_2 hH_1 hHN
    have hHpos : (0 : ℝ) < (H N : ℝ) := by positivity
    have hratio : ((N : ℝ) + (H N : ℝ)) / (H N : ℝ) ≤ 2 * Real.log (N : ℝ) := by
      have h1 : (N : ℝ) / (H N : ℝ) ≤ Real.log (N : ℝ) := by
        rw [div_le_iff₀ hHpos]
        have hlt := (div_lt_iff₀ hlog_pos).mp hreg
        linarith
      have h2 : ((N : ℝ) + (H N : ℝ)) / (H N : ℝ) = (N : ℝ) / (H N : ℝ) + 1 := by
        field_simp [hHpos.ne']
      linarith
    have hval_sq_lt : val ^ 2 < ε ^ 2 := by
      have hstep1 : val ^ 2 ≤ (C / (Real.log (N : ℝ)) ^ 2) ^ 2 * (2 * Real.log (N : ℝ)) :=
        le_trans hsq (mul_le_mul_of_nonneg_left hratio (sq_nonneg _))
      have hstep2 : (C / (Real.log (N : ℝ)) ^ 2) ^ 2 * (2 * Real.log (N : ℝ)) =
          2 * C ^ 2 / (Real.log (N : ℝ)) ^ 3 := by
        field_simp [hlog_pos.ne']
      have hstep3 : 2 * C ^ 2 / (Real.log (N : ℝ)) ^ 3 < ε ^ 2 := by
        have hlog3 : Real.log (N : ℝ) ≤ (Real.log (N : ℝ)) ^ 3 := by
          have : (1 : ℝ) ≤ (Real.log (N : ℝ)) ^ 2 := by nlinarith
          nlinarith
        have hlt1 : 2 * C ^ 2 / ε ^ 2 < (Real.log (N : ℝ)) ^ 3 := by linarith
        rw [div_lt_iff₀ (pow_pos hlog_pos 3)]
        have hlt2 := (div_lt_iff₀ (pow_pos hε 2)).mp hlt1
        linarith
      linarith
    nlinarith [sq_nonneg (val - ε)]

end OMA.R_ChowlaLiouvilleConjecture_chowla_liouville_conjecture_variants_averaged_two_point_uniform_R1
