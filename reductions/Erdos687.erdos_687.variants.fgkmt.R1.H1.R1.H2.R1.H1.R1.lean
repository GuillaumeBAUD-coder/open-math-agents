import OMAReductions.R_Erdos687_erdos_687_variants_fgkmt_R1_H1_R1_H2_R1
import Mathlib

-- Reduction Erdos687.erdos_687.variants.fgkmt.R1.H1.R1.H2.R1.H1.R1 of step Erdos687.erdos_687.variants.fgkmt.R1.H1.R1.H2.R1.H1
-- Credit: @carterleffen

/-!
# Decoupling FGKMT Theorem 5 into primes in APs, admissible tuples, 1D Maynard weights, and Selberg sieve

Reduces `Erdos687.erdos_687.variants.fgkmt.R1.H1.R1.H2.R1.H1` (Theorem 5 of Ford, Green, Konyagin,
Maynard and Tao, *Long gaps between primes*, J. Amer. Math. Soc. 31 (2018)) into four independent
pure-Mathlib hypotheses:

* `H1`: Effective Landau-Page and Vaughan Bombieri-Vinogradov estimate for primes in `(x / 2, x]`
  in reduced arithmetic progressions of modulus `q <= x ^ (1 / 3)` coprime to an exceptional
  modulus `B <= exp(c_1 sqrt(log x))` with exponential saving `C x exp(-c_2 sqrt(log x))`
  (FGKMT Lemma 7.2).
* `H2`: Existence of an admissible prime `r`-tuple `H` inside `(r, 2 r ^ 2]` for
  `r = floor((log x) ^ (1 / 5))` together with elementary Chebyshev density bounds for primes in
  `(x / 2, x]`.
* `H3`: Existence of a compactly supported, monotone, measurable one-dimensional Maynard product
  sieve weight `g : ℝ → ℝ` with ratio `alpha ^ 2 / gamma` of order `log r` and controlled first
  and second moments.
* `H4`: Multidimensional Selberg sieve evaluation (Maynard 2016 Propositions 9.1 and 9.2, FGKMT
  Sections 7-8) producing unnormalized non-negative shift weights `w(p, n)` from `H1`, `H2`, `H3`.

Inside `main`, we normalize `μ p n := w p n / ∑ m ∈ T, w p m`, absorb the exact prime count
`|P|` into the scalar `u`, verify the pointwise bound `μ p n <= X ^ (-2 / 3)`, and propagate the
uniform relative error `1 / U ^ 4` in `S_1` and `S_2` to the target `1 / U ^ 3` error bound.
-/

namespace OMA.R_Erdos687_erdos_687_variants_fgkmt_R1_H1_R1_H2_R1_H1_R1

open Finset Filter Real
open scoped Classical

private lemma totient_div_bounds {B : ℕ} (hB : B = 1 ∨ B.Prime) :
    (0 : ℝ) < (B : ℝ) ∧ (1 / 2 : ℝ) ≤ (B.totient : ℝ) / (B : ℝ) ∧ (B.totient : ℝ) / (B : ℝ) ≤ 1 := by
  rcases hB with rfl | hp
  · norm_num
  · have hB2 : (2 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hp.two_le
    have hBpos : (0 : ℝ) < (B : ℝ) := by linarith
    have htot : (B.totient : ℝ) = (B : ℝ) - 1 := by
      rw [Nat.totient_prime hp, Nat.cast_sub hp.one_le, Nat.cast_one]
    refine ⟨hBpos, ?_, ?_⟩
    · rw [htot, le_div_iff₀ hBpos]
      linarith
    · rw [htot, div_le_iff₀ hBpos]
      linarith

private lemma tendsto_floor_log_rpow :
    Tendsto (fun x : ℕ => ⌊(Real.log (x : ℝ)) ^ (1 / 5 : ℝ)⌋₊) atTop atTop := by
  have hlog : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hrpow : Tendsto (fun x : ℕ => (Real.log (x : ℝ)) ^ (1 / 5 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 5)).comp hlog
  exact tendsto_nat_floor_atTop.comp hrpow

private lemma asymptotic_helpers (c : ℝ) (hc : 0 < c) :
    ∀ᶠ x : ℕ in atTop,
      let X : ℝ := x
      let L := Real.log X
      let U := Real.log L
      let y := c * X * L * Real.log U / U
      let r := ⌊L ^ (1 / 5 : ℝ)⌋₊
      100 ≤ X ∧ 1024 ≤ L ∧ 10 ≤ U ∧ 1 ≤ Real.log U ∧ X ≤ y ∧
      2 ≤ r ∧ (r : ℝ) ≤ L ^ (1 / 5 : ℝ) ∧ (1 / 2 : ℝ) * L ^ (1 / 5 : ℝ) ≤ (r : ℝ) ∧
      2 * ((r : ℝ) ^ 2) ≤ √L ∧
      (1 / 10 : ℝ) * U ≤ Real.log (r : ℝ) ∧ Real.log (r : ℝ) ≤ U := by
  have hX : Tendsto (fun x : ℕ => (x : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hL : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hX
  have hU : Tendsto (fun x : ℕ => Real.log (Real.log (x : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp hL
  have hlogU : Tendsto (fun x : ℕ => Real.log (Real.log (Real.log (x : ℝ)))) atTop atTop :=
    Real.tendsto_log_atTop.comp hU
  have hL_div_U : Tendsto (fun x : ℕ => Real.log (x : ℝ) / Real.log (Real.log (x : ℝ))) atTop atTop := by
    have h1 : Tendsto (fun t : ℝ => Real.log t / t) atTop (nhds 0) := by
      simpa [Real.rpow_one] using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    have h2 : Tendsto (fun t : ℝ => (Real.log t / t)⁻¹) atTop atTop := by
      refine Tendsto.inv_tendsto_nhdsGT_zero ?_
      rw [tendsto_nhdsWithin_iff]
      refine ⟨h1, ?_⟩
      filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
      exact div_pos (Real.log_pos ht) (by linarith)
    have h3 : Tendsto (fun t : ℝ => t / Real.log t) atTop atTop := by
      refine h2.congr' ?_
      filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
      simp [inv_div]
    exact h3.comp hL
  have hL15 : Tendsto (fun x : ℕ => (Real.log (x : ℝ)) ^ (1 / 5 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 5)).comp hL
  filter_upwards [hX.eventually (eventually_ge_atTop (100 : ℝ)),
    hL.eventually (eventually_ge_atTop (1024 : ℝ)),
    hU.eventually (eventually_ge_atTop (10 : ℝ)),
    hlogU.eventually (eventually_ge_atTop (1 : ℝ)),
    hL_div_U.eventually (eventually_ge_atTop (1 / c)),
    hL15.eventually (eventually_ge_atTop (4 : ℝ))] with x hX100 hL1024 hU10 hlogU1 hLU hL15_4
  dsimp only
  set X : ℝ := (x : ℝ)
  set L : ℝ := Real.log X
  set U : ℝ := Real.log L
  set y : ℝ := c * X * L * Real.log U / U
  set r : ℕ := ⌊L ^ (1 / 5 : ℝ)⌋₊
  have hXpos : 0 < X := by linarith only [hX100]
  have hLpos : 0 < L := by linarith only [hL1024]
  have hUpos : 0 < U := by linarith only [hU10]
  have hy_ge_X : X ≤ y := by
    have h1 : 1 ≤ c * (L / U) := by
      have := mul_le_mul_of_nonneg_left hLU hc.le
      rwa [mul_one_div_cancel hc.ne'] at this
    have h2 : c * (L / U) * 1 ≤ c * (L / U) * Real.log U :=
      mul_le_mul_of_nonneg_left hlogU1 (by positivity)
    have h3 : X * 1 ≤ X * (c * (L / U) * Real.log U) :=
      mul_le_mul_of_nonneg_left (by linarith only [h1, h2]) hXpos.le
    have hEq : X * (c * (L / U) * Real.log U) = y := by
      dsimp only [y]; ring
    linarith only [h3, hEq]
  have hr_le : (r : ℝ) ≤ L ^ (1 / 5 : ℝ) := Nat.floor_le (by positivity)
  have hr_gt : L ^ (1 / 5 : ℝ) - 1 < (r : ℝ) := by
    have := Nat.lt_floor_add_one (L ^ (1 / 5 : ℝ))
    linarith
  have hr_ge_half : (1 / 2 : ℝ) * L ^ (1 / 5 : ℝ) ≤ (r : ℝ) := by linarith
  have hr2 : 2 ≤ r := by
    have : (2 : ℝ) ≤ (r : ℝ) := by linarith
    exact_mod_cast this
  have h2r2_le : 2 * ((r : ℝ) ^ 2) ≤ √L := by
    have hsq : (r : ℝ) ^ 2 ≤ (L ^ (1 / 5 : ℝ)) ^ 2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg r) hr_le 2
    have hpow2 : (L ^ (1 / 5 : ℝ)) ^ 2 = L ^ (2 / 5 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hLpos.le]
      norm_num
    have hL10 : (2 : ℝ) ≤ L ^ (1 / 10 : ℝ) := by
      have h1024 : (2 : ℝ) ^ (10 : ℕ) = 1024 := by norm_num
      have hbase : ((2 : ℝ) ^ (10 : ℕ)) ^ (1 / 10 : ℝ) ≤ L ^ (1 / 10 : ℝ) :=
        Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)] at hbase
      norm_num at hbase
      exact hbase
    have hprod : 2 * L ^ (2 / 5 : ℝ) ≤ L ^ (1 / 10 : ℝ) * L ^ (2 / 5 : ℝ) :=
      mul_le_mul_of_nonneg_right hL10 (by positivity)
    have hmul : L ^ (1 / 10 : ℝ) * L ^ (2 / 5 : ℝ) = √L := by
      rw [← Real.rpow_add hLpos, Real.sqrt_eq_rpow]
      norm_num
    linarith
  have hrpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
  have hlogr_le : Real.log (r : ℝ) ≤ U := by
    have h1 : Real.log (r : ℝ) ≤ Real.log (L ^ (1 / 5 : ℝ)) :=
      Real.log_le_log hrpos hr_le
    rw [Real.log_rpow hLpos] at h1
    linarith
  have hlogr_ge : (1 / 10 : ℝ) * U ≤ Real.log (r : ℝ) := by
    have h1 : Real.log ((1 / 2 : ℝ) * L ^ (1 / 5 : ℝ)) ≤ Real.log (r : ℝ) :=
      Real.log_le_log (by positivity) hr_ge_half
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_rpow hLpos, one_div, Real.log_inv] at h1
    have hlog2 : Real.log 2 < 1 := by
      rw [Real.log_lt_iff_lt_exp (by norm_num)]
      linarith [Real.exp_one_gt_d9]
    linarith
  exact ⟨hX100, hL1024, hU10, hlogU1, hy_ge_X, hr2, hr_le, hr_ge_half, h2r2_le, hlogr_ge, hlogr_le⟩

private lemma ratio_error_bound {ε M₁ M₂ S₂ : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 4)
    (hM₁ : 0 < M₁) (hM₂ : 0 ≤ M₂)
    (hlo : (1 - ε) * M₂ ≤ S₂) (hhi : S₂ ≤ (1 + ε) * M₂)
    {s : ℝ} (hs_lo : S₂ / ((1 + ε) * M₁) ≤ s) (hs_hi : s ≤ S₂ / ((1 - ε) * M₁)) :
    |s - M₂ / M₁| ≤ 4 * ε * (M₂ / M₁) := by
  have h1m : (0 : ℝ) < 1 - ε := by linarith
  have h1p : (0 : ℝ) < 1 + ε := by linarith
  have hupper : s - M₂ / M₁ ≤ 4 * ε * (M₂ / M₁) := by
    have h1 : S₂ / ((1 - ε) * M₁) ≤ ((1 + ε) / (1 - ε)) * (M₂ / M₁) := by
      have heq : ((1 + ε) / (1 - ε)) * (M₂ / M₁) = ((1 + ε) * M₂) / ((1 - ε) * M₁) := by
        field_simp [h1m.ne', hM₁.ne']
      rw [heq]
      exact div_le_div_of_nonneg_right hhi (by positivity)
    have h2 : (1 + ε) / (1 - ε) ≤ 1 + 4 * ε := by
      rw [div_le_iff₀ h1m]
      nlinarith only [hε0, hε]
    have h3 : ((1 + ε) / (1 - ε)) * (M₂ / M₁) ≤ (1 + 4 * ε) * (M₂ / M₁) :=
      mul_le_mul_of_nonneg_right h2 (div_nonneg hM₂ hM₁.le)
    linarith only [hs_hi, h1, h3]
  have hlower : -(4 * ε * (M₂ / M₁)) ≤ s - M₂ / M₁ := by
    have h1 : ((1 - ε) / (1 + ε)) * (M₂ / M₁) ≤ S₂ / ((1 + ε) * M₁) := by
      have heq : ((1 - ε) / (1 + ε)) * (M₂ / M₁) = ((1 - ε) * M₂) / ((1 + ε) * M₁) := by
        field_simp [h1p.ne', hM₁.ne']
      rw [heq]
      exact div_le_div_of_nonneg_right hlo (by positivity)
    have h2 : 1 - 4 * ε ≤ (1 - ε) / (1 + ε) := by
      rw [le_div_iff₀ h1p]
      nlinarith only [hε0, hε]
    have h3 : (1 - 4 * ε) * (M₂ / M₁) ≤ ((1 - ε) / (1 + ε)) * (M₂ / M₁) :=
      mul_le_mul_of_nonneg_right h2 (div_nonneg hM₂ hM₁.le)
    linarith only [hs_lo, h1, h3]
  exact abs_le.mpr ⟨hlower, hupper⟩

private lemma rpow_pointwise_bound {X : ℝ} (hX : 1 ≤ X) :
    X ^ (1 / 4 : ℝ) / (X * X ^ (-(1 / 20 : ℝ))) ≤ X ^ (-2 / 3 : ℝ) := by
  have hXpos : 0 < X := by linarith only [hX]
  have hden : X * X ^ (-(1 / 20 : ℝ)) = X ^ (19 / 20 : ℝ) := by
    calc X * X ^ (-(1 / 20 : ℝ))
        = X ^ (1 : ℝ) * X ^ (-(1 / 20 : ℝ)) := by rw [Real.rpow_one]
      _ = X ^ ((1 : ℝ) + -(1 / 20 : ℝ)) := (Real.rpow_add hXpos _ _).symm
      _ = X ^ (19 / 20 : ℝ) := by norm_num
  have hdiv : X ^ (1 / 4 : ℝ) / X ^ (19 / 20 : ℝ) = X ^ (-(7 / 10 : ℝ)) := by
    rw [← Real.rpow_sub hXpos]
    congr 1; norm_num
  rw [hden, hdiv]
  exact Real.rpow_le_rpow_of_exponent_le hX (by norm_num)

private lemma m2_div_m1_eq {a b c d e f g : ℝ} (hb : b ≠ 0) (hd : d ≠ 0) (hf : f ≠ 0) :
    a * c * (e / 10) * g * f / (2 * d * f) = a * (c * e / (10 * b)) * g * b / (2 * d) := by
  field_simp [hb, hd, hf]

def H1 : Prop :=
  ∃ c₁ c₂ C : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ 0 < C ∧ ∀ᶠ x : ℕ in Filter.atTop,
    ∃ B : ℕ, (B = 1 ∨ B.Prime) ∧ (B : ℝ) ≤ Real.exp (c₁ * √(Real.log x)) ∧
      ∃ M : ℕ → ℝ,
        (∀ q ∈ Finset.Icc 1 ⌊(x : ℝ) ^ (1 / 3 : ℝ)⌋₊, Nat.Coprime q B → ∀ a : (ZMod q)ˣ,
          |(((Finset.Ioc (x / 2) x).filter (fun p : ℕ => p.Prime ∧ (p : ZMod q) = (a : ZMod q))).card : ℝ) -
            (((Finset.Ioc (x / 2) x).filter Nat.Prime).card : ℝ) / (q.totient : ℝ)| ≤ M q) ∧
        (∑ q ∈ (Finset.Icc 1 ⌊(x : ℝ) ^ (1 / 3 : ℝ)⌋₊).filter (fun q => Nat.Coprime q B), M q) ≤
          C * (x : ℝ) * Real.exp (-c₂ * √(Real.log x))

def H2 : Prop :=
  ∀ᶠ x : ℕ in Filter.atTop,
    let X : ℝ := x
    let r := ⌊(Real.log X) ^ (1 / 5 : ℝ)⌋₊
    let P := (Finset.Ioc (x / 2) x).filter Nat.Prime
    (∃ H : Finset ℕ, H.card = r ∧ (∀ h ∈ H, h.Prime ∧ r < h ∧ h ≤ 2 * r ^ 2)) ∧
    (1 / 10 : ℝ) * X / Real.log X ≤ (P.card : ℝ) ∧
    (P.card : ℝ) ≤ 4 * X / Real.log X

def H3 : Prop :=
  ∃ d₁ d₂ : ℝ, 0 < d₁ ∧ d₁ ≤ d₂ ∧ ∀ᶠ r : ℕ in Filter.atTop,
    ∃ g : ℝ → ℝ,
      Measurable g ∧ (∀ u, 0 ≤ g u ∧ g u ≤ 1) ∧
      AntitoneOn g (Set.Ici 0) ∧
      (∀ u, u < 0 ∨ (r : ℝ) ^ (1 / 4 : ℝ) ≤ u → g u = 0) ∧
      let γ := ∫ u : ℝ, (g u) ^ 2
      let α := ∫ u : ℝ, g u
      (32 * Real.log r)⁻¹ ≤ γ ∧
      (∫ u : ℝ, u * (g u) ^ 2) ≤ (1 / 4) * γ ∧
      (∫ u : ℝ, u ^ 2 * (g u) ^ 2) ≤ (r : ℝ) ^ (1 / 2 : ℝ) * γ ∧
      d₁ * Real.log r * γ ≤ α ^ 2 ∧
      α ^ 2 ≤ d₂ * Real.log r * γ

def H4 : Prop :=
  ∀ c c₁ c₂ C d₁ : ℝ, 0 < c → 0 < c₁ → 0 < c₂ → 0 < C → 0 < d₁ →
    ∀ᶠ x : ℕ in Filter.atTop,
      let X : ℝ := x
      let L := Real.log X
      let U := Real.log L
      let y := c * X * L * Real.log U / U
      let r := ⌊L ^ (1 / 5 : ℝ)⌋₊
      let P := (Finset.Ioc (x / 2) x).filter Nat.Prime
      let V := (Finset.Ioc x ⌊y⌋₊).filter Nat.Prime
      let T := Finset.Icc (-(⌊y⌋₊ : ℤ)) (⌊y⌋₊ : ℤ)
      (1 / 10 : ℝ) * X / L ≤ (P.card : ℝ) →
      ∀ (B : ℕ) (M : ℕ → ℝ) (H : Finset ℕ) (g : ℝ → ℝ),
        (B = 1 ∨ B.Prime) → (B : ℝ) ≤ Real.exp (c₁ * √L) →
        (∀ q ∈ Finset.Icc 1 ⌊X ^ (1 / 3 : ℝ)⌋₊, Nat.Coprime q B → ∀ a : (ZMod q)ˣ,
          |(((Finset.Ioc (x / 2) x).filter (fun p : ℕ => p.Prime ∧ (p : ZMod q) = (a : ZMod q))).card : ℝ) -
            (P.card : ℝ) / (q.totient : ℝ)| ≤ M q) →
        (∑ q ∈ (Finset.Icc 1 ⌊X ^ (1 / 3 : ℝ)⌋₊).filter (fun q => Nat.Coprime q B), M q) ≤
          C * X * Real.exp (-c₂ * √L) →
        H.card = r → (∀ h ∈ H, h.Prime ∧ r < h ∧ h ≤ 2 * r ^ 2) →
        Measurable g → (∀ u, 0 ≤ g u ∧ g u ≤ 1) → AntitoneOn g (Set.Ici 0) →
        (∀ u, u < 0 ∨ (r : ℝ) ^ (1 / 4 : ℝ) ≤ u → g u = 0) →
        let γ := ∫ u : ℝ, (g u) ^ 2
        let α := ∫ u : ℝ, g u
        (32 * Real.log r)⁻¹ ≤ γ →
        (∫ u : ℝ, u * (g u) ^ 2) ≤ (1 / 4) * γ →
        (∫ u : ℝ, u ^ 2 * (g u) ^ 2) ≤ (r : ℝ) ^ (1 / 2 : ℝ) * γ →
        d₁ * Real.log r * γ ≤ α ^ 2 →
        ∃ (w : ℕ → ℤ → ℝ) (A : ℝ), X ^ (-(1 / 20 : ℝ)) ≤ A ∧
          (∀ p ∈ P, (∀ n, 0 ≤ w p n) ∧ (∀ n, n ∉ T → w p n = 0) ∧ (∀ n, w p n ≤ X ^ (1 / 4 : ℝ)) ∧
            |(∑ n ∈ T, w p n) - 2 * y * A| ≤ (1 / U ^ 4) * (2 * y * A)) ∧
          (∀ q ∈ V,
            let M₂ := (B.totient : ℝ) / (B : ℝ) * (P.card : ℝ) * (L / 10) * (α ^ 2 / γ) * A
            |(∑ p ∈ P, ∑ h ∈ H, w p ((q : ℤ) - (h : ℤ) * p)) - M₂| ≤ (1 / U ^ 4) * M₂)

theorem main : H1 → H2 → H3 → H4 → OMA.R_Erdos687_erdos_687_variants_fgkmt_R1_H1_R1_H2_R1.H1 := by
  intro h1 h2 h3 h4
  obtain ⟨c₁, c₂, C, hc₁, hc₂, hC, hBV⟩ := h1
  obtain ⟨d₁, d₂, hd₁, hd₁₂, hW⟩ := h3
  refine ⟨d₁ / 2000, d₂, by positivity, by linarith, ?_⟩
  intro c hc
  have hW_x := tendsto_floor_log_rpow.eventually hW
  have hSieve := h4 c c₁ c₂ C d₁ hc hc₁ hc₂ hC hd₁
  filter_upwards [hBV, h2, hW_x, hSieve, asymptotic_helpers c hc] with x hxBV hx2 hxW hxSieve hxAsym
  obtain ⟨hX100, hL1024, hU10, hlogU1, hy_ge_X, hr2, hr_le, hr_ge_half, h2r2_le, hlogr_ge, hlogr_le⟩ := hxAsym
  let X : ℝ := x
  let L : ℝ := Real.log X
  let U : ℝ := Real.log L
  let y : ℝ := c * X * L * Real.log U / U
  let r : ℕ := ⌊L ^ (1 / 5 : ℝ)⌋₊
  let P : Finset ℕ := (Finset.Ioc (x / 2) x).filter Nat.Prime
  let V : Finset ℕ := (Finset.Ioc x ⌊y⌋₊).filter Nat.Prime
  let T : Finset ℤ := Finset.Icc (-(⌊y⌋₊ : ℤ)) (⌊y⌋₊ : ℤ)
  have hXpos : 0 < X := by linarith only [hX100]
  have hLpos : 0 < L := by linarith only [hL1024]
  have hUpos : 0 < U := by linarith only [hU10]
  have hypos : 0 < y := by linarith only [hXpos, hy_ge_X]
  obtain ⟨B, hBprime, hBbound, M, hM_pt, hM_sum⟩ := hxBV
  obtain ⟨⟨H, hHcard, hHprop⟩, hP_lo, hP_hi⟩ := hx2
  obtain ⟨g, hg_meas, hg_01, hg_anti, hg_supp, hγ_lo, hμ_hi, hσ_hi, hα_lo, hα_hi⟩ := hxW
  let γ : ℝ := ∫ u : ℝ, (g u) ^ 2
  let α : ℝ := ∫ u : ℝ, g u
  have hlogr_pos : 0 < Real.log (r : ℝ) := by linarith only [hU10, hlogr_ge]
  have hγ_pos : 0 < γ := lt_of_lt_of_le (by positivity) hγ_lo
  have hratio_lo : d₁ * Real.log (r : ℝ) ≤ α ^ 2 / γ :=
    (le_div_iff₀ hγ_pos).mpr hα_lo
  have hratio_hi : α ^ 2 / γ ≤ d₂ * Real.log (r : ℝ) :=
    (div_le_iff₀ hγ_pos).mpr hα_hi
  obtain ⟨w, A, hA_lo, hw_p, hw_q⟩ :=
    hxSieve hP_lo B M H g hBprime hBbound hM_pt hM_sum hHcard hHprop
      hg_meas hg_01 hg_anti hg_supp hγ_lo hμ_hi hσ_hi hα_lo
  obtain ⟨hBpos, hφB_lo, hφB_hi⟩ := totient_div_bounds hBprime
  have hA_pos : 0 < A := lt_of_lt_of_le (Real.rpow_pos_of_pos hXpos _) hA_lo
  let M₁ : ℝ := 2 * y * A
  let M₂ : ℝ := (B.totient : ℝ) / (B : ℝ) * (P.card : ℝ) * (L / 10) * (α ^ 2 / γ) * A
  let u : ℝ := (B.totient : ℝ) / (B : ℝ) * ((P.card : ℝ) * L / (10 * X)) * (α ^ 2 / γ)
  let μ : ℕ → ℤ → ℝ := fun p n => w p n / (∑ m ∈ T, w p m)
  have hM₁_pos : 0 < M₁ := by dsimp only [M₁]; positivity
  have hM₂_nn : 0 ≤ M₂ := by
    dsimp only [M₂]
    have h1 : 0 ≤ (B.totient : ℝ) / (B : ℝ) := by linarith only [hφB_lo]
    have h2 : 0 ≤ α ^ 2 / γ := div_nonneg (sq_nonneg α) hγ_pos.le
    positivity
  have hε_nn : (0 : ℝ) ≤ 1 / U ^ 4 := by positivity
  have hε_le : (1 / U ^ 4 : ℝ) ≤ 1 / 4 := by
    have hU4 : (10 : ℝ) ^ 4 ≤ U ^ 4 := pow_le_pow_left₀ (by norm_num) hU10 4
    rw [div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 4)]
    linarith only [hU4]
  have h4ε_le : 4 * (1 / U ^ 4 : ℝ) ≤ 1 / U ^ 3 := by
    have hU3pos : 0 < U ^ 3 := pow_pos hUpos 3
    have hU4 : 4 * U ^ 3 ≤ U ^ 4 := by
      have : U ^ 4 = U * U ^ 3 := by ring
      nlinarith only [hU10, hU3pos, this]
    rw [show 4 * (1 / U ^ 4 : ℝ) = 4 / U ^ 4 by ring,
      div_le_div_iff₀ (by positivity) hU3pos]
    linarith only [hU4]
  have hHne : H.Nonempty := Finset.card_pos.mp (by omega)
  have hHcard_le : (H.card : ℝ) ≤ L ^ (1 / 5 : ℝ) := by
    rw [hHcard]; exact hr_le
  have hHmax : ∀ h ∈ H, (h : ℝ) ≤ √L := fun h hh => by
    have hle : (h : ℝ) ≤ 2 * (r : ℝ) ^ 2 := by exact_mod_cast (hHprop h hh).2.2
    exact hle.trans h2r2_le
  have hPL_lo : (1 / 100 : ℝ) ≤ (P.card : ℝ) * L / (10 * X) := by
    rw [le_div_iff₀ (by positivity)]
    have h1 : (1 / 10 : ℝ) * X ≤ (P.card : ℝ) * L := (div_le_iff₀ hLpos).mp hP_lo
    linarith only [h1]
  have hPL_hi : (P.card : ℝ) * L / (10 * X) ≤ 2 / 5 := by
    rw [div_le_iff₀ (by positivity)]
    have h1 : (P.card : ℝ) * L ≤ 4 * X := (le_div_iff₀ hLpos).mp hP_hi
    linarith only [h1]
  have hu_lo : d₁ / 2000 * U ≤ u := by
    have h1 : (1 / 2 : ℝ) * (1 / 100 : ℝ) ≤
        (B.totient : ℝ) / (B : ℝ) * ((P.card : ℝ) * L / (10 * X)) :=
      mul_le_mul hφB_lo hPL_lo (by norm_num) (by linarith only [hφB_lo])
    have h2 : d₁ * ((1 / 10 : ℝ) * U) ≤ α ^ 2 / γ :=
      (mul_le_mul_of_nonneg_left hlogr_ge hd₁.le).trans hratio_lo
    have h3 : (1 / 2 : ℝ) * (1 / 100 : ℝ) * (d₁ * ((1 / 10 : ℝ) * U)) ≤ u :=
      mul_le_mul h1 h2 (by positivity) (by linarith only [h1])
    linarith only [h3]
  have hu_hi : u ≤ d₂ * U := by
    have h1 : (B.totient : ℝ) / (B : ℝ) * ((P.card : ℝ) * L / (10 * X)) ≤ 1 * (2 / 5 : ℝ) :=
      mul_le_mul hφB_hi hPL_hi (by positivity) (by norm_num)
    have h2 : α ^ 2 / γ ≤ d₂ * U :=
      hratio_hi.trans (mul_le_mul_of_nonneg_left hlogr_le (by linarith only [hd₁, hd₁₂]))
    have h3 : u ≤ (1 * (2 / 5 : ℝ)) * (d₂ * U) :=
      mul_le_mul h1 h2 (div_nonneg (sq_nonneg α) hγ_pos.le) (by norm_num)
    have h4 : 0 ≤ d₂ * U := mul_nonneg (by linarith only [hd₁, hd₁₂]) hUpos.le
    linarith only [h3, h4]
  have hS1_bounds : ∀ p ∈ P,
      (1 - 1 / U ^ 4) * M₁ ≤ (∑ m ∈ T, w p m) ∧ (∑ m ∈ T, w p m) ≤ (1 + 1 / U ^ 4) * M₁ := by
    intro p hp
    have habs := (hw_p p hp).2.2.2
    rw [abs_le] at habs
    constructor <;> linarith only [habs.1, habs.2]
  have hS1_pos : ∀ p ∈ P, 0 < ∑ m ∈ T, w p m := by
    intro p hp
    have hlo := (hS1_bounds p hp).1
    have h1 : (1 / 2 : ℝ) * M₁ ≤ (1 - 1 / U ^ 4) * M₁ :=
      mul_le_mul_of_nonneg_right (by linarith only [hε_le]) hM₁_pos.le
    linarith only [hlo, h1, hM₁_pos]
  have hμ_props : ∀ p ∈ P, (∀ n : ℤ, 0 ≤ μ p n) ∧ (∀ n : ℤ, n ∉ T → μ p n = 0) ∧
      (∑ n ∈ T, μ p n) = 1 ∧ (∀ n : ℤ, μ p n ≤ X ^ (-2 / 3 : ℝ)) := by
    intro p hp
    obtain ⟨hw_nn, hw_supp, hw_max, _⟩ := hw_p p hp
    have hSp := hS1_pos p hp
    refine ⟨fun n => div_nonneg (hw_nn n) hSp.le,
      fun n hn => by dsimp only [μ]; rw [hw_supp n hn, zero_div], ?_, ?_⟩
    · dsimp only [μ]
      rw [← Finset.sum_div, div_self hSp.ne']
    · intro n
      dsimp only [μ]
      have hS_ge : X * X ^ (-(1 / 20 : ℝ)) ≤ ∑ m ∈ T, w p m := by
        have h1 : y * A ≤ ∑ m ∈ T, w p m := by
          have hlo := (hS1_bounds p hp).1
          have h2 : (1 / 2 : ℝ) * M₁ = y * A := by dsimp only [M₁]; ring
          have h3 : (1 / 2 : ℝ) * M₁ ≤ (1 - 1 / U ^ 4) * M₁ :=
            mul_le_mul_of_nonneg_right (by linarith only [hε_le]) hM₁_pos.le
          linarith only [hlo, h2, h3]
        have h2 : X * X ^ (-(1 / 20 : ℝ)) ≤ y * A :=
          mul_le_mul hy_ge_X hA_lo (by positivity) hypos.le
        exact h2.trans h1
      have hstep : w p n / (∑ m ∈ T, w p m) ≤ X ^ (1 / 4 : ℝ) / (X * X ^ (-(1 / 20 : ℝ))) :=
        div_le_div₀ (by positivity) (hw_max n) (by positivity) hS_ge
      exact hstep.trans (rpow_pointwise_bound (by linarith only [hX100]))
  have hM2_div_M1 : M₂ / M₁ = u * X / (2 * y) :=
    m2_div_m1_eq hXpos.ne' hypos.ne' hA_pos.ne'
  have hq_avg : ∀ q ∈ V,
      |(∑ p ∈ P, ∑ h ∈ H, μ p ((q : ℤ) - (h : ℤ) * p)) - u * X / (2 * y)| ≤
        (1 / U ^ 3) * (u * X / (2 * y)) := by
    intro q hq
    set S₂ : ℝ := ∑ p ∈ P, ∑ h ∈ H, w p ((q : ℤ) - (h : ℤ) * p)
    have hS₂_abs : |S₂ - M₂| ≤ (1 / U ^ 4) * M₂ := hw_q q hq
    rw [abs_le] at hS₂_abs
    have hS₂_lo : (1 - 1 / U ^ 4) * M₂ ≤ S₂ := by linarith only [hS₂_abs.1]
    have hS₂_hi : S₂ ≤ (1 + 1 / U ^ 4) * M₂ := by linarith only [hS₂_abs.2]
    have hs_lo : S₂ / ((1 + 1 / U ^ 4) * M₁) ≤ ∑ p ∈ P, ∑ h ∈ H, μ p ((q : ℤ) - (h : ℤ) * p) := by
      dsimp only [S₂, μ]
      rw [Finset.sum_div]
      apply Finset.sum_le_sum
      intro p hp
      rw [Finset.sum_div]
      apply Finset.sum_le_sum
      intro h _
      exact div_le_div_of_nonneg_left ((hw_p p hp).1 _) (hS1_pos p hp) (hS1_bounds p hp).2
    have hs_hi : ∑ p ∈ P, ∑ h ∈ H, μ p ((q : ℤ) - (h : ℤ) * p) ≤ S₂ / ((1 - 1 / U ^ 4) * M₁) := by
      dsimp only [S₂, μ]
      rw [Finset.sum_div]
      apply Finset.sum_le_sum
      intro p hp
      rw [Finset.sum_div]
      apply Finset.sum_le_sum
      intro h _
      have hden_pos : 0 < (1 - 1 / U ^ 4) * M₁ := mul_pos (by linarith only [hε_le]) hM₁_pos
      exact div_le_div_of_nonneg_left ((hw_p p hp).1 _) hden_pos (hS1_bounds p hp).1
    have hrat := ratio_error_bound hε_nn hε_le hM₁_pos hM₂_nn hS₂_lo hS₂_hi hs_lo hs_hi
    rw [hM2_div_M1] at hrat
    have huX_nn : 0 ≤ u * X / (2 * y) := by
      rw [← hM2_div_M1]; exact div_nonneg hM₂_nn hM₁_pos.le
    exact hrat.trans (mul_le_mul_of_nonneg_right h4ε_le huX_nn)
  exact ⟨H, μ, u, hHne, hHcard_le, hHmax, hu_lo, hu_hi, hμ_props, hq_avg⟩

end OMA.R_Erdos687_erdos_687_variants_fgkmt_R1_H1_R1_H2_R1_H1_R1
