import FormalConjectures.ErdosProblems.«525»
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Tactic

/-!
# Reduction of `Erdos525.erdos_525.variants.konyagin_schlag`

Following S. V. Konyagin and W. Schlag (*Lower bounds for the absolute value of random polynomials
on a neighborhood of the unit circle*, Trans. Amer. Math. Soc. **351** (1999), 4963–4980), we
reduce the linear tail bound for the minimum modulus of a random Littlewood polynomial
$$\limsup_{n\to\infty} \mathbb{P}\!\left(m(f) \le \frac{\varepsilon}{\sqrt{n}}\right) \le C \varepsilon$$
to two independent probabilistic pillars on dyadic local-derivative scales:
1. `H1`: **Grid-summed local small-ball and derivative-scale estimate** (Konyagin–Schlag 1999):
   there is a universal constant `C₁ > 0` such that for every `ε ∈ (0, 1]` and dyadic scale `k : ℕ`,
   for all sufficiently large `n`, summing over the uniform grid of
   `M = n * ⌈2π · 2^k · n / ε⌉` points on `[0, 2π]` the probability that
   `‖eval f (exp (i θ_r))‖ ≤ 2ε / √n` (and when `k ≥ 1`, the angular derivative on
   `[θ_r - 4π/n, θ_r + 4π/n]` exceeds `2^{k-1} n^{3/2}`) is at most `C₁ ε / 2^k`.
2. `H2`: **High local-derivative tail cutoff**: for every `ε ∈ (0, 1]` and `δ > 0`, there is a
   scale `K : ℕ` such that for all sufficiently large `n`, the probability that `eval f` attains
   norm `≤ ε / √n` at some `θ ∈ [0, 2π]` whose `2π/n`-neighborhood has angular derivative
   exceeding `2^K n^{3/2}` is at most `δ`.

Inside `main`, we prove from scratch:
- Continuity of `z ↦ ‖eval f z‖` and attainment of `m f` at a minimizer `z₀ ∈ S¹` with angle
  `θ₀ ∈ [0, 2π]`.
- The explicit complex derivative of `θ ↦ eval f (exp (i θ))` and the Mean Value Theorem bound
  propagating `‖eval f (exp (i θ₀))‖ ≤ ε / √n` to the nearest grid point `θ_r` at scale `k`
  (`‖eval f (exp (i θ_r))‖ ≤ 2ε / √n`).
- The finite union bound over scales `0 ≤ k ≤ K` and grid points `r : Fin M`, the geometric series
  bound `∑_{k ≤ K} 2^{-k} ≤ 2`, and the `Filter.limsup_le_of_le` passage to the limit superior.

Credit: @tkaiman
-/

namespace OMA.R_Erdos525_erdos_525_variants_konyagin_schlag_R1

open Filter Real Finset Complex
open scoped Classical BigOperators

/- ### Step 1: Minimizer attainment on `S¹` and polar angle in `[0, 2π]` -/

private lemma continuous_eval {n : ℕ} (f : Fin (n + 1) → ℤˣ) :
    Continuous (fun z : ℂ => Erdos525.eval f z) := by
  unfold Erdos525.eval
  exact continuous_finsetSum _ fun j _ => continuous_const.mul (continuous_pow _)

private lemma exists_angle_minimizer {n : ℕ} (f : Fin (n + 1) → ℤˣ) :
    ∃ θ ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
      ‖Erdos525.eval f (Complex.exp (Complex.I * (θ : ℂ)))‖ = Erdos525.m f := by
  have hcomp : IsCompact (Metric.sphere (0 : ℂ) 1) := isCompact_sphere (0 : ℂ) 1
  have hne : (Metric.sphere (0 : ℂ) 1).Nonempty := ⟨1, by simp⟩
  have hcont : ContinuousOn (fun z : ℂ => ‖Erdos525.eval f z‖) (Metric.sphere (0 : ℂ) 1) :=
    (continuous_eval f).norm.continuousOn
  obtain ⟨z₀, hz₀_mem, hz₀_min⟩ := hcomp.exists_isMinOn hne hcont
  have hm_eq : Erdos525.m f = ‖Erdos525.eval f z₀‖ := by
    unfold Erdos525.m
    apply le_antisymm
    · exact csInf_le ⟨0, by rintro _ ⟨w, -, rfl⟩; exact norm_nonneg _⟩ ⟨z₀, hz₀_mem, rfl⟩
    · refine le_csInf (hne.image _) ?_
      rintro _ ⟨w, hw, rfl⟩
      exact hz₀_min hw
  have hnorm1 : ‖z₀‖ = 1 := by simpa [Metric.mem_sphere] using hz₀_mem
  let a : ℝ := Complex.arg z₀
  let θ : ℝ := if 0 ≤ a then a else a + 2 * Real.pi
  have hθ_mem : θ ∈ Set.Icc (0 : ℝ) (2 * Real.pi) := by
    have hlow : -Real.pi < a := Complex.neg_pi_lt_arg z₀
    have hhi : a ≤ Real.pi := Complex.arg_le_pi z₀
    dsimp [θ]
    split_ifs with h0
    · exact ⟨h0, by linarith [Real.pi_pos]⟩
    · exact ⟨by linarith, by linarith⟩
  have hexp_eq : Complex.exp (Complex.I * (θ : ℂ)) = z₀ := by
    have hbase : Complex.exp ((a : ℂ) * Complex.I) = z₀ := by
      have h := Complex.norm_mul_exp_arg_mul_I z₀
      rwa [hnorm1, Complex.ofReal_one, one_mul] at h
    dsimp [θ]
    split_ifs with h0
    · rw [mul_comm, hbase]
    · push_cast
      rw [mul_add, Complex.exp_add, mul_comm Complex.I (a : ℂ), hbase]
      have h2pi : Complex.I * (2 * (Real.pi : ℂ)) = 2 * (Real.pi : ℂ) * Complex.I := by ring
      rw [h2pi, Complex.exp_two_pi_mul_I, mul_one]
  exact ⟨θ, hθ_mem, by rw [hexp_eq, hm_eq]⟩

/- ### Step 2: Complex angular derivative and Mean Value Theorem bound -/

private lemma hasDerivAt_eval_exp {n : ℕ} (f : Fin (n + 1) → ℤˣ) (t : ℝ) :
    HasDerivAt (fun θ : ℝ => Erdos525.eval f (Complex.exp (Complex.I * (θ : ℂ))))
      (∑ j : Fin (n + 1),
        ((f j : ℤ) : ℂ) * (Complex.I * (j : ℂ)) *
          Complex.exp (Complex.I * (j : ℂ) * (t : ℂ))) t := by
  have hterm : ∀ j : Fin (n + 1),
      HasDerivAt (fun θ : ℝ => ((f j : ℤ) : ℂ) * (Complex.exp (Complex.I * (θ : ℂ))) ^ (j : ℕ))
        (((f j : ℤ) : ℂ) * (Complex.I * (j : ℂ)) *
          Complex.exp (Complex.I * (j : ℂ) * (t : ℂ))) t := by
    intro j
    have hfun : (fun θ : ℝ => ((f j : ℤ) : ℂ) * (Complex.exp (Complex.I * (θ : ℂ))) ^ (j : ℕ)) =
        (fun θ : ℝ => ((f j : ℤ) : ℂ) * Complex.exp ((Complex.I * (j : ℂ)) * (θ : ℂ))) := by
      funext θ
      rw [← Complex.exp_nat_mul]
      congr 2
      ring
    rw [hfun]
    have hlin : HasDerivAt (fun θ : ℝ => (Complex.I * (j : ℂ)) * (θ : ℂ))
        (Complex.I * (j : ℂ)) t := by
      have h1 : HasDerivAt (fun θ : ℝ => (θ : ℂ)) 1 t := Complex.ofRealCLM.hasDerivAt
      simpa using h1.const_mul (Complex.I * (j : ℂ))
    have hexp : HasDerivAt (fun θ : ℝ => Complex.exp ((Complex.I * (j : ℂ)) * (θ : ℂ)))
        (Complex.exp ((Complex.I * (j : ℂ)) * (t : ℂ)) * (Complex.I * (j : ℂ))) t :=
      hlin.cexp
    have hmul := hexp.const_mul ((f j : ℤ) : ℂ)
    have hder_eq :
        ((f j : ℤ) : ℂ) * (Complex.exp ((Complex.I * (j : ℂ)) * (t : ℂ)) * (Complex.I * (j : ℂ))) =
        ((f j : ℤ) : ℂ) * (Complex.I * (j : ℂ)) * Complex.exp (Complex.I * (j : ℂ) * (t : ℂ)) := by
      ring
    rwa [hder_eq] at hmul
  simpa [Erdos525.eval] using HasDerivAt.fun_sum (u := Finset.univ) (fun j _ => hterm j)

private lemma norm_deriv_eq {n : ℕ} (f : Fin (n + 1) → ℤˣ) (t : ℝ) :
    ‖∑ j : Fin (n + 1),
        ((f j : ℤ) : ℂ) * (Complex.I * (j : ℂ)) *
          Complex.exp (Complex.I * (j : ℂ) * (t : ℂ))‖ =
    ‖∑ j : Fin (n + 1),
        (j : ℂ) * ((f j : ℤ) : ℂ) *
          Complex.exp (Complex.I * (j : ℂ) * (t : ℂ))‖ := by
  have hfac : (∑ j : Fin (n + 1),
      ((f j : ℤ) : ℂ) * (Complex.I * (j : ℂ)) *
        Complex.exp (Complex.I * (j : ℂ) * (t : ℂ))) =
      Complex.I * (∑ j : Fin (n + 1),
        (j : ℂ) * ((f j : ℤ) : ℂ) *
          Complex.exp (Complex.I * (j : ℂ) * (t : ℂ))) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => by ring
  rw [hfac, norm_mul, Complex.norm_I, one_mul]

private lemma eval_exp_sub_norm_le {n : ℕ} (f : Fin (n + 1) → ℤˣ) {a b B : ℝ}
    (hab : a ≤ b)
    (hderiv : ∀ t ∈ Set.Icc a b,
      ‖∑ j : Fin (n + 1),
        (j : ℂ) * ((f j : ℤ) : ℂ) *
          Complex.exp (Complex.I * (j : ℂ) * (t : ℂ))‖ ≤ B) :
    ‖Erdos525.eval f (Complex.exp (Complex.I * (a : ℂ))) -
      Erdos525.eval f (Complex.exp (Complex.I * (b : ℂ)))‖ ≤ B * (b - a) := by
  have hconv : Convex ℝ (Set.Icc a b) := convex_Icc a b
  have hmvt := hconv.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun θ : ℝ => Erdos525.eval f (Complex.exp (Complex.I * (θ : ℂ))))
    (f' := fun t : ℝ => ∑ j : Fin (n + 1),
      ((f j : ℤ) : ℂ) * (Complex.I * (j : ℂ)) *
        Complex.exp (Complex.I * (j : ℂ) * (t : ℂ)))
    (C := B)
    (fun t _ => (hasDerivAt_eval_exp f t).hasDerivWithinAt)
    (fun t ht => by rw [norm_deriv_eq]; exact hderiv t ht)
    (Set.right_mem_Icc.mpr hab) (Set.left_mem_Icc.mpr hab)
  have hnorm_sub : ‖a - b‖ = b - a := by
    rw [Real.norm_eq_abs, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hab)]
  rwa [hnorm_sub] at hmvt

/- ### Step 3: Finite probability union bound and geometric series bound -/

private lemma prob_mono {n : ℕ} {P Q : (Fin (n + 1) → ℤˣ) → Prop}
    (h : ∀ f, P f → Q f) : Erdos525.prob n P ≤ Erdos525.prob n Q := by
  unfold Erdos525.prob
  have hsub : (Finset.univ.filter P) ⊆ (Finset.univ.filter Q) := by
    intro f hf
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ f, h f (Finset.mem_filter.mp hf).2⟩
  exact div_le_div_of_nonneg_right (Nat.cast_le.mpr (Finset.card_le_card hsub)) (by positivity)

private lemma prob_or_le {n : ℕ} (P Q : (Fin (n + 1) → ℤˣ) → Prop) :
    Erdos525.prob n (fun f => P f ∨ Q f) ≤ Erdos525.prob n P + Erdos525.prob n Q := by
  unfold Erdos525.prob
  rw [← add_div]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  have hsub : (Finset.univ.filter fun f => P f ∨ Q f) ⊆
      (Finset.univ.filter P) ∪ (Finset.univ.filter Q) := by
    intro f hf
    rcases (Finset.mem_filter.mp hf).2 with hp | hq
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ f, hp⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ f, hq⟩)
  have hcard : (Finset.univ.filter fun f => P f ∨ Q f).card ≤
      (Finset.univ.filter P).card + (Finset.univ.filter Q).card :=
    (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hcast : (((Finset.univ.filter fun f => P f ∨ Q f).card : ℕ) : ℝ) ≤
      ((Finset.univ.filter P).card : ℝ) + ((Finset.univ.filter Q).card : ℝ) := by
    exact_mod_cast hcard
  exact le_trans
    (le_of_eq (congrArg (Nat.cast (R := ℝ)) (congrArg Finset.card (by ext f; simp))))
    (hcast.trans_eq (congrArg₂ (· + ·)
      (congrArg (Nat.cast (R := ℝ)) (congrArg Finset.card (by ext f; simp)))
      (congrArg (Nat.cast (R := ℝ)) (congrArg Finset.card (by ext f; simp)))))

private lemma prob_exists_finset_le {n : ℕ} {ι : Type*} (s : Finset ι)
    (P : ι → (Fin (n + 1) → ℤˣ) → Prop) :
    Erdos525.prob n (fun f => ∃ i ∈ s, P i f) ≤ ∑ i ∈ s, Erdos525.prob n (P i) := by
  unfold Erdos525.prob
  rw [← Finset.sum_div]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  have hsub : (Finset.univ.filter fun f => ∃ i ∈ s, P i f) ⊆
      s.biUnion (fun i => Finset.univ.filter (P i)) := by
    intro f hf
    obtain ⟨i, hi, hpi⟩ := (Finset.mem_filter.mp hf).2
    exact Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_filter.mpr ⟨Finset.mem_univ f, hpi⟩⟩
  have hcard : (Finset.univ.filter fun f => ∃ i ∈ s, P i f).card ≤
      ∑ i ∈ s, (Finset.univ.filter (P i)).card :=
    (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  have hcast : (((Finset.univ.filter fun f => ∃ i ∈ s, P i f).card : ℕ) : ℝ) ≤
      ∑ i ∈ s, ((Finset.univ.filter (P i)).card : ℝ) := by
    exact_mod_cast hcard
  exact le_trans
    (le_of_eq (congrArg (Nat.cast (R := ℝ)) (congrArg Finset.card (by ext f; simp))))
    (hcast.trans_eq (Finset.sum_congr rfl fun i _ =>
      congrArg (Nat.cast (R := ℝ)) (congrArg Finset.card (by ext f; simp))))

private lemma prob_nonneg (n : ℕ) (P : (Fin (n + 1) → ℤˣ) → Prop) :
    0 ≤ Erdos525.prob n P := by
  unfold Erdos525.prob
  positivity

private lemma prob_le_one (n : ℕ) (P : (Fin (n + 1) → ℤˣ) → Prop) :
    Erdos525.prob n P ≤ 1 := by
  unfold Erdos525.prob
  rw [div_le_one (by positivity)]
  have hcard : (Finset.univ.filter P).card ≤ (Finset.univ : Finset (Fin (n + 1) → ℤˣ)).card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  have huniv : (Finset.univ : Finset (Fin (n + 1) → ℤˣ)).card = 2 ^ (n + 1) := by
    simp [Fintype.card_pi, Fintype.card_units_int]
  rw [huniv] at hcard
  exact_mod_cast hcard

private lemma sum_inv_pow_two_le (K : ℕ) :
    ∑ k ∈ Finset.range (K + 1), (1 : ℝ) / (2 : ℝ) ^ k ≤ 2 := by
  induction K with
  | zero => norm_num
  | succ m ih =>
    have hsum : ∑ k ∈ Finset.range (m + 2), (1 : ℝ) / (2 : ℝ) ^ k =
        2 - (1 : ℝ) / (2 : ℝ) ^ (m + 1) := by
      clear ih
      induction m with
      | zero =>
        rw [Finset.sum_range_succ, Finset.sum_range_one]
        norm_num
      | succ r ihr =>
        rw [Finset.sum_range_succ, ihr]
        ring
    rw [hsum]
    have hpos : (0 : ℝ) ≤ (1 : ℝ) / (2 : ℝ) ^ (m + 1) := by positivity
    linarith

/- ### Hypotheses and main reduction theorem -/

/-- **Grid-summed local small-ball and derivative-scale estimate** (Konyagin–Schlag 1999):
there exists `C₁ > 0` such that for every `ε ∈ (0, 1]` and dyadic scale `k : ℕ`, for all
sufficiently large `n`, summing over the uniform grid of
`M = n * ⌈2π · 2^k · n / ε⌉` points on `[0, 2π]` the probability that
`‖eval f (exp (i θ_r))‖ ≤ 2ε / √n` (and when `k ≥ 1`, the angular derivative on
`[θ_r - 4π/n, θ_r + 4π/n]` exceeds `2^{k-1} n^{3/2}`) is at most `C₁ ε / 2^k`. -/
def H1 : Prop :=
  ∃ C₁ : ℝ, 0 < C₁ ∧
    ∀ ε ∈ Set.Ioc (0 : ℝ) 1, ∀ k : ℕ,
      ∀ᶠ n : ℕ in Filter.atTop,
        let M : ℕ := n * Nat.ceil (2 * Real.pi * (2 : ℝ) ^ k * (n : ℝ) / ε)
        ∑ r : Fin M,
          Erdos525.prob n (fun f =>
            ‖Erdos525.eval f (Complex.exp (Complex.I * (2 * Real.pi * (r : ℝ) / (M : ℝ))))‖ ≤
              2 * ε / Real.sqrt n ∧
            (k = 0 ∨ ∃ t ∈ Set.Icc (2 * Real.pi * (r : ℝ) / (M : ℝ) - 4 * Real.pi / (n : ℝ))
                (2 * Real.pi * (r : ℝ) / (M : ℝ) + 4 * Real.pi / (n : ℝ)),
              (2 : ℝ) ^ (k - 1) * (n : ℝ) ^ ((3 : ℝ) / 2) <
                ‖∑ j : Fin (n + 1), (j : ℂ) * ((f j : ℤ) : ℂ) *
                  Complex.exp (Complex.I * (j : ℂ) * (t : ℂ))‖)) ≤
          C₁ * ε / (2 : ℝ) ^ k

/-- **High local-derivative tail cutoff** (Konyagin–Schlag 1999):
for every `ε ∈ (0, 1]` and `δ > 0`, there exists a dyadic scale `K : ℕ` such that for all
sufficiently large `n`, the probability that `eval f` attains norm `≤ ε / √n` at some
`θ ∈ [0, 2π]` whose `2π/n`-neighborhood has angular derivative exceeding `2^K n^{3/2}` is at
most `δ`. -/
def H2 : Prop :=
  ∀ ε ∈ Set.Ioc (0 : ℝ) 1, ∀ δ : ℝ, 0 < δ →
    ∃ K : ℕ, ∀ᶠ n : ℕ in Filter.atTop,
      Erdos525.prob n (fun f =>
        ∃ θ ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
          ‖Erdos525.eval f (Complex.exp (Complex.I * (θ : ℂ)))‖ ≤ ε / Real.sqrt n ∧
          ∃ t ∈ Set.Icc (θ - 2 * Real.pi / (n : ℝ)) (θ + 2 * Real.pi / (n : ℝ)),
            (2 : ℝ) ^ K * (n : ℝ) ^ ((3 : ℝ) / 2) <
              ‖∑ j : Fin (n + 1), (j : ℂ) * ((f j : ℤ) : ℂ) *
                Complex.exp (Complex.I * (j : ℂ) * (t : ℂ))‖) ≤ δ

theorem main : H1 → H2 → type_of% @Erdos525.erdos_525.variants.konyagin_schlag := by
  rintro ⟨C₁, hC₁_pos, h1⟩ h2
  refine ⟨max 1 (2 * C₁ + 1), fun ε hε => ?_⟩
  have hC_ge1 : (1 : ℝ) ≤ max 1 (2 * C₁ + 1) := le_max_left _ _
  have hC_ge2 : 2 * C₁ + 1 ≤ max 1 (2 * C₁ + 1) := le_max_right _ _
  have hbdd_below : Filter.IsCoboundedUnder (· ≤ ·) Filter.atTop
      (fun n : ℕ => Erdos525.prob n fun f => Erdos525.m f ≤ ε / Real.sqrt n) :=
    Filter.isCoboundedUnder_le_of_le Filter.atTop fun n => prob_nonneg n _
  by_cases hε1 : 1 < ε
  · refine Filter.limsup_le_of_le hbdd_below ?_
    refine Filter.Eventually.of_forall fun n => ?_
    calc Erdos525.prob n (fun f => Erdos525.m f ≤ ε / Real.sqrt n)
        ≤ 1 := prob_le_one n _
      _ ≤ max 1 (2 * C₁ + 1) * ε := by nlinarith
  · push Not at hε1
    have hε_mem : ε ∈ Set.Ioc (0 : ℝ) 1 := ⟨hε, hε1⟩
    obtain ⟨K, hK_ev⟩ := h2 ε hε_mem ε hε
    have h1_all : ∀ᶠ n : ℕ in Filter.atTop,
        ∀ k ∈ Finset.range (K + 1),
          let M : ℕ := n * Nat.ceil (2 * Real.pi * (2 : ℝ) ^ k * (n : ℝ) / ε)
          ∑ r : Fin M,
            Erdos525.prob n (fun f =>
              ‖Erdos525.eval f (Complex.exp (Complex.I * (2 * Real.pi * (r : ℝ) / (M : ℝ))))‖ ≤
                2 * ε / Real.sqrt n ∧
              (k = 0 ∨ ∃ t ∈ Set.Icc (2 * Real.pi * (r : ℝ) / (M : ℝ) - 4 * Real.pi / (n : ℝ))
                  (2 * Real.pi * (r : ℝ) / (M : ℝ) + 4 * Real.pi / (n : ℝ)),
                (2 : ℝ) ^ (k - 1) * (n : ℝ) ^ ((3 : ℝ) / 2) <
                  ‖∑ j : Fin (n + 1), (j : ℂ) * ((f j : ℤ) : ℂ) *
                    Complex.exp (Complex.I * (j : ℂ) * (t : ℂ))‖)) ≤
            C₁ * ε / (2 : ℝ) ^ k :=
      Filter.eventually_all_finset (Finset.range (K + 1)) |>.mpr fun k _ => h1 ε hε_mem k
    refine Filter.limsup_le_of_le hbdd_below ?_
    filter_upwards [hK_ev, h1_all, Filter.eventually_ge_atTop (1 : ℕ)] with n hK_n h1_n hn1
    have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    -- Define the high-derivative tail event and the grid events at each scale `k ≤ K`
    let E_tail : (Fin (n + 1) → ℤˣ) → Prop := fun f =>
      ∃ θ ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
        ‖Erdos525.eval f (Complex.exp (Complex.I * (θ : ℂ)))‖ ≤ ε / Real.sqrt n ∧
        ∃ t ∈ Set.Icc (θ - 2 * Real.pi / (n : ℝ)) (θ + 2 * Real.pi / (n : ℝ)),
          (2 : ℝ) ^ K * (n : ℝ) ^ ((3 : ℝ) / 2) <
            ‖∑ j : Fin (n + 1), (j : ℂ) * ((f j : ℤ) : ℂ) *
              Complex.exp (Complex.I * (j : ℂ) * (t : ℂ))‖
    let Mk : ℕ → ℕ := fun k => n * Nat.ceil (2 * Real.pi * (2 : ℝ) ^ k * (n : ℝ) / ε)
    let E_scale : ℕ → (Fin (n + 1) → ℤˣ) → Prop := fun k f =>
      ∃ r : Fin (Mk k),
        ‖Erdos525.eval f (Complex.exp (Complex.I * (2 * Real.pi * (r : ℝ) / (Mk k : ℝ))))‖ ≤
          2 * ε / Real.sqrt n ∧
        (k = 0 ∨ ∃ t ∈ Set.Icc (2 * Real.pi * (r : ℝ) / (Mk k : ℝ) - 4 * Real.pi / (n : ℝ))
            (2 * Real.pi * (r : ℝ) / (Mk k : ℝ) + 4 * Real.pi / (n : ℝ)),
          (2 : ℝ) ^ (k - 1) * (n : ℝ) ^ ((3 : ℝ) / 2) <
            ‖∑ j : Fin (n + 1), (j : ℂ) * ((f j : ℤ) : ℂ) *
              Complex.exp (Complex.I * (j : ℂ) * (t : ℂ))‖)
    -- Every `f` with `m f ≤ ε / √n` belongs either to `E_tail` or to `E_scale k` for some `k ≤ K`
    have hcover : ∀ f : Fin (n + 1) → ℤˣ,
        Erdos525.m f ≤ ε / Real.sqrt n →
        (∃ k ∈ Finset.range (K + 1), E_scale k f) ∨ E_tail f := by
      intro f hmf
      obtain ⟨θ₀, hθ₀_mem, hθ₀_eq⟩ := exists_angle_minimizer f
      have hθ₀_le : ‖Erdos525.eval f (Complex.exp (Complex.I * (θ₀ : ℂ)))‖ ≤ ε / Real.sqrt n := by
        rwa [hθ₀_eq]
      let Pscale : ℕ → Prop := fun k =>
        ∀ t ∈ Set.Icc (θ₀ - 2 * Real.pi / (n : ℝ)) (θ₀ + 2 * Real.pi / (n : ℝ)),
          ‖∑ j : Fin (n + 1), (j : ℂ) * ((f j : ℤ) : ℂ) *
            Complex.exp (Complex.I * (j : ℂ) * (t : ℂ))‖ ≤
          (2 : ℝ) ^ k * (n : ℝ) ^ ((3 : ℝ) / 2)
      by_cases hPK : Pscale K
      · left
        have hex : ∃ k : ℕ, Pscale k := ⟨K, hPK⟩
        let k : ℕ := Nat.find hex
        have hk_spec : Pscale k := Nat.find_spec hex
        have hk_le : k ≤ K := Nat.find_min' hex hPK
        refine ⟨k, Finset.mem_range.mpr (Nat.lt_succ_of_le hk_le), ?_⟩
        -- Build the nearest grid point `θ_r = 2π r / Mk k ≤ θ₀`
        let m : ℕ := Nat.ceil (2 * Real.pi * (2 : ℝ) ^ k * (n : ℝ) / ε)
        have hm_pos : 0 < m := by
          dsimp [m]
          exact Nat.ceil_pos.mpr (by positivity)
        have hM_pos : 0 < Mk k := Nat.mul_pos (by omega) hm_pos
        have hM_real_pos : (0 : ℝ) < (Mk k : ℝ) := by exact_mod_cast hM_pos
        have hstep_le : 2 * Real.pi / (Mk k : ℝ) ≤ ε / ((2 : ℝ) ^ k * (n : ℝ) ^ 2) := by
          have hceil : 2 * Real.pi * (2 : ℝ) ^ k * (n : ℝ) / ε ≤ (m : ℝ) := Nat.le_ceil _
          have hM_ge : 2 * Real.pi * (2 : ℝ) ^ k * (n : ℝ) ^ 2 / ε ≤ (Mk k : ℝ) := by
            have h1 : (Mk k : ℝ) = (n : ℝ) * (m : ℝ) := by exact_mod_cast rfl
            rw [h1]
            have := mul_le_mul_of_nonneg_left hceil hn_pos.le
            calc 2 * Real.pi * (2 : ℝ) ^ k * (n : ℝ) ^ 2 / ε
                = (n : ℝ) * (2 * Real.pi * (2 : ℝ) ^ k * (n : ℝ) / ε) := by ring
              _ ≤ (n : ℝ) * (m : ℝ) := this
          rw [div_le_div_iff₀ hM_real_pos (by positivity)]
          have hmul := (div_le_iff₀ hε).mp hM_ge
          nlinarith [Real.pi_pos]
        have hstep_le_arc : 2 * Real.pi / (Mk k : ℝ) ≤ 2 * Real.pi / (n : ℝ) := by
          refine div_le_div_of_nonneg_left (by positivity) hn_pos ?_
          have h1 : n ≤ Mk k := Nat.le_mul_of_pos_right n hm_pos
          exact_mod_cast h1
        -- Choose `r : Fin (Mk k)` with `θ_r = 2π r / Mk k` satisfying `0 ≤ θ₀ - θ_r ≤ 2π / Mk k`
        -- (handling `θ₀ = 2π` by wrapping to `r = 0`, where `exp(i * 0) = exp(i * 2π)`)
        have hex_r : ∃ (r : Fin (Mk k)) (θ' : ℝ),
            Complex.exp (Complex.I * (θ' : ℂ)) = Complex.exp (Complex.I * (θ₀ : ℂ)) ∧
            2 * Real.pi * (r : ℝ) / (Mk k : ℝ) ≤ θ' ∧
            θ' - 2 * Real.pi * (r : ℝ) / (Mk k : ℝ) ≤ 2 * Real.pi / (Mk k : ℝ) ∧
            (∀ t ∈ Set.Icc (2 * Real.pi * (r : ℝ) / (Mk k : ℝ)) θ',
              ‖∑ j : Fin (n + 1), (j : ℂ) * ((f j : ℤ) : ℂ) *
                Complex.exp (Complex.I * (j : ℂ) * (t : ℂ))‖ ≤
              (2 : ℝ) ^ k * (n : ℝ) ^ ((3 : ℝ) / 2)) ∧
            (k = 0 ∨ ∃ t ∈ Set.Icc (2 * Real.pi * (r : ℝ) / (Mk k : ℝ) - 4 * Real.pi / (n : ℝ))
                (2 * Real.pi * (r : ℝ) / (Mk k : ℝ) + 4 * Real.pi / (n : ℝ)),
              (2 : ℝ) ^ (k - 1) * (n : ℝ) ^ ((3 : ℝ) / 2) <
                ‖∑ j : Fin (n + 1), (j : ℂ) * ((f j : ℤ) : ℂ) *
                  Complex.exp (Complex.I * (j : ℂ) * (t : ℂ))‖) := by
          have hper : ∀ (t : ℝ),
              ‖∑ j : Fin (n + 1), (j : ℂ) * ((f j : ℤ) : ℂ) *
                Complex.exp (Complex.I * (j : ℂ) * ((t - 2 * Real.pi : ℝ) : ℂ))‖ =
              ‖∑ j : Fin (n + 1), (j : ℂ) * ((f j : ℤ) : ℂ) *
                Complex.exp (Complex.I * (j : ℂ) * (t : ℂ))‖ := by
            intro t
            congr 1
            refine Finset.sum_congr rfl fun j _ => ?_
            congr 1
            have hexp : Complex.I * (j : ℂ) * ((t - 2 * Real.pi : ℝ) : ℂ) =
                Complex.I * (j : ℂ) * (t : ℂ) + (((-((j : ℕ) : ℤ) : ℤ) : ℂ)) * (2 * (Real.pi : ℂ) * Complex.I) := by
              push_cast; ring
            rw [hexp, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
          have hmin_k : k = 0 ∨ ∃ t ∈ Set.Icc (θ₀ - 2 * Real.pi / (n : ℝ)) (θ₀ + 2 * Real.pi / (n : ℝ)),
              (2 : ℝ) ^ (k - 1) * (n : ℝ) ^ ((3 : ℝ) / 2) <
                ‖∑ j : Fin (n + 1), (j : ℂ) * ((f j : ℤ) : ℂ) *
                  Complex.exp (Complex.I * (j : ℂ) * (t : ℂ))‖ := by
            by_cases hk0 : k = 0
            · exact Or.inl hk0
            · right
              have hnot : ¬ Pscale (k - 1) := Nat.find_min hex (by omega)
              dsimp [Pscale] at hnot
              push Not at hnot
              exact hnot
          by_cases htop : θ₀ = 2 * Real.pi
          · refine ⟨⟨0, hM_pos⟩, 0, ?_, by simp, by simp; positivity, ?_, ?_⟩
            · rw [htop]
              have h2pi : Complex.I * ((2 * Real.pi : ℝ) : ℂ) = 2 * (Real.pi : ℂ) * Complex.I := by
                push_cast; ring
              rw [h2pi, Complex.exp_two_pi_mul_I]
              simp
            · intro t ht
              simp only [Nat.cast_zero, mul_zero, zero_div, Set.mem_Icc] at ht
              have ht0 : t = 0 := le_antisymm ht.2 ht.1
              subst ht0
              have h2pi_mem : 2 * Real.pi ∈ Set.Icc (θ₀ - 2 * Real.pi / (n : ℝ)) (θ₀ + 2 * Real.pi / (n : ℝ)) := by
                rw [htop]
                exact ⟨by linarith [div_pos (mul_pos two_pos Real.pi_pos) hn_pos],
                       by linarith [div_pos (mul_pos two_pos Real.pi_pos) hn_pos]⟩
              have h0 := hper (2 * Real.pi)
              rw [sub_self] at h0
              rw [h0]
              exact hk_spec (2 * Real.pi) h2pi_mem
            · rcases hmin_k with hk0 | ⟨t, ht_mem, ht_gt⟩
              · exact Or.inl hk0
              · right
                refine ⟨t - 2 * Real.pi, ?_, ?_⟩
                · simp only [Nat.cast_zero, mul_zero, zero_div, zero_sub, zero_add, Set.mem_Icc]
                  rw [htop] at ht_mem
                  have h42 : 4 * Real.pi / (n : ℝ) = 2 * (2 * Real.pi / (n : ℝ)) := by ring
                  exact ⟨by linarith [ht_mem.1, div_pos (mul_pos two_pos Real.pi_pos) hn_pos, h42],
                         by linarith [ht_mem.2, div_pos (mul_pos two_pos Real.pi_pos) hn_pos, h42]⟩
                · rwa [hper t]
          · have hlt : θ₀ < 2 * Real.pi := lt_of_le_of_ne hθ₀_mem.2 htop
            let idx : ℕ := Nat.floor (θ₀ * (Mk k : ℝ) / (2 * Real.pi))
            have hfrac_nn : 0 ≤ θ₀ * (Mk k : ℝ) / (2 * Real.pi) := by
              have := hθ₀_mem.1; positivity
            have hfrac_lt : θ₀ * (Mk k : ℝ) / (2 * Real.pi) < (Mk k : ℝ) := by
              rw [div_lt_iff₀ (by positivity)]
              nlinarith [Real.pi_pos]
            have hidx_lt : idx < Mk k := by
              have hle : (idx : ℝ) ≤ θ₀ * (Mk k : ℝ) / (2 * Real.pi) := Nat.floor_le hfrac_nn
              exact_mod_cast (lt_of_le_of_lt hle hfrac_lt)
            let r : Fin (Mk k) := ⟨idx, hidx_lt⟩
            have hr_le : 2 * Real.pi * (r : ℝ) / (Mk k : ℝ) ≤ θ₀ := by
              have hle : (idx : ℝ) ≤ θ₀ * (Mk k : ℝ) / (2 * Real.pi) := Nat.floor_le hfrac_nn
              rw [div_le_iff₀ hM_real_pos]
              have hmul := (le_div_iff₀ (show (0 : ℝ) < 2 * Real.pi by positivity)).mp hle
              dsimp [r]; linarith
            have hr_close : θ₀ - 2 * Real.pi * (r : ℝ) / (Mk k : ℝ) ≤ 2 * Real.pi / (Mk k : ℝ) := by
              have hlt1 : θ₀ * (Mk k : ℝ) / (2 * Real.pi) < (idx : ℝ) + 1 := Nat.lt_floor_add_one _
              have hmul := (div_lt_iff₀ (show (0 : ℝ) < 2 * Real.pi by positivity)).mp hlt1
              rw [sub_le_iff_le_add, ← add_div, le_div_iff₀ hM_real_pos]
              dsimp [r]; linarith
            refine ⟨r, θ₀, rfl, hr_le, hr_close, ?_, ?_⟩
            · intro t ht
              refine hk_spec t ⟨?_, ?_⟩
              · linarith [ht.1, hr_close, hstep_le_arc]
              · linarith [ht.2, div_pos (mul_pos two_pos Real.pi_pos) hn_pos]
            · rcases hmin_k with hk0 | ⟨t, ht_mem, ht_gt⟩
              · exact Or.inl hk0
              · right
                have h42 : 4 * Real.pi / (n : ℝ) = 2 * (2 * Real.pi / (n : ℝ)) := by ring
                refine ⟨t, ⟨?_, ?_⟩, ht_gt⟩
                · linarith [ht_mem.1, hr_le, div_pos (mul_pos two_pos Real.pi_pos) hn_pos, h42]
                · linarith [ht_mem.2, hr_close, hstep_le_arc, h42]
        obtain ⟨r, θ', hexp', hr_le, hr_close, hder_sub, hmin_r⟩ := hex_r
        refine ⟨r, ?_, hmin_r⟩
        have hmvt := eval_exp_sub_norm_le f hr_le hder_sub
        have hdiff_le : (2 : ℝ) ^ k * (n : ℝ) ^ ((3 : ℝ) / 2) *
            (θ' - 2 * Real.pi * (r : ℝ) / (Mk k : ℝ)) ≤ ε / Real.sqrt n := by
          have h1 : (2 : ℝ) ^ k * (n : ℝ) ^ ((3 : ℝ) / 2) *
              (θ' - 2 * Real.pi * (r : ℝ) / (Mk k : ℝ)) ≤
              (2 : ℝ) ^ k * (n : ℝ) ^ ((3 : ℝ) / 2) * (ε / ((2 : ℝ) ^ k * (n : ℝ) ^ 2)) :=
            mul_le_mul_of_nonneg_left (hr_close.trans hstep_le) (by positivity)
          have h2 : (2 : ℝ) ^ k * (n : ℝ) ^ ((3 : ℝ) / 2) *
              (ε / ((2 : ℝ) ^ k * (n : ℝ) ^ 2)) = ε / Real.sqrt n := by
            have hpow32 : (n : ℝ) ^ ((3 : ℝ) / 2) = (n : ℝ) * Real.sqrt (n : ℝ) := by
              rw [Real.sqrt_eq_rpow, ← Real.rpow_one_add' hn_pos.le (by norm_num)]
              norm_num
            have hsqrt_ne : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hn_pos).ne'
            have hsq : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) :=
              Real.mul_self_sqrt hn_pos.le
            rw [hpow32]
            field_simp [hn_pos.ne', hsqrt_ne, pow_ne_zero k (two_ne_zero : (2 : ℝ) ≠ 0)]
            nlinarith [hsq]
          linarith
        have htri : ‖Erdos525.eval f (Complex.exp (Complex.I * (2 * Real.pi * (r : ℝ) / (Mk k : ℝ))))‖ ≤
            ‖Erdos525.eval f (Complex.exp (Complex.I * (2 * Real.pi * (r : ℝ) / (Mk k : ℝ)))) -
              Erdos525.eval f (Complex.exp (Complex.I * (θ' : ℂ)))‖ +
            ‖Erdos525.eval f (Complex.exp (Complex.I * (θ' : ℂ)))‖ := by
          simpa using norm_add_le
            (Erdos525.eval f (Complex.exp (Complex.I * (2 * Real.pi * (r : ℝ) / (Mk k : ℝ)))) -
              Erdos525.eval f (Complex.exp (Complex.I * (θ' : ℂ))))
            (Erdos525.eval f (Complex.exp (Complex.I * (θ' : ℂ))))
        have hcast : Complex.exp (Complex.I * (2 * Real.pi * (r : ℝ) / (Mk k : ℝ))) =
            Complex.exp (Complex.I * ((2 * Real.pi * (r : ℝ) / (Mk k : ℝ) : ℝ) : ℂ)) := by
          push_cast; rfl
        rw [hcast]
        rw [hcast] at htri
        rw [hexp'] at htri hmvt
        have h2e : 2 * ε / Real.sqrt n = ε / Real.sqrt n + ε / Real.sqrt n := by ring
        linarith
      · right
        dsimp [Pscale] at hPK
        push Not at hPK
        exact ⟨θ₀, hθ₀_mem, hθ₀_le, hPK⟩
    -- Apply finite union bounds
    have hprob1 : Erdos525.prob n (fun f => Erdos525.m f ≤ ε / Real.sqrt n) ≤
        Erdos525.prob n (fun f => ∃ k ∈ Finset.range (K + 1), E_scale k f) +
        Erdos525.prob n E_tail :=
      (prob_mono hcover).trans (prob_or_le _ _)
    have hprob2 : Erdos525.prob n (fun f => ∃ k ∈ Finset.range (K + 1), E_scale k f) ≤
        ∑ k ∈ Finset.range (K + 1), Erdos525.prob n (E_scale k) :=
      prob_exists_finset_le _ _
    have hprob3 : ∑ k ∈ Finset.range (K + 1), Erdos525.prob n (E_scale k) ≤
        ∑ k ∈ Finset.range (K + 1), C₁ * ε / (2 : ℝ) ^ k := by
      refine Finset.sum_le_sum fun k hk => ?_
      have hscale_union : Erdos525.prob n (E_scale k) ≤
          ∑ r : Fin (Mk k),
            Erdos525.prob n (fun f =>
              ‖Erdos525.eval f (Complex.exp (Complex.I * (2 * Real.pi * (r : ℝ) / (Mk k : ℝ))))‖ ≤
                2 * ε / Real.sqrt n ∧
              (k = 0 ∨ ∃ t ∈ Set.Icc (2 * Real.pi * (r : ℝ) / (Mk k : ℝ) - 4 * Real.pi / (n : ℝ))
                  (2 * Real.pi * (r : ℝ) / (Mk k : ℝ) + 4 * Real.pi / (n : ℝ)),
                (2 : ℝ) ^ (k - 1) * (n : ℝ) ^ ((3 : ℝ) / 2) <
                  ‖∑ j : Fin (n + 1), (j : ℂ) * ((f j : ℤ) : ℂ) *
                    Complex.exp (Complex.I * (j : ℂ) * (t : ℂ))‖)) := by
        have := prob_exists_finset_le (Finset.univ : Finset (Fin (Mk k)))
          (fun r f =>
            ‖Erdos525.eval f (Complex.exp (Complex.I * (2 * Real.pi * (r : ℝ) / (Mk k : ℝ))))‖ ≤
              2 * ε / Real.sqrt n ∧
            (k = 0 ∨ ∃ t ∈ Set.Icc (2 * Real.pi * (r : ℝ) / (Mk k : ℝ) - 4 * Real.pi / (n : ℝ))
                (2 * Real.pi * (r : ℝ) / (Mk k : ℝ) + 4 * Real.pi / (n : ℝ)),
              (2 : ℝ) ^ (k - 1) * (n : ℝ) ^ ((3 : ℝ) / 2) <
                ‖∑ j : Fin (n + 1), (j : ℂ) * ((f j : ℤ) : ℂ) *
                  Complex.exp (Complex.I * (j : ℂ) * (t : ℂ))‖))
        exact (prob_mono fun f ⟨r, hr⟩ => ⟨r, Finset.mem_univ r, hr⟩).trans this
      exact hscale_union.trans (h1_n k hk)
    have hgeom : ∑ k ∈ Finset.range (K + 1), C₁ * ε / (2 : ℝ) ^ k ≤ 2 * C₁ * ε := by
      have hfac : ∑ k ∈ Finset.range (K + 1), C₁ * ε / (2 : ℝ) ^ k =
          (C₁ * ε) * ∑ k ∈ Finset.range (K + 1), (1 : ℝ) / (2 : ℝ) ^ k := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => by ring
      rw [hfac]
      have hle := mul_le_mul_of_nonneg_left (sum_inv_pow_two_le K) (by positivity : (0 : ℝ) ≤ C₁ * ε)
      linarith
    have htot : Erdos525.prob n (fun f => Erdos525.m f ≤ ε / Real.sqrt n) ≤
        (2 * C₁ + 1) * ε := by
      linarith [hprob1, hprob2, hprob3, hgeom, hK_n]
    exact htot.trans (mul_le_mul_of_nonneg_right hC_ge2 hε.le)

end OMA.R_Erdos525_erdos_525_variants_konyagin_schlag_R1
