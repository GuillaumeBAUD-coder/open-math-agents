import FormalConjectures.Arxiv.«2406.10319».StableMatchingHyperbola
import Mathlib.Tactic
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.MeasureTheory.Integral.Pi

-- Reduction Arxiv.2406.10319.pittel_hyperbola_threshold.R1 of Pittel's stable-matching hyperbola threshold conjecture
-- Credit: @tatashbar
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- The reduction fixes the threshold: pStar n = ((9/4) (log n)^2 + 1) / n, an exact closed form.
-- The summand 1/n gives the strict bound (9/4) (log n)^2 / n < pStar n. It is harmless: a sharp
-- threshold with relative margin delta is only determined up to a factor 1 + o(1).
-- Reason for the constant: at p = c (log n)^2 / n with c > 1 the scaled wife ranks of the stable
-- matchings should fill the interval [c^(-1/2), c^(1/2)] (heuristic and simulation), so the arc
-- t in [2/3, 3/2] is covered exactly when c >= 9/4.
--
-- H1 (above the threshold) is open. It is known only at p = 1 (Pittel, Ann. Appl. Probab. 2 (1992)).
-- H2 (range 1/n <= p <= (9/4)(1-eta)(log n)^2/n) is open. Pittel, arXiv 2406.10319, Theorem 1.6
-- gives it for p = c (log n)^2 / n with a fixed c < 1 only.
-- The range p <= 1/n is proved here (sparse_tendsto): a total wife rank is at most the number of
-- admissible pairs, and Chebyshev's inequality bounds that number.
-- H1 and H2 are unproved, and together they are stronger than the original statement.

open Filter MeasureTheory StableMarriage ProbabilityTheory
open scoped Topology

namespace OMA.R_Arxiv_2406_10319_pittel_hyperbola_threshold_R1

open Arxiv.«2406.10319»

lemma hyperbolaEvent_mono (n : ℕ) (p : unitInterval) {ε ε' : ℝ} (h : ε ≤ ε') :
    hyperbolaEvent n p ε ⊆ hyperbolaEvent n p ε' := by
  intro ω hω
  obtain ⟨hn, hp, h1, h2⟩ := hω
  refine ⟨hn, hp, fun M hM => (h1 M hM).trans h, fun t ht => ?_⟩
  obtain ⟨M, hM, hb⟩ := h2 t ht
  exact ⟨M, hM, hb.trans h⟩

lemma wifeRank_le {n : ℕ} (P : Profile n) (A : Admissibility n) (m w : Fin n)
    (h : A (m, w) = true) :
    wifeRank P A m w ≤ (Finset.univ.filter fun v : Fin n => A (m, v) = true).card := by
  unfold wifeRank
  have hw : w ∉ Finset.univ.filter
      (fun v : Fin n => A (m, v) = true ∧ P.manRank m v < P.manRank m w) := by
    simp
  have hsub : insert w (Finset.univ.filter
      (fun v : Fin n => A (m, v) = true ∧ P.manRank m v < P.manRank m w)) ⊆
      Finset.univ.filter (fun v : Fin n => A (m, v) = true) := by
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · simp [h]
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
      exact hv.1
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hw] at hcard
  omega

lemma totalWifeRank_le {n : ℕ} (P : Profile n) (A : Admissibility n) (M : PartialMatching n)
    (hM : IsPartialStable P A M) :
    totalWifeRank P A M ≤ (Finset.univ.filter fun e : Fin n × Fin n => A e = true).card := by
  unfold totalWifeRank
  calc ∑ e ∈ M.pairs, wifeRank P A e.1 e.2
      ≤ ∑ e ∈ M.pairs, (Finset.univ.filter fun v : Fin n => A (e.1, v) = true).card :=
        Finset.sum_le_sum fun e he => wifeRank_le P A e.1 e.2 (hM.1 e he)
    _ = ∑ m ∈ M.pairs.image Prod.fst,
          (Finset.univ.filter fun v : Fin n => A (m, v) = true).card :=
        (Finset.sum_image
          (f := fun m : Fin n => (Finset.univ.filter fun v : Fin n => A (m, v) = true).card)
          (fun x hx y hy hxy => M.left_inj hx hy hxy)).symm
    _ ≤ ∑ m : Fin n, (Finset.univ.filter fun v : Fin n => A (m, v) = true).card :=
        Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    _ = (Finset.univ.filter fun e : Fin n × Fin n => A e = true).card := by
        simp only [Finset.card_filter]
        rw [Fintype.sum_prod_type]

lemma totalWifeRank_le_real {n : ℕ} (P : Profile n) (A : Admissibility n)
    (M : PartialMatching n) (hM : IsPartialStable P A M) :
    (totalWifeRank P A M : ℝ) ≤ ∑ e : Fin n × Fin n, (if A e = true then (1 : ℝ) else 0) := by
  have h := totalWifeRank_le P A M hM
  have h2 : ((Finset.univ.filter fun e : Fin n × Fin n => A e = true).card : ℝ)
      = ∑ e : Fin n × Fin n, (if A e = true then (1 : ℝ) else 0) := by
    simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [← h2]
  exact_mod_cast h

lemma integral_bern (p : unitInterval) :
    ∫ b : Bool, (if b = true then (1 : ℝ) else 0) ∂(bernoulliMeasure true false p) = p := by
  rw [integral_bernoulliMeasure]
  simp

lemma variance_bern_le (p : unitInterval) :
    variance (fun b : Bool => if b = true then (1 : ℝ) else 0) (bernoulliMeasure true false p)
      ≤ p := by
  have h := variance_le_sub_mul_sub (μ := bernoulliMeasure true false p) (a := 0) (b := 1)
    (X := fun b : Bool => if b = true then (1 : ℝ) else 0)
    (Eventually.of_forall fun b => by cases b <;> simp) (measurable_of_finite _).aemeasurable
  rw [integral_bern] at h
  have hp0 := p.2.1
  have hp1 := p.2.2
  nlinarith

lemma integral_count (n : ℕ) (p : unitInterval) :
    ∫ A : Admissibility n, ∑ e : Fin n × Fin n, (if A e = true then (1 : ℝ) else 0)
      ∂(Admissibility.law n p) = (n : ℝ) ^ 2 * p := by
  unfold Admissibility.law
  rw [integral_finsetSum _ (fun e _ => Integrable.of_finite)]
  have h : ∀ e : Fin n × Fin n,
      ∫ A : Admissibility n, (if A e = true then (1 : ℝ) else 0)
        ∂(Measure.pi fun _ : Fin n × Fin n => bernoulliMeasure true false p) = p := by
    intro e
    rw [integral_comp_eval (μ := fun _ : Fin n × Fin n => bernoulliMeasure true false p)
      (i := e) (f := fun b : Bool => if b = true then (1 : ℝ) else 0)
      (measurable_of_finite _).aestronglyMeasurable]
    exact integral_bern p
  rw [Finset.sum_congr rfl (fun e _ => h e)]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_mul]
  ring

lemma variance_count_le (n : ℕ) (p : unitInterval) :
    variance (fun A : Admissibility n =>
      ∑ e : Fin n × Fin n, (if A e = true then (1 : ℝ) else 0)) (Admissibility.law n p)
      ≤ (n : ℝ) ^ 2 * p := by
  unfold Admissibility.law
  have hsum := variance_sum_pi (μ := fun _ : Fin n × Fin n => bernoulliMeasure true false p)
    (X := fun _ (b : Bool) => if b = true then (1 : ℝ) else 0) (fun _ => MemLp.of_discrete)
  have hfun : (fun A : Admissibility n =>
      ∑ e : Fin n × Fin n, (if A e = true then (1 : ℝ) else 0))
      = ∑ e : Fin n × Fin n, fun A : (Fin n × Fin n) → Bool =>
          (if A e = true then (1 : ℝ) else 0) := by
    funext A
    simp only [Finset.sum_apply]
  rw [hfun, hsum]
  calc ∑ e : Fin n × Fin n,
        variance (fun b : Bool => if b = true then (1 : ℝ) else 0) (bernoulliMeasure true false p)
      ≤ ∑ _e : Fin n × Fin n, (p : ℝ) := Finset.sum_le_sum fun e _ => variance_bern_le p
    _ = (n : ℝ) ^ 2 * p := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
          nsmul_eq_mul, Nat.cast_mul]
        ring

/-- For $p \le 1/n$ the hyperbola event at tolerance $1/4$ has probability at most $16/n$. -/
lemma sparse_bound (n : ℕ) (hn : 0 < n) (p : unitInterval) (hp : (p : ℝ) ≤ 1 / n) :
    marketLaw n p (hyperbolaEvent n p (1 / 4)) ≤ ENNReal.ofReal (16 / n) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  by_cases hp0 : (p : ℝ) = 0
  · have hempty : hyperbolaEvent n p (1 / 4) ⊆ ∅ := by
      intro ω hω
      obtain ⟨_, hpos, _, _⟩ := hω
      rw [hp0] at hpos
      exact absurd hpos (lt_irrefl _)
    exact (measure_mono hempty).trans (by simp)
  have hppos : 0 < (p : ℝ) := lt_of_le_of_ne p.2.1 (Ne.symm hp0)
  have hnp : (n : ℝ) * p ≤ 1 := by
    have h := (le_div_iff₀ hn').mp hp
    linarith
  have hs2 : Real.sqrt ((p : ℝ) * (n : ℝ) ^ 3) ^ 2 = (p : ℝ) * (n : ℝ) ^ 3 :=
    Real.sq_sqrt (by positivity)
  have hs : 0 < Real.sqrt ((p : ℝ) * (n : ℝ) ^ 3) := Real.sqrt_pos.mpr (by positivity)
  have hmu : (n : ℝ) ^ 2 * p ≤ Real.sqrt ((p : ℝ) * (n : ℝ) ^ 3) := by
    have hle : ((n : ℝ) ^ 2 * p) ^ 2 ≤ (p : ℝ) * (n : ℝ) ^ 3 := by
      have h1 : ((n : ℝ) ^ 2 * p) ^ 2 = ((p : ℝ) * (n : ℝ) ^ 3) * ((n : ℝ) * p) := by ring
      rw [h1]
      have h2 : 0 ≤ (p : ℝ) * (n : ℝ) ^ 3 := by positivity
      nlinarith
    calc (n : ℝ) ^ 2 * p = Real.sqrt (((n : ℝ) ^ 2 * p) ^ 2) :=
          (Real.sqrt_sq (by positivity)).symm
      _ ≤ Real.sqrt ((p : ℝ) * (n : ℝ) ^ 3) := Real.sqrt_le_sqrt hle
  have hsub : hyperbolaEvent n p (1 / 4) ⊆ Prod.snd ⁻¹' {A : Admissibility n |
      Real.sqrt ((p : ℝ) * (n : ℝ) ^ 3) / 4 ≤
        |(∑ e : Fin n × Fin n, (if A e = true then (1 : ℝ) else 0)) -
          ∫ A' : Admissibility n, ∑ e : Fin n × Fin n, (if A' e = true then (1 : ℝ) else 0)
            ∂(Admissibility.law n p)|} := by
    intro ω hω
    obtain ⟨_, _, _, hcov⟩ := hω
    obtain ⟨M, hM, hb⟩ := hcov (3 / 2) ⟨by norm_num, le_rfl⟩
    have hq : |(totalWifeRank ω.1 ω.2 M : ℝ) / Real.sqrt ((p : ℝ) * (n : ℝ) ^ 3) - 3 / 2|
        ≤ 1 / 4 := (le_max_left _ _).trans hb
    have h2 : 5 / 4 ≤ (totalWifeRank ω.1 ω.2 M : ℝ) / Real.sqrt ((p : ℝ) * (n : ℝ) ^ 3) := by
      have h3 := (abs_le.mp hq).1
      linarith
    rw [le_div_iff₀ hs] at h2
    have hN := totalWifeRank_le_real ω.1 ω.2 M hM
    show Real.sqrt ((p : ℝ) * (n : ℝ) ^ 3) / 4 ≤
      |(∑ e : Fin n × Fin n, (if ω.2 e = true then (1 : ℝ) else 0)) -
        ∫ A' : Admissibility n, ∑ e : Fin n × Fin n, (if A' e = true then (1 : ℝ) else 0)
          ∂(Admissibility.law n p)|
    rw [integral_count, le_abs]
    left
    linarith
  obtain ⟨C, hC⟩ := Finite.exists_le (fun A : Admissibility n =>
    ‖∑ e : Fin n × Fin n, (if A e = true then (1 : ℝ) else 0)‖)
  have hmem : MemLp (fun A : Admissibility n =>
      ∑ e : Fin n × Fin n, (if A e = true then (1 : ℝ) else 0)) 2 (Admissibility.law n p) :=
    MemLp.of_bound (measurable_of_finite _).aestronglyMeasurable C (Eventually.of_forall hC)
  have hc : 0 < Real.sqrt ((p : ℝ) * (n : ℝ) ^ 3) / 4 := by positivity
  have hcheb := meas_ge_le_variance_div_sq hmem hc
  have hmeas : MeasurableSet {A : Admissibility n |
      Real.sqrt ((p : ℝ) * (n : ℝ) ^ 3) / 4 ≤
        |(∑ e : Fin n × Fin n, (if A e = true then (1 : ℝ) else 0)) -
          ∫ A' : Admissibility n, ∑ e : Fin n × Fin n, (if A' e = true then (1 : ℝ) else 0)
            ∂(Admissibility.law n p)|} := (Set.toFinite _).measurableSet
  have hprod : marketLaw n p (Prod.snd ⁻¹' {A : Admissibility n |
      Real.sqrt ((p : ℝ) * (n : ℝ) ^ 3) / 4 ≤
        |(∑ e : Fin n × Fin n, (if A e = true then (1 : ℝ) else 0)) -
          ∫ A' : Admissibility n, ∑ e : Fin n × Fin n, (if A' e = true then (1 : ℝ) else 0)
            ∂(Admissibility.law n p)|}) = (Admissibility.law n p) {A : Admissibility n |
      Real.sqrt ((p : ℝ) * (n : ℝ) ^ 3) / 4 ≤
        |(∑ e : Fin n × Fin n, (if A e = true then (1 : ℝ) else 0)) -
          ∫ A' : Admissibility n, ∑ e : Fin n × Fin n, (if A' e = true then (1 : ℝ) else 0)
            ∂(Admissibility.law n p)|} := by
    unfold marketLaw
    rw [← Measure.map_apply measurable_snd hmeas, Measure.map_snd_prod, measure_univ, one_smul]
  have hratio : variance (fun A : Admissibility n =>
      ∑ e : Fin n × Fin n, (if A e = true then (1 : ℝ) else 0)) (Admissibility.law n p) /
      (Real.sqrt ((p : ℝ) * (n : ℝ) ^ 3) / 4) ^ 2 ≤ 16 / n := by
    have hv := variance_count_le n p
    rw [div_le_div_iff₀ (by positivity) hn']
    have h16 : 16 * (Real.sqrt ((p : ℝ) * (n : ℝ) ^ 3) / 4) ^ 2 = (p : ℝ) * (n : ℝ) ^ 3 :=
      calc 16 * (Real.sqrt ((p : ℝ) * (n : ℝ) ^ 3) / 4) ^ 2
          = Real.sqrt ((p : ℝ) * (n : ℝ) ^ 3) ^ 2 := by ring
        _ = (p : ℝ) * (n : ℝ) ^ 3 := hs2
    rw [h16]
    nlinarith
  calc marketLaw n p (hyperbolaEvent n p (1 / 4))
      ≤ marketLaw n p (Prod.snd ⁻¹' {A : Admissibility n |
          Real.sqrt ((p : ℝ) * (n : ℝ) ^ 3) / 4 ≤
            |(∑ e : Fin n × Fin n, (if A e = true then (1 : ℝ) else 0)) -
              ∫ A' : Admissibility n, ∑ e : Fin n × Fin n, (if A' e = true then (1 : ℝ) else 0)
                ∂(Admissibility.law n p)|}) := measure_mono hsub
    _ ≤ ENNReal.ofReal (variance (fun A : Admissibility n =>
          ∑ e : Fin n × Fin n, (if A e = true then (1 : ℝ) else 0)) (Admissibility.law n p) /
          (Real.sqrt ((p : ℝ) * (n : ℝ) ^ 3) / 4) ^ 2) := by
        rw [hprod]
        exact hcheb
    _ ≤ ENNReal.ofReal (16 / n) := ENNReal.ofReal_le_ofReal hratio

/-- Sparse range: for $p \le 1/n$ the hyperbola event at tolerance $1/4$ fails with high
probability, uniformly in $p$. -/
lemma sparse_tendsto : Tendsto (fun n : ℕ ↦
    ⨆ p : {p : unitInterval // (p : ℝ) ≤ 1 / n},
      marketLaw n p.1 (hyperbolaEvent n p.1 (1 / 4))) atTop (𝓝 0) := by
  have h16 : Tendsto (fun n : ℕ => ENNReal.ofReal (16 / (n : ℝ))) atTop (𝓝 0) := by
    have h : Tendsto (fun n : ℕ => (16 : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat 16
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using
      (ENNReal.continuous_ofReal.tendsto 0).comp h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h16
    (Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  exact iSup_le fun p => sparse_bound n hn p.1 p.2

/-- Above the threshold: for $p \ge \frac94(1+\eta)(\log n)^2/n$ the hyperbola event holds with
high probability, uniformly in $p$, at every tolerance. -/
def H1 : Prop := ∀ η > (0 : ℝ), ∀ ε > (0 : ℝ), Tendsto (fun n : ℕ ↦
    ⨆ p : {p : unitInterval // (9 / 4 : ℝ) * (1 + η) * (Real.log n) ^ 2 / n ≤ (p : ℝ)},
      marketLaw n p.1 (hyperbolaEvent n p.1 ε)ᶜ) atTop (𝓝 0)

/-- Below the threshold: for $1/n \le p \le \frac94(1-\eta)(\log n)^2/n$ the hyperbola event fails
with high probability, uniformly in $p$, at one tolerance for each $\eta$. -/
def H2 : Prop := ∀ η ∈ Set.Ioo (0 : ℝ) 1, ∃ ε > (0 : ℝ), Tendsto (fun n : ℕ ↦
    ⨆ p : {p : unitInterval //
        1 / n ≤ (p : ℝ) ∧ (p : ℝ) ≤ (9 / 4 : ℝ) * (1 - η) * (Real.log n) ^ 2 / n},
      marketLaw n p.1 (hyperbolaEvent n p.1 ε)) atTop (𝓝 0)

theorem main : H1 → H2 → type_of% @Arxiv.«2406.10319».pittel_hyperbola_threshold := by
  intro h1 h3
  classical
  let a : ℕ → ℝ := fun n => ((9 / 4 : ℝ) * (Real.log n) ^ 2 + 1) / n
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have ha_tend : Tendsto a atTop (𝓝 0) := by
    have t1 : Tendsto (fun n : ℕ => (Real.log (n : ℝ)) ^ 2 / (n : ℝ)) atTop (𝓝 0) :=
      ((Real.isLittleO_pow_log_id_atTop (n := 2)).tendsto_div_nhds_zero).comp
        tendsto_natCast_atTop_atTop
    have t2 : Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_one_div_atTop_nhds_zero_nat
    have t3 := (t1.const_mul (9 / 4 : ℝ)).add t2
    simp only [mul_zero, add_zero] at t3
    refine t3.congr fun n => ?_
    simp only [a]
    ring
  have ha_ev : ∀ᶠ n in atTop, a n ∈ Set.Ioo (0 : ℝ) (1 / 2) := by
    have hlt : ∀ᶠ n in atTop, a n < 1 / 2 := ha_tend.eventually_lt_const (by norm_num)
    filter_upwards [hlt, eventually_gt_atTop 0] with n hn hn0
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
    exact ⟨div_pos (by positivity) hn', hn⟩
  have hhalf : (1 / 2 : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by constructor <;> norm_num
  let pStar : ℕ → Set.Ioo (0 : ℝ) 1 := fun n =>
    if h : a n ∈ Set.Ioo (0 : ℝ) (1 / 2) then ⟨a n, h.1, by linarith [h.2]⟩ else ⟨1 / 2, hhalf⟩
  refine ⟨pStar, ?_⟩
  intro d
  have hp_ev : ∀ᶠ n in atTop, (pStar n : ℝ) = a n ∧ d n = a n := by
    filter_upwards [ha_ev] with n hn
    have e1 : (pStar n : ℝ) = a n := by
      simp only [pStar, dif_pos hn]
    refine ⟨e1, ?_⟩
    show min (pStar n : ℝ) (1 - (pStar n : ℝ)) = a n
    rw [e1]
    exact min_eq_left (by linarith [hn.2])
  refine ⟨?_, ?_⟩
  · filter_upwards [hp_ev, eventually_gt_atTop 0] with n hn hn0
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
    rw [hn.1]
    have key : a n = (9 / 4 : ℝ) * (Real.log n) ^ 2 / n + 1 / n := by
      simp only [a]
      ring
    have : 0 < 1 / (n : ℝ) := by positivity
    linarith
  · intro δ hδ
    have hδ0 : 0 < δ := hδ.1
    refine ⟨fun ε hε => ?_, ?_⟩
    · have hH := h1 δ hδ0 ε hε
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hH
        (Eventually.of_forall fun _ => bot_le) ?_
      filter_upwards [hp_ev, eventually_gt_atTop 0] with n hn hn0
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
      refine iSup_le fun p => ?_
      have hp : a n + δ * a n ≤ (p.1 : ℝ) :=
        calc a n + δ * a n = (pStar n : ℝ) + δ * d n := by rw [hn.1, hn.2]
          _ ≤ (p.1 : ℝ) := p.2
      have key : a n + δ * a n = (9 / 4 : ℝ) * (1 + δ) * (Real.log n) ^ 2 / n + (1 + δ) / n := by
        simp only [a]
        ring
      have hpos : 0 ≤ (1 + δ) / (n : ℝ) := by positivity
      exact le_iSup_of_le
        (f := fun q : {q : unitInterval //
          (9 / 4 : ℝ) * (1 + δ) * (Real.log n) ^ 2 / n ≤ (q : ℝ)} =>
          marketLaw n q.1 (hyperbolaEvent n q.1 ε)ᶜ) ⟨p.1, by linarith⟩ le_rfl
    · have hT2 := sparse_tendsto
      obtain ⟨ε3, hε3, hT3⟩ := h3 (δ / 2) ⟨by linarith, by linarith [hδ.2]⟩
      refine ⟨min (1 / 4) ε3, lt_min (by norm_num) hε3, ?_⟩
      have hsum := hT2.add hT3
      rw [add_zero] at hsum
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
        (Eventually.of_forall fun _ => bot_le) ?_
      have hlog_ev : ∀ᶠ n : ℕ in atTop, 1 / δ ≤ Real.log (n : ℝ) :=
        hlog.eventually_ge_atTop (1 / δ)
      filter_upwards [hp_ev, eventually_gt_atTop 0, hlog_ev] with n hn hn0 hln
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
      refine iSup_le fun p => ?_
      have hp : (p.1 : ℝ) ≤ a n - δ * a n :=
        calc (p.1 : ℝ) ≤ (pStar n : ℝ) - δ * d n := p.2
          _ = a n - δ * a n := by rw [hn.1, hn.2]
      by_cases hc : (p.1 : ℝ) ≤ 1 / n
      · exact le_add_right (le_iSup_of_le
          (f := fun q : {q : unitInterval // (q : ℝ) ≤ 1 / n} =>
            marketLaw n q.1 (hyperbolaEvent n q.1 (1 / 4))) ⟨p.1, hc⟩
          (measure_mono (hyperbolaEvent_mono n p.1 (min_le_left _ _))))
      · have hx1 : 1 ≤ δ * Real.log n := by
          have h := mul_le_mul_of_nonneg_left hln hδ0.le
          rwa [mul_one_div_cancel hδ0.ne'] at h
        have hx2 : 1 ≤ Real.log (n : ℝ) := by
          refine le_trans ?_ hln
          rw [le_div_iff₀ hδ0]
          linarith [hδ.2]
        have hx3 : 1 ≤ δ * (Real.log n) ^ 2 := by nlinarith
        have key : (9 / 4 : ℝ) * (1 - δ / 2) * (Real.log n) ^ 2 / n - (a n - δ * a n)
            = ((9 / 8) * δ * (Real.log n) ^ 2 - (1 - δ)) / n := by
          simp only [a]
          ring
        have hnn : 0 ≤ ((9 / 8) * δ * (Real.log n) ^ 2 - (1 - δ)) / (n : ℝ) :=
          div_nonneg (by nlinarith) hn'.le
        exact le_add_left (le_iSup_of_le
          (f := fun q : {q : unitInterval // 1 / n ≤ (q : ℝ) ∧
            (q : ℝ) ≤ (9 / 4 : ℝ) * (1 - δ / 2) * (Real.log n) ^ 2 / n} =>
            marketLaw n q.1 (hyperbolaEvent n q.1 ε3)) ⟨p.1, (not_le.mp hc).le, by linarith⟩
          (measure_mono (hyperbolaEvent_mono n p.1 (min_le_right _ _))))

end OMA.R_Arxiv_2406_10319_pittel_hyperbola_threshold_R1
