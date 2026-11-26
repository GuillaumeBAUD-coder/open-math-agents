import FormalConjectures.ErdosProblems.«165»

/-!
# Proof of Erdős Problem 165 (Shearer's Upper Bound on `R(3, k)`)

We prove Shearer's 1983 theorem `R(3, k) ≤ (1 + ε) k² / log k` for all sufficiently large `k`:
1. Using the integral representation
   `shearerF d = ∫ t in 0..1, (1 - t) / (1 - t + d * t)` (with `shearerF 0 = 1`) and
   `shearerP d = -∫ t in 0..1, t * (1 - t) / (1 - t + d * t) ^ 2`,
   we establish without derivatives of `shearerF` that `shearerP d ≤ 0`, `shearerF` is antitone on
   `[0, ∞)`, satisfies the supporting-line bound `shearerF d + shearerP d * (y - d) ≤ shearerF y`
   for all `d > 0, y ≥ 0`, obeys Shearer's identity `(d + 1) * shearerF d - (d - d ^ 2) * shearerP d = 1`
   (by FTC on `t * (1 + d - t) / (1 - t + d * t)`), and equals `(d * log d - d + 1) / (d - 1) ^ 2`
   for `d > 1`.
2. By strong induction on vertex count, every nonempty triangle-free finite graph on `S` with
   average degree `d` contains an independent set of size at least `|S| * shearerF d`.
3. Applying this to any triangle-free graph on `N = ⌊(1 + ε) k² / log k⌋` vertices with no
   independent set of size `k` (hence `d ≤ k - 1 < k`) yields a contradiction for large `k`.
-/

-- Problem: Erdős Problem 165 — upper
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/165.lean:77 (declaration Erdos165.erdos_165.variants.upper)
-- Credit: @TheWaler (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace Erdos165UpperProof

open Filter MeasureTheory

open scoped Classical

private noncomputable def shearerF (d : ℝ) : ℝ :=
  if d = 0 then 1 else ∫ t in (0 : ℝ)..1, (1 - t) / (1 - t + d * t)

private noncomputable def shearerP (d : ℝ) : ℝ :=
  -∫ t in (0 : ℝ)..1, t * (1 - t) / (1 - t + d * t) ^ 2

private lemma denom_pos {d t : ℝ} (hd : 0 < d) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    0 < 1 - t + d * t := by
  by_cases h1 : t = 1
  · subst h1
    linarith
  · have hlt : t < 1 := lt_of_le_of_ne ht.2 h1
    have hdt : 0 ≤ d * t := mul_nonneg hd.le ht.1
    linarith

private lemma denom_ne_zero {d t : ℝ} (hd : 0 < d) (ht : t ∈ Set.uIcc (0 : ℝ) 1) :
    1 - t + d * t ≠ 0 := by
  rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
  exact (denom_pos hd ht).ne'

private lemma shearerF_integrable {d : ℝ} (hd : 0 < d) :
    IntervalIntegrable (fun t : ℝ => (1 - t) / (1 - t + d * t)) volume 0 1 := by
  refine ContinuousOn.intervalIntegrable ?_
  refine ContinuousOn.div (continuous_const.sub continuous_id).continuousOn ?_ (fun t ht =>
    denom_ne_zero hd ht)
  exact ((continuous_const.sub continuous_id).add (continuous_const.mul continuous_id)).continuousOn

private lemma shearerP_integrable {d : ℝ} (hd : 0 < d) :
    IntervalIntegrable (fun t : ℝ => t * (1 - t) / (1 - t + d * t) ^ 2) volume 0 1 := by
  refine ContinuousOn.intervalIntegrable ?_
  refine ContinuousOn.div (continuous_id.mul (continuous_const.sub continuous_id)).continuousOn ?_
    (fun t ht => pow_ne_zero 2 (denom_ne_zero hd ht))
  exact (((continuous_const.sub continuous_id).add
    (continuous_const.mul continuous_id)).pow 2).continuousOn

private lemma shearerF_zero : shearerF 0 = 1 := if_pos rfl

private lemma shearerF_of_pos {d : ℝ} (hd : 0 < d) :
    shearerF d = ∫ t in (0 : ℝ)..1, (1 - t) / (1 - t + d * t) :=
  if_neg hd.ne'

private lemma shearerP_nonpos (d : ℝ) : shearerP d ≤ 0 := by
  dsimp only [shearerP]
  have hnonneg : 0 ≤ ∫ t in (0 : ℝ)..1, t * (1 - t) / (1 - t + d * t) ^ 2 := by
    refine intervalIntegral.integral_nonneg (by norm_num : (0 : ℝ) ≤ 1) ?_
    intro t ht
    exact div_nonneg (mul_nonneg ht.1 (by linarith [ht.2])) (sq_nonneg _)
  linarith

private lemma shearerF_antitone {d₁ d₂ : ℝ} (hd₁ : 0 ≤ d₁) (hle : d₁ ≤ d₂) :
    shearerF d₂ ≤ shearerF d₁ := by
  by_cases h0 : d₁ = 0
  · subst h0
    rw [shearerF_zero]
    by_cases h2 : d₂ = 0
    · subst h2
      rw [shearerF_zero]
    · have hd₂ : 0 < d₂ := lt_of_le_of_ne hle (Ne.symm h2)
      rw [shearerF_of_pos hd₂]
      calc
        (∫ t in (0 : ℝ)..1, (1 - t) / (1 - t + d₂ * t))
            ≤ ∫ _t in (0 : ℝ)..1, (1 : ℝ) := by
              refine intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
                (shearerF_integrable hd₂) intervalIntegrable_const ?_
              intro t ht
              have hden : 0 < 1 - t + d₂ * t := denom_pos hd₂ ht
              rw [div_le_iff₀ hden]
              have hdt : 0 ≤ d₂ * t := mul_nonneg hd₂.le ht.1
              linarith
        _ = 1 := by simp
  · have hd₁' : 0 < d₁ := lt_of_le_of_ne hd₁ (Ne.symm h0)
    have hd₂' : 0 < d₂ := lt_of_lt_of_le hd₁' hle
    rw [shearerF_of_pos hd₁', shearerF_of_pos hd₂']
    refine intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
      (shearerF_integrable hd₂') (shearerF_integrable hd₁') ?_
    intro t ht
    have hden1 : 0 < 1 - t + d₁ * t := denom_pos hd₁' ht
    have hden_le : 1 - t + d₁ * t ≤ 1 - t + d₂ * t := by
      have : d₁ * t ≤ d₂ * t := mul_le_mul_of_nonneg_right hle ht.1
      linarith
    exact div_le_div_of_nonneg_left (by linarith [ht.2]) hden1 hden_le

private lemma shearerF_supporting {d y : ℝ} (hd : 0 < d) (hy : 0 ≤ y) :
    shearerF d + shearerP d * (y - d) ≤ shearerF y := by
  have hintF := shearerF_integrable hd
  have hintP := shearerP_integrable hd
  have hcomb : shearerF d + shearerP d * (y - d) =
      ∫ t in (0 : ℝ)..1,
        ((1 - t) / (1 - t + d * t) - (y - d) * (t * (1 - t) / (1 - t + d * t) ^ 2)) := by
    rw [shearerF_of_pos hd, shearerP]
    rw [intervalIntegral.integral_sub hintF (hintP.const_mul (y - d)),
      intervalIntegral.integral_const_mul]
    ring
  have hintL : IntervalIntegrable
      (fun t : ℝ => (1 - t) / (1 - t + d * t) - (y - d) * (t * (1 - t) / (1 - t + d * t) ^ 2))
      volume 0 1 :=
    hintF.sub (hintP.const_mul (y - d))
  rw [hcomb]
  by_cases hy0 : y = 0
  · subst hy0
    rw [shearerF_zero]
    calc
      (∫ t in (0 : ℝ)..1,
          ((1 - t) / (1 - t + d * t) - (0 - d) * (t * (1 - t) / (1 - t + d * t) ^ 2)))
          ≤ ∫ _t in (0 : ℝ)..1, (1 : ℝ) := by
            refine intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
              hintL intervalIntegrable_const ?_
            intro t ht
            have hA : 0 < 1 - t + d * t := denom_pos hd ht
            set A : ℝ := 1 - t + d * t
            have hA' : A ≠ 0 := hA.ne'
            have hdiff : (1 : ℝ) -
                ((1 - t) / A - (0 - d) * (t * (1 - t) / A ^ 2)) =
                (d * t) ^ 2 / A ^ 2 := by
              field_simp [hA']
              dsimp only [A]
              ring
            have hge : 0 ≤ (d * t) ^ 2 / A ^ 2 := div_nonneg (sq_nonneg _) (sq_nonneg _)
            linarith
      _ = 1 := by simp
  · have hy_pos : 0 < y := lt_of_le_of_ne hy (Ne.symm hy0)
    rw [shearerF_of_pos hy_pos]
    refine intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
      hintL (shearerF_integrable hy_pos) ?_
    intro t ht
    have hA : 0 < 1 - t + d * t := denom_pos hd ht
    have hB : 0 < 1 - t + y * t := denom_pos hy_pos ht
    set A : ℝ := 1 - t + d * t
    set B : ℝ := 1 - t + y * t
    have hA' : A ≠ 0 := hA.ne'
    have hB' : B ≠ 0 := hB.ne'
    have hdiff : (1 - t) / B -
        ((1 - t) / A - (y - d) * (t * (1 - t) / A ^ 2)) =
        (1 - t) * (t * (y - d)) ^ 2 / (A ^ 2 * B) := by
      field_simp [hA', hB']
      dsimp only [A, B]
      ring
    have hge : 0 ≤ (1 - t) * (t * (y - d)) ^ 2 / (A ^ 2 * B) :=
      div_nonneg (mul_nonneg (by linarith [ht.2]) (sq_nonneg _)) (mul_nonneg (sq_nonneg _) hB.le)
    linarith

private lemma shearer_ode {d : ℝ} (hd : 0 < d) :
    (d + 1) * shearerF d - (d - d ^ 2) * shearerP d = 1 := by
  have hintF := shearerF_integrable hd
  have hintP := shearerP_integrable hd
  have hlhs : (d + 1) * shearerF d - (d - d ^ 2) * shearerP d =
      ∫ t in (0 : ℝ)..1,
        ((d + 1) * ((1 - t) / (1 - t + d * t)) +
          (d - d ^ 2) * (t * (1 - t) / (1 - t + d * t) ^ 2)) := by
    rw [shearerF_of_pos hd, shearerP]
    rw [intervalIntegral.integral_add (hintF.const_mul (d + 1)) (hintP.const_mul (d - d ^ 2)),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    ring
  rw [hlhs]
  let H : ℝ → ℝ := fun t => t * (1 + d - t) / (1 - t + d * t)
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt H ((d + 1) * ((1 - t) / (1 - t + d * t)) +
        (d - d ^ 2) * (t * (1 - t) / (1 - t + d * t) ^ 2)) t := by
    intro t ht
    have hden : 1 - t + d * t ≠ 0 := denom_ne_zero hd ht
    have hnum : HasDerivAt (fun x : ℝ => x * (1 + d - x))
        (1 * (1 + d - t) + t * (0 - 1)) t :=
      (hasDerivAt_id t).mul ((hasDerivAt_const t (1 + d)).sub (hasDerivAt_id t))
    have hdenom : HasDerivAt (fun x : ℝ => 1 - x + d * x) (0 - 1 + d * 1) t :=
      ((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).add
        ((hasDerivAt_id t).const_mul d)
    have hq := hnum.div hdenom hden
    refine hq.congr_deriv ?_
    field_simp [hden]
    ring
  have hintH : IntervalIntegrable
      (fun t : ℝ => (d + 1) * ((1 - t) / (1 - t + d * t)) +
        (d - d ^ 2) * (t * (1 - t) / (1 - t + d * t) ^ 2)) volume 0 1 :=
    (hintF.const_mul (d + 1)).add (hintP.const_mul (d - d ^ 2))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hintH]
  dsimp only [H]
  field_simp [hd.ne']
  ring

private lemma shearerF_formula {d : ℝ} (hd : 1 < d) :
    shearerF d = (d * Real.log d - d + 1) / (d - 1) ^ 2 := by
  have hd0 : 0 < d := by linarith
  have hd1 : d - 1 ≠ 0 := by linarith
  rw [shearerF_of_pos hd0]
  let F : ℝ → ℝ := fun t => d / (d - 1) ^ 2 * Real.log (1 - t + d * t) - t / (d - 1)
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt F ((1 - t) / (1 - t + d * t)) t := by
    intro t ht
    have hden : 1 - t + d * t ≠ 0 := denom_ne_zero hd0 ht
    have hdenom : HasDerivAt (fun x : ℝ => 1 - x + d * x) (0 - 1 + d * 1) t :=
      ((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).add
        ((hasDerivAt_id t).const_mul d)
    have hlog : HasDerivAt (fun x : ℝ => Real.log (1 - x + d * x))
        ((0 - 1 + d * 1) / (1 - t + d * t)) t :=
      hdenom.log hden
    have hF : HasDerivAt F
        (d / (d - 1) ^ 2 * ((0 - 1 + d * 1) / (1 - t + d * t)) - 1 / (d - 1)) t :=
      (hlog.const_mul (d / (d - 1) ^ 2)).sub ((hasDerivAt_id t).div_const (d - 1))
    refine hF.congr_deriv ?_
    field_simp [hden, hd1]
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (shearerF_integrable hd0)]
  dsimp only [F]
  have h1 : (1 : ℝ) - 1 + d * 1 = d := by ring
  have h0 : (1 : ℝ) - 0 + d * 0 = 1 := by ring
  rw [h1, h0, Real.log_one]
  field_simp [hd1]
  ring

private def IsIndep {V : Type*} (G : SimpleGraph V) (I : Finset V) : Prop :=
  ∀ u ∈ I, ∀ w ∈ I, ¬ G.Adj u w

private noncomputable def degIn {V : Type*} (G : SimpleGraph V) (S : Finset V) (v : V) : ℕ :=
  (S.filter (G.Adj v)).card

private noncomputable def edgeSum {V : Type*} (G : SimpleGraph V) (S : Finset V) : ℕ :=
  ∑ v ∈ S, degIn G S v

private lemma degIn_eq_sum {V : Type*} (G : SimpleGraph V) (S : Finset V) (v : V) :
    degIn G S v = ∑ w ∈ S, if G.Adj v w then 1 else 0 := by
  rw [degIn, Finset.card_filter]

private lemma edgeSum_eq_sum {V : Type*} (G : SimpleGraph V) (S : Finset V) :
    edgeSum G S = ∑ a ∈ S, ∑ b ∈ S, if G.Adj a b then 1 else 0 := by
  simp [edgeSum, degIn_eq_sum]

private lemma edgeSum_sub_closedNbr {V : Type*} (G : SimpleGraph V)
    (htf : ∀ a b c : V, ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj a c))
    (S : Finset V) {v : V} (hv : v ∈ S) :
    edgeSum G (S \ insert v (S.filter (G.Adj v))) +
        2 * ∑ u ∈ S.filter (G.Adj v), degIn G S u =
      edgeSum G S := by
  let N : Finset V := S.filter (G.Adj v)
  let D : Finset V := insert v N
  let Sv : Finset V := S \ D
  let f : V → V → ℕ := fun a b => if G.Adj a b then 1 else 0
  have hv_not_N : v ∉ N := by
    simp only [N, Finset.mem_filter, not_and]
    exact fun _ h => G.loopless.irrefl v h
  have hD_sub : D ⊆ S := by
    intro x hx
    simp only [D, N, Finset.mem_insert, Finset.mem_filter] at hx
    rcases hx with rfl | ⟨hxS, _⟩
    · exact hv
    · exact hxS
  have hdisj : Disjoint Sv D := Finset.sdiff_disjoint
  have hunion : Sv ∪ D = S := Finset.sdiff_union_of_subset hD_sub
  have hf_symm : ∀ a b, f a b = f b a := by
    intro a b
    simp only [f]
    by_cases h : G.Adj a b
    · simp [h, h.symm]
    · have h' : ¬ G.Adj b a := fun hba => h hba.symm
      simp [h, h']
  have hSvD_eq : (∑ a ∈ Sv, ∑ b ∈ D, f a b) = ∑ a ∈ D, ∑ b ∈ Sv, f a b := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => hf_symm b a
  have hDD : (∑ a ∈ D, ∑ b ∈ D, f a b) = 2 * degIn G S v := by
    have hD_split : ∀ g : V → ℕ, ∑ x ∈ D, g x = g v + ∑ x ∈ N, g x :=
      fun g => Finset.sum_insert hv_not_N
    rw [hD_split]
    have hvv : f v v = 0 := by simp [f]
    have hvN : (∑ b ∈ N, f v b) = degIn G S v := by
      have : ∀ b ∈ N, f v b = 1 := fun b hb => by
        simp [f, (Finset.mem_filter.mp hb).2]
      rw [Finset.sum_congr rfl this, Finset.sum_const, smul_eq_mul, mul_one]
      rfl
    have hNv : (∑ a ∈ N, f a v) = degIn G S v := by
      have : ∀ a ∈ N, f a v = 1 := fun a ha => by
        simp [f, (Finset.mem_filter.mp ha).2.symm]
      rw [Finset.sum_congr rfl this, Finset.sum_const, smul_eq_mul, mul_one]
      rfl
    have hNN : (∑ a ∈ N, ∑ b ∈ N, f a b) = 0 := by
      refine Finset.sum_eq_zero fun a ha => Finset.sum_eq_zero fun b hb => ?_
      have hva : G.Adj v a := (Finset.mem_filter.mp ha).2
      have hvb : G.Adj v b := (Finset.mem_filter.mp hb).2
      have hnab : ¬ G.Adj a b := fun hab => htf v a b ⟨hva, hab, hvb⟩
      simp [f, hnab]
    calc
      (∑ b ∈ D, f v b) + ∑ a ∈ N, ∑ b ∈ D, f a b
          = (f v v + ∑ b ∈ N, f v b) + ∑ a ∈ N, (f a v + ∑ b ∈ N, f a b) := by
            rw [hD_split]
            congr 1
            exact Finset.sum_congr rfl fun a _ => hD_split (f a)
      _ = (0 + degIn G S v) + ((∑ a ∈ N, f a v) + ∑ a ∈ N, ∑ b ∈ N, f a b) := by
            rw [hvv, hvN, Finset.sum_add_distrib]
      _ = 2 * degIn G S v := by rw [hNv, hNN]; omega
  have hDS : (∑ a ∈ D, ∑ b ∈ S, f a b) = degIn G S v + ∑ u ∈ N, degIn G S u := by
    have : ∀ a ∈ D, (∑ b ∈ S, f a b) = degIn G S a := fun a _ => (degIn_eq_sum G S a).symm
    rw [Finset.sum_congr rfl this, Finset.sum_insert hv_not_N]
  have hDS_split : (∑ a ∈ D, ∑ b ∈ S, f a b) =
      (∑ a ∈ D, ∑ b ∈ Sv, f a b) + ∑ a ∈ D, ∑ b ∈ D, f a b := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_union hdisj, hunion]
  have hSS_split : edgeSum G S = edgeSum G Sv + (∑ a ∈ Sv, ∑ b ∈ D, f a b) +
      (∑ a ∈ D, ∑ b ∈ Sv, f a b) + ∑ a ∈ D, ∑ b ∈ D, f a b := by
    have hS_eq : edgeSum G S = ∑ a ∈ S, ∑ b ∈ S, f a b := edgeSum_eq_sum G S
    have hSv_eq : edgeSum G Sv = ∑ a ∈ Sv, ∑ b ∈ Sv, f a b := edgeSum_eq_sum G Sv
    rw [hS_eq, hSv_eq, ← hunion, Finset.sum_union hdisj]
    have h1 : (∑ a ∈ Sv, ∑ b ∈ Sv ∪ D, f a b) =
        (∑ a ∈ Sv, ∑ b ∈ Sv, f a b) + ∑ a ∈ Sv, ∑ b ∈ D, f a b := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_union hdisj
    have h2 : (∑ a ∈ D, ∑ b ∈ Sv ∪ D, f a b) =
        (∑ a ∈ D, ∑ b ∈ Sv, f a b) + ∑ a ∈ D, ∑ b ∈ D, f a b := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_union hdisj
    rw [h1, h2]
    omega
  change edgeSum G Sv + 2 * ∑ u ∈ N, degIn G S u = edgeSum G S
  omega

private lemma sum_nbr_degIn_eq_sum_sq {V : Type*} (G : SimpleGraph V) (S : Finset V) :
    (∑ v ∈ S, ∑ u ∈ S.filter (G.Adj v), degIn G S u) = ∑ u ∈ S, (degIn G S u) ^ 2 := by
  calc
    (∑ v ∈ S, ∑ u ∈ S.filter (G.Adj v), degIn G S u)
        = ∑ v ∈ S, ∑ u ∈ S, if G.Adj v u then degIn G S u else 0 := by
          refine Finset.sum_congr rfl fun v _ => ?_
          rw [Finset.sum_filter]
    _ = ∑ u ∈ S, ∑ v ∈ S, if G.Adj v u then degIn G S u else 0 := Finset.sum_comm
    _ = ∑ u ∈ S, ∑ v ∈ S, if G.Adj u v then degIn G S u else 0 := by
          refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
          by_cases h : G.Adj v u
          · simp [h, h.symm]
          · have h' : ¬ G.Adj u v := fun huv => h huv.symm
            simp [h, h']
    _ = ∑ u ∈ S, (degIn G S u) ^ 2 := by
          refine Finset.sum_congr rfl fun u _ => ?_
          rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, sq]
          rfl

private lemma shearer_indep {V : Type*} (G : SimpleGraph V)
    (htf : ∀ a b c : V, ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj a c)) :
    ∀ (m : ℕ) (S : Finset V), S.card = m → S.Nonempty →
      ∃ I ⊆ S, IsIndep G I ∧
        (S.card : ℝ) * shearerF ((edgeSum G S : ℝ) / (S.card : ℝ)) ≤ (I.card : ℝ) := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro S hcard hne
    have hn_pos : (0 : ℝ) < (S.card : ℝ) := Nat.cast_pos.mpr hne.card_pos
    set n : ℝ := (S.card : ℝ)
    set d : ℝ := (edgeSum G S : ℝ) / n
    by_cases hd0 : edgeSum G S = 0
    · have hS_indep : IsIndep G S := by
        intro u hu w hw hadj
        have hzero : degIn G S u = 0 :=
          (Finset.sum_eq_zero_iff.mp hd0) u hu
        have hpos : 0 < degIn G S u :=
          Finset.card_pos.mpr ⟨w, Finset.mem_filter.mpr ⟨hw, hadj⟩⟩
        omega
      refine ⟨S, Finset.Subset.refl S, hS_indep, ?_⟩
      have hd_zero : d = 0 := by
        dsimp only [d]
        rw [hd0, Nat.cast_zero, zero_div]
      rw [hd_zero, shearerF_zero, mul_one]
    · have hd_pos : 0 < d := div_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hd0)) hn_pos
      have hedg_eq : (edgeSum G S : ℝ) = n * d := by
        dsimp only [d]
        field_simp [hn_pos.ne']
      let indepSets : Finset (Finset V) := S.powerset.filter (IsIndep G)
      have hEmpty_mem : (∅ : Finset V) ∈ indepSets := by
        simp [indepSets, IsIndep]
      have hcard_ne : (indepSets.image Finset.card).Nonempty :=
        ⟨0, Finset.mem_image.mpr ⟨∅, hEmpty_mem, Finset.card_empty⟩⟩
      let α : ℕ := (indepSets.image Finset.card).max' hcard_ne
      obtain ⟨Imax, hImax_mem, hImax_card⟩ :=
        Finset.mem_image.mp (Finset.max'_mem _ hcard_ne)
      have hImax_sub : Imax ⊆ S := Finset.mem_powerset.mp (Finset.mem_filter.mp hImax_mem).1
      have hImax_indep : IsIndep G Imax := (Finset.mem_filter.mp hImax_mem).2
      have hα_ge : ∀ I : Finset V, I ⊆ S → IsIndep G I → I.card ≤ α := fun I hIsub hIind =>
        Finset.le_max' _ _ (Finset.mem_image.mpr ⟨I,
          Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hIsub, hIind⟩, rfl⟩)
      have hvertex : ∀ v ∈ S,
          1 + (n - 1 - (degIn G S v : ℝ)) * shearerF d +
            shearerP d * ((1 + (degIn G S v : ℝ)) * d -
              2 * ∑ u ∈ S.filter (G.Adj v), (degIn G S u : ℝ)) ≤ (α : ℝ) := by
        intro v hv
        let N : Finset V := S.filter (G.Adj v)
        let D : Finset V := insert v N
        let Sv : Finset V := S \ D
        have hv_not_N : v ∉ N := by
          simp only [N, Finset.mem_filter, not_and]
          exact fun _ h => G.loopless.irrefl v h
        have hD_sub : D ⊆ S := by
          intro x hx
          simp only [D, N, Finset.mem_insert, Finset.mem_filter] at hx
          rcases hx with rfl | ⟨hxS, _⟩
          · exact hv
          · exact hxS
        have hD_card : D.card = 1 + degIn G S v := by
          rw [Finset.card_insert_of_notMem hv_not_N]
          dsimp only [N, degIn]
          omega
        have hSv_card_nat : Sv.card + (1 + degIn G S v) = S.card := by
          have := Finset.card_sdiff_add_card_eq_card hD_sub
          rw [hD_card] at this
          exact this
        have hSv_card_real : (Sv.card : ℝ) = n - 1 - (degIn G S v : ℝ) := by
          have : (Sv.card : ℝ) + (1 + (degIn G S v : ℝ)) = (S.card : ℝ) := by
            exact_mod_cast hSv_card_nat
          linarith
        have hSv_edg_nat := edgeSum_sub_closedNbr G htf S hv
        have hSv_edg_real : (edgeSum G Sv : ℝ) =
            n * d - 2 * ∑ u ∈ N, (degIn G S u : ℝ) := by
          have hcast : (edgeSum G Sv : ℝ) + 2 * ∑ u ∈ N, (degIn G S u : ℝ) =
              (edgeSum G S : ℝ) := by
            have := congrArg (Nat.cast (R := ℝ)) hSv_edg_nat
            push_cast at this
            exact this
          linarith [hedg_eq]
        have hdiff_eq : (edgeSum G Sv : ℝ) - (Sv.card : ℝ) * d =
            (1 + (degIn G S v : ℝ)) * d - 2 * ∑ u ∈ N, (degIn G S u : ℝ) := by
          rw [hSv_edg_real, hSv_card_real]
          ring
        by_cases hSv_ne : Sv.Nonempty
        · have hSv_lt : Sv.card < m := by omega
          obtain ⟨Iv, hIv_sub, hIv_indep, hIv_bound⟩ := ih Sv.card hSv_lt Sv rfl hSv_ne
          have hv_not_Iv : v ∉ Iv := fun hvIv => by
            have := hIv_sub hvIv
            simp [Sv, D] at this
          have hIv_ins_sub : insert v Iv ⊆ S := by
            intro x hx
            rcases Finset.mem_insert.mp hx with rfl | hxIv
            · exact hv
            · exact (Finset.mem_sdiff.mp (hIv_sub hxIv)).1
          have hIv_ins_indep : IsIndep G (insert v Iv) := by
            intro a ha b hb hab
            rcases Finset.mem_insert.mp ha with rfl | haIv <;>
            rcases Finset.mem_insert.mp hb with rfl | hbIv
            · exact G.loopless.irrefl _ hab
            · have hbSv := Finset.mem_sdiff.mp (hIv_sub hbIv)
              exact hbSv.2 (Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hbSv.1, hab⟩))
            · have haSv := Finset.mem_sdiff.mp (hIv_sub haIv)
              exact haSv.2 (Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨haSv.1, hab.symm⟩))
            · exact hIv_indep a haIv b hbIv hab
          have hα_Iv : (1 : ℝ) + (Iv.card : ℝ) ≤ (α : ℝ) := by
            have hle_nat := hα_ge (insert v Iv) hIv_ins_sub hIv_ins_indep
            rw [Finset.card_insert_of_notMem hv_not_Iv] at hle_nat
            have : (Iv.card : ℝ) + 1 ≤ (α : ℝ) := by exact_mod_cast hle_nat
            linarith
          have hSv_pos : (0 : ℝ) < (Sv.card : ℝ) := Nat.cast_pos.mpr hSv_ne.card_pos
          have hdv_nonneg : 0 ≤ (edgeSum G Sv : ℝ) / (Sv.card : ℝ) :=
            div_nonneg (Nat.cast_nonneg _) hSv_pos.le
          have hsupp := shearerF_supporting hd_pos hdv_nonneg
          have hmul := mul_le_mul_of_nonneg_left hsupp hSv_pos.le
          have hdiv : (Sv.card : ℝ) * ((edgeSum G Sv : ℝ) / (Sv.card : ℝ)) = (edgeSum G Sv : ℝ) :=
            mul_div_cancel₀ _ hSv_pos.ne'
          have hlin : (Sv.card : ℝ) * (shearerF d + shearerP d * ((edgeSum G Sv : ℝ) / (Sv.card : ℝ) - d)) =
              (Sv.card : ℝ) * shearerF d + shearerP d * ((edgeSum G Sv : ℝ) - (Sv.card : ℝ) * d) := by
            linear_combination shearerP d * hdiv
          have hle1 : (Sv.card : ℝ) * shearerF d +
              shearerP d * ((edgeSum G Sv : ℝ) - (Sv.card : ℝ) * d) ≤ (Iv.card : ℝ) := by
            linarith [hmul, hlin, hIv_bound]
          rw [hdiff_eq, hSv_card_real] at hle1
          linarith
        · rw [Finset.not_nonempty_iff_eq_empty] at hSv_ne
          have hSv_card0 : (Sv.card : ℝ) = 0 := by simp [hSv_ne]
          have hSv_edg0 : (edgeSum G Sv : ℝ) = 0 := by simp [hSv_ne, edgeSum]
          have h1_le_α : (1 : ℝ) ≤ (α : ℝ) := by
            have hsing_sub : ({v} : Finset V) ⊆ S := Finset.singleton_subset_iff.mpr hv
            have hsing_indep : IsIndep G ({v} : Finset V) := by
              intro a ha b hb hab
              rw [Finset.mem_singleton] at ha hb
              subst ha; subst hb
              exact G.loopless.irrefl _ hab
            have := hα_ge {v} hsing_sub hsing_indep
            simp only [Finset.card_singleton] at this
            exact_mod_cast this
          rw [← hSv_card_real, ← hdiff_eq, hSv_card0, hSv_edg0]
          linarith
      have hsum_ineq := Finset.sum_le_sum hvertex
      have hsum_rhs : (∑ _v ∈ S, (α : ℝ)) = n * (α : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      have hsum_deg : (∑ v ∈ S, (degIn G S v : ℝ)) = n * d := by
        have : (∑ v ∈ S, (degIn G S v : ℝ)) = (edgeSum G S : ℝ) := by
          dsimp only [edgeSum]
          push_cast
          rfl
        rw [this, hedg_eq]
      have hsum_sq_nat := sum_nbr_degIn_eq_sum_sq G S
      have hsum_nbr : (∑ v ∈ S, ∑ u ∈ S.filter (G.Adj v), (degIn G S u : ℝ)) =
          ∑ u ∈ S, (degIn G S u : ℝ) ^ 2 := by
        have := congrArg (Nat.cast (R := ℝ)) hsum_sq_nat
        push_cast at this
        exact this
      have hcs : (n * d) ^ 2 ≤ n * ∑ u ∈ S, (degIn G S u : ℝ) ^ 2 := by
        rw [← hsum_deg]
        simpa [n] using sq_sum_le_card_mul_sum_sq (s := S) (f := fun u => (degIn G S u : ℝ))
      have hsq_ge : n * d ^ 2 ≤ ∑ u ∈ S, (degIn G S u : ℝ) ^ 2 := by
        nlinarith
      have hsum_lhs : (∑ v ∈ S, (1 + (n - 1 - (degIn G S v : ℝ)) * shearerF d +
          shearerP d * ((1 + (degIn G S v : ℝ)) * d -
            2 * ∑ u ∈ S.filter (G.Adj v), (degIn G S u : ℝ)))) =
          n + (n * (n - 1) - n * d) * shearerF d +
            shearerP d * ((n + n * d) * d - 2 * ∑ u ∈ S, (degIn G S u : ℝ) ^ 2) := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
          ← Finset.mul_sum, ← Finset.sum_mul, hsum_deg, hsum_nbr]
        ring
      rw [hsum_lhs, hsum_rhs] at hsum_ineq
      have hP_nonpos := shearerP_nonpos d
      have hP_cs : shearerP d * (-2 * (n * d ^ 2)) ≤
          shearerP d * (-2 * ∑ u ∈ S, (degIn G S u : ℝ) ^ 2) := by
        nlinarith
      have hode := shearer_ode hd_pos
      have hfinal : n * (n * shearerF d) ≤ n * (α : ℝ) := by
        have hstep1 : n + (n * (n - 1) - n * d) * shearerF d +
            shearerP d * ((n + n * d) * d - 2 * (n * d ^ 2)) ≤ n * (α : ℝ) := by
          linarith
        have hident : n + (n * (n - 1) - n * d) * shearerF d +
            shearerP d * ((n + n * d) * d - 2 * (n * d ^ 2)) =
            n * (n * shearerF d) +
              n * (1 - ((d + 1) * shearerF d - (d - d ^ 2) * shearerP d)) := by
          ring
        rw [hident, hode] at hstep1
        linarith
      have hα_bound : n * shearerF d ≤ (α : ℝ) := by nlinarith
      refine ⟨Imax, hImax_sub, hImax_indep, ?_⟩
      rw [hImax_card]
      exact hα_bound

private lemma exists_copy_K3_of_triangle {n : ℕ} {C : SimpleGraph (Fin n)} {a b c : Fin n}
    (hab : C.Adj a b) (hbc : C.Adj b c) (hac : C.Adj a c) :
    (SimpleGraph.completeGraph (Fin 3)).IsContained C := by
  have hne_ab : a ≠ b := C.ne_of_adj hab
  have hne_bc : b ≠ c := C.ne_of_adj hbc
  have hne_ac : a ≠ c := C.ne_of_adj hac
  refine ⟨⟨⟨![a, b, c], ?_⟩, ?_⟩⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [hab.symm, hbc.symm, hac.symm]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [hne_ab.symm, hne_bc.symm, hne_ac.symm]

private lemma exists_copy_Kk_compl_of_indep {n k : ℕ} {C : SimpleGraph (Fin n)}
    {I : Finset (Fin n)} (hI : IsIndep C I) (hcard : k ≤ I.card) :
    (SimpleGraph.completeGraph (Fin k)).IsContained Cᶜ := by
  obtain ⟨I', hI'_sub, hI'_card⟩ := Finset.exists_subset_card_eq hcard
  let e : Fin k ≃ I' := (Fintype.equivFinOfCardEq (by simp [hI'_card])).symm
  let f : Fin k → Fin n := fun i => (e i).1
  have hf_inj : Function.Injective f := Subtype.val_injective.comp e.injective
  refine ⟨⟨⟨f, ?_⟩, hf_inj⟩⟩
  intro i j hij
  have hne : f i ≠ f j := hf_inj.ne hij
  have hna : ¬ C.Adj (f i) (f j) := hI (f i) (hI'_sub (e i).2) (f j) (hI'_sub (e j).2)
  exact ⟨hne, hna⟩

private lemma shearer_ramsey_upper :
    ∀ ε > (0 : ℝ), ∀ᶠ k : ℕ in atTop,
      (SimpleGraph.classicalRamsey 3 k : ℝ) ≤ (1 + ε) * (k : ℝ) ^ 2 / Real.log k := by
  intro ε hε
  let M : ℝ := max 2 (2 * (1 + ε) / ε)
  let K0 : ℕ := max 3 (max (Nat.ceil (2 / ε)) (Nat.ceil (Real.exp M)))
  rw [Filter.eventually_atTop]
  refine ⟨K0, fun k hk => ?_⟩
  have hk3 : 3 ≤ k := le_trans (le_max_left _ _) hk
  have hk_ge_2div : (2 / ε) ≤ (k : ℝ) :=
    le_trans (Nat.le_ceil _) (Nat.cast_le.mpr (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hk))
  have hk_ge_exp : Real.exp M ≤ (k : ℝ) :=
    le_trans (Nat.le_ceil _) (Nat.cast_le.mpr (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hk))
  have hk_real_pos : (0 : ℝ) < (k : ℝ) := by positivity
  have hk_gt_one : (1 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 1 < k)
  have hlog_ge_M : M ≤ Real.log (k : ℝ) := by
    rw [← Real.log_exp M]
    exact Real.log_le_log (Real.exp_pos M) hk_ge_exp
  have hlog_ge_2 : (2 : ℝ) ≤ Real.log (k : ℝ) := le_trans (le_max_left _ _) hlog_ge_M
  have hlog_pos : 0 < Real.log (k : ℝ) := by linarith
  have hlog_ge_ratio : 2 * (1 + ε) / ε ≤ Real.log (k : ℝ) := le_trans (le_max_right _ _) hlog_ge_M
  have hlog_le_k : Real.log (k : ℝ) ≤ (k : ℝ) - 1 := Real.log_le_sub_one_of_pos hk_real_pos
  let A : ℝ := (1 + ε) * (k : ℝ) ^ 2 / Real.log (k : ℝ)
  have hA_ge_1 : 1 ≤ A := by
    dsimp only [A]
    rw [le_div_iff₀ hlog_pos]
    have hk_ge_3 : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk3
    nlinarith
  let N : ℕ := Nat.floor A
  have hN_le : (N : ℝ) ≤ A := Nat.floor_le (by linarith)
  have hN_pos : 0 < N := Nat.floor_pos.mpr hA_ge_1
  have hN_gt : A - 1 < (N : ℝ) := by
    have := Nat.lt_floor_add_one A
    linarith
  have hramsey_le : SimpleGraph.classicalRamsey 3 k ≤ N := by
    apply Nat.sInf_le
    intro C
    by_contra hnone
    push Not at hnone
    rcases hnone with ⟨hno3, hnok⟩
    have htf : ∀ a b c : Fin N, ¬ (C.Adj a b ∧ C.Adj b c ∧ C.Adj a c) :=
      fun a b c ⟨h1, h2, h3⟩ => hno3.elim (exists_copy_K3_of_triangle h1 h2 h3).some
    have hα_lt : ∀ I : Finset (Fin N), IsIndep C I → I.card < k := by
      intro I hI
      by_contra hge
      push Not at hge
      exact hnok.elim (exists_copy_Kk_compl_of_indep hI hge).some
    have hdeg_le : ∀ v : Fin N, degIn C Finset.univ v ≤ k - 1 := by
      intro v
      have hN_indep : IsIndep C (Finset.univ.filter (C.Adj v)) := by
        intro a ha b hb hab
        exact htf v a b ⟨(Finset.mem_filter.mp ha).2, hab, (Finset.mem_filter.mp hb).2⟩
      have hlt := hα_lt _ hN_indep
      dsimp only [degIn]
      omega
    have hS_ne : (Finset.univ : Finset (Fin N)).Nonempty := by
      rw [Finset.univ_nonempty_iff]
      exact ⟨⟨0, hN_pos⟩⟩
    obtain ⟨I, _, hI_indep, hI_bound⟩ :=
      shearer_indep C htf N Finset.univ (by simp) hS_ne
    have hI_lt : I.card < k := hα_lt I hI_indep
    have hI_real_lt : (I.card : ℝ) < (k : ℝ) := Nat.cast_lt.mpr hI_lt
    have hcard_univ : ((Finset.univ : Finset (Fin N)).card : ℝ) = (N : ℝ) := by simp
    have hN_real_pos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN_pos
    have hd_nonneg : 0 ≤ (edgeSum C Finset.univ : ℝ) / (N : ℝ) :=
      div_nonneg (Nat.cast_nonneg _) hN_real_pos.le
    have hd_le_k : (edgeSum C Finset.univ : ℝ) / (N : ℝ) ≤ (k : ℝ) := by
      rw [div_le_iff₀ hN_real_pos]
      have hsum_le : edgeSum C Finset.univ ≤ k * N := by
        calc
          edgeSum C Finset.univ = ∑ v : Fin N, degIn C Finset.univ v := rfl
          _ ≤ ∑ _v : Fin N, k := Finset.sum_le_sum fun v _ => le_trans (hdeg_le v) (Nat.sub_le k 1)
          _ = k * N := by simp [mul_comm]
      exact_mod_cast hsum_le
    have hf_ge : shearerF (k : ℝ) ≤ shearerF ((edgeSum C Finset.univ : ℝ) / (N : ℝ)) :=
      shearerF_antitone hd_nonneg hd_le_k
    have hfk_lower : (Real.log (k : ℝ) - 1) / (k : ℝ) ≤ shearerF (k : ℝ) := by
      rw [shearerF_formula hk_gt_one]
      have hk1_pos : (0 : ℝ) < (k : ℝ) - 1 := by linarith
      have hsq_pos : (0 : ℝ) < ((k : ℝ) - 1) ^ 2 := sq_pos_of_pos hk1_pos
      rw [div_le_div_iff₀ hk_real_pos hsq_pos]
      have hsq_le : ((k : ℝ) - 1) ^ 2 ≤ (k : ℝ) ^ 2 := by nlinarith
      have hnum_pos : 0 ≤ Real.log (k : ℝ) - 1 := by linarith
      nlinarith
    rw [hcard_univ] at hI_bound
    have hN_mul_le : (N : ℝ) * ((Real.log (k : ℝ) - 1) / (k : ℝ)) ≤ (I.card : ℝ) :=
      le_trans (mul_le_mul_of_nonneg_left (le_trans hfk_lower hf_ge) hN_real_pos.le) hI_bound
    have hN_log_lt : (N : ℝ) * (Real.log (k : ℝ) - 1) < (k : ℝ) ^ 2 := by
      have : (N : ℝ) * ((Real.log (k : ℝ) - 1) / (k : ℝ)) < (k : ℝ) := lt_of_le_of_lt hN_mul_le hI_real_lt
      rw [← mul_div_assoc, div_lt_iff₀ hk_real_pos] at this
      nlinarith
    have hA_term : A ≤ (ε / 2) * (k : ℝ) ^ 2 := by
      dsimp only [A]
      rw [div_le_iff₀ hlog_pos]
      have h1 := (div_le_iff₀ hε).mp hlog_ge_ratio
      nlinarith
    have hk_term : Real.log (k : ℝ) - 1 ≤ (ε / 2) * (k : ℝ) ^ 2 := by
      have h1 := (div_le_iff₀ hε).mp hk_ge_2div
      nlinarith
    have hprod_ge : (k : ℝ) ^ 2 ≤ (A - 1) * (Real.log (k : ℝ) - 1) := by
      have hAlog : A * Real.log (k : ℝ) = (1 + ε) * (k : ℝ) ^ 2 := by
        dsimp only [A]
        field_simp [hlog_pos.ne']
      nlinarith
    have hstrict : (A - 1) * (Real.log (k : ℝ) - 1) < (N : ℝ) * (Real.log (k : ℝ) - 1) :=
      mul_lt_mul_of_pos_right hN_gt (by linarith)
    linarith
  exact le_trans (Nat.cast_le.mpr hramsey_le) hN_le

end Erdos165UpperProof

theorem OMA.solution : type_of% @Erdos165.erdos_165.variants.upper :=
  Erdos165UpperProof.shearer_ramsey_upper
