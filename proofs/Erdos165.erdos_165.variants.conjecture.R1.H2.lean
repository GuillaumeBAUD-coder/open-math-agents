import OMAReductions.R_Erdos165_erdos_165_variants_conjecture_R1

/-!
# Proof of `Erdos165.erdos_165.variants.conjecture.R1.H2`

Shearer's 1983 lower bound on the independence number of triangle-free graphs:
every triangle-free graph `G` on `n` vertices with average degree `d = 2 |E(G)| / n`
contains an independent set of size at least `n * f(d)`, where
`f(d) = (d log d - d + 1) / (d - 1)^2` (with `f(0) = 1`, `f(1) = 1/2`).
When `4 |E(G)| ≤ n k`, we have `d ≤ k / 2`, so `n * f(d) ≥ n * f(k / 2) ≥ k`
for all sufficiently large `k` whenever `n > (1 + δ) k^2 / (2 log k)`.
-/

open Filter SimpleGraph
open scoped BigOperators

namespace Erdos165R1H2Proof

private noncomputable def shearerF (d : ℝ) : ℝ :=
  if d = 0 then 1
  else if d = 1 then 1 / 2
  else (d * Real.log d - d + 1) / (d - 1) ^ 2

private noncomputable def shearerF' (d : ℝ) : ℝ :=
  if d = 1 then -(1 / 6)
  else (2 * (d - 1) - (d + 1) * Real.log d) / (d - 1) ^ 3

private lemma cube_pos_of_pos {a : ℝ} (ha : 0 < a) : 0 < a ^ 3 := by
  have : a ^ 3 = a * a ^ 2 := by ring
  rw [this]; exact mul_pos ha (sq_pos_of_pos ha)

private lemma cube_neg_of_neg {a : ℝ} (ha : a < 0) : a ^ 3 < 0 := by
  have : a ^ 3 = a * a ^ 2 := by ring
  rw [this]; exact mul_neg_of_neg_of_pos ha (sq_pos_of_neg ha)

private lemma log_le_or_ge_rational (x : ℝ) (hx : 0 < x) :
    (1 ≤ x → 2 * (x - 1) / (x + 1) ≤ Real.log x) ∧
    (x ≤ 1 → Real.log x ≤ 2 * (x - 1) / (x + 1)) := by
  let h : ℝ → ℝ := fun t => Real.log t - 2 * (t - 1) / (t + 1)
  have hderiv : ∀ t ∈ Set.Ioi (0 : ℝ),
      HasDerivAt h ((t - 1) ^ 2 / (t * (t + 1) ^ 2)) t := by
    intro t ht
    have ht_pos : 0 < t := ht
    have ht0 : t ≠ 0 := ne_of_gt ht_pos
    have ht1 : t + 1 ≠ 0 := by linarith
    have h1 : HasDerivAt (fun s : ℝ => Real.log s) t⁻¹ t := Real.hasDerivAt_log ht0
    have h2 : HasDerivAt (fun s : ℝ => 2 * (s - 1)) 2 t := by
      have := ((hasDerivAt_id t).sub_const 1).const_mul 2
      simpa using this
    have h3 : HasDerivAt (fun s : ℝ => s + 1) 1 t := by
      simpa using (hasDerivAt_id t).add_const 1
    have hq := h1.fun_sub (h2.fun_div h3 ht1)
    have hval : t⁻¹ - (2 * (t + 1) - 2 * (t - 1) * 1) / (t + 1) ^ 2 =
        (t - 1) ^ 2 / (t * (t + 1) ^ 2) := by
      field_simp; ring
    simpa only [hval] using hq
  have hmono : MonotoneOn h (Set.Ioi 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ioi 0)
    · intro t ht; exact (hderiv t ht).continuousAt.continuousWithinAt
    · intro t ht; exact (hderiv t (by simpa [interior_Ioi] using ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      have ht' : 0 < t := by simpa [interior_Ioi] using ht
      rw [(hderiv t ht').deriv]
      positivity
  have h1_val : h 1 = 0 := by simp [h]
  constructor
  · intro hge
    have := hmono (show (1 : ℝ) ∈ Set.Ioi 0 by norm_num) hx hge
    rw [h1_val] at this
    dsimp [h] at this
    linarith
  · intro hle
    have := hmono hx (show (1 : ℝ) ∈ Set.Ioi 0 by norm_num) hle
    rw [h1_val] at this
    dsimp [h] at this
    linarith

private lemma log_ge_second_deriv_num (x : ℝ) (hx : 0 < x) :
    (x - 1) * (5 * x + 1) ≤ 2 * x * (x + 2) * Real.log x := by
  let q : ℝ → ℝ := fun t => Real.log t - (t - 1) * (5 * t + 1) / (2 * t * (t + 2))
  have hderiv : ∀ t ∈ Set.Ioi (0 : ℝ),
      HasDerivAt q ((t - 1) ^ 3 / (t ^ 2 * (t + 2) ^ 2)) t := by
    intro t ht
    have ht_pos : 0 < t := ht
    have ht0 : t ≠ 0 := ne_of_gt ht_pos
    have ht2 : t + 2 ≠ 0 := by linarith
    have hden : 2 * t * (t + 2) ≠ 0 := by positivity
    have h1 : HasDerivAt (fun s : ℝ => Real.log s) t⁻¹ t := Real.hasDerivAt_log ht0
    have hnum : HasDerivAt (fun s : ℝ => (s - 1) * (5 * s + 1)) (10 * t - 4) t := by
      have ha : HasDerivAt (fun s : ℝ => s - 1) 1 t := by simpa using (hasDerivAt_id t).sub_const 1
      have hb : HasDerivAt (fun s : ℝ => 5 * s + 1) 5 t := by
        simpa using ((hasDerivAt_id t).const_mul 5).add_const 1
      have hmul := ha.fun_mul hb
      have hval : 1 * (5 * t + 1) + (t - 1) * 5 = 10 * t - 4 := by ring
      simpa only [hval] using hmul
    have hden_d : HasDerivAt (fun s : ℝ => 2 * s * (s + 2)) (4 * t + 4) t := by
      have ha : HasDerivAt (fun s : ℝ => 2 * s) 2 t := by simpa using (hasDerivAt_id t).const_mul 2
      have hb : HasDerivAt (fun s : ℝ => s + 2) 1 t := by simpa using (hasDerivAt_id t).add_const 2
      have hmul := ha.fun_mul hb
      have hval : 2 * (t + 2) + 2 * t * 1 = 4 * t + 4 := by ring
      simpa only [hval] using hmul
    have hq := h1.fun_sub (hnum.fun_div hden_d hden)
    have hval : t⁻¹ - ((10 * t - 4) * (2 * t * (t + 2)) - (t - 1) * (5 * t + 1) * (4 * t + 4)) /
        (2 * t * (t + 2)) ^ 2 = (t - 1) ^ 3 / (t ^ 2 * (t + 2) ^ 2) := by
      field_simp; ring
    simpa only [hval] using hq
  have hq1 : q 1 = 0 := by simp [q]
  have hq_nonneg : 0 ≤ q x := by
    by_cases hx1 : 1 ≤ x
    · have hmono : MonotoneOn q (Set.Ici 1) := by
        apply monotoneOn_of_deriv_nonneg (convex_Ici 1)
        · intro t ht
          have ht_ge : 1 ≤ t := ht
          exact (hderiv t (show (0 : ℝ) < t by linarith)).continuousAt.continuousWithinAt
        · intro t ht
          have ht' : 1 < t := by simpa [interior_Ici] using ht
          exact (hderiv t (show (0 : ℝ) < t by linarith)).differentiableAt.differentiableWithinAt
        · intro t ht
          have ht' : 1 < t := by simpa [interior_Ici] using ht
          rw [(hderiv t (show (0 : ℝ) < t by linarith)).deriv]
          have hsub : 0 ≤ t - 1 := by linarith
          positivity
      have := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hx1) hx1
      linarith
    · have hanti : AntitoneOn q (Set.Ioc 0 1) := by
        apply antitoneOn_of_deriv_nonpos (convex_Ioc 0 1)
        · intro t ht; exact (hderiv t ht.1).continuousAt.continuousWithinAt
        · intro t ht
          have ht' : 0 < t ∧ t < 1 := by simpa [interior_Ioc] using ht
          exact (hderiv t ht'.1).differentiableAt.differentiableWithinAt
        · intro t ht
          have ht' : 0 < t ∧ t < 1 := by simpa [interior_Ioc] using ht
          rw [(hderiv t ht'.1).deriv]
          have hnum_le : (t - 1) ^ 3 ≤ 0 := le_of_lt (cube_neg_of_neg (by linarith))
          have hden_pos : 0 < t ^ 2 * (t + 2) ^ 2 := by
            have ht0 : 0 < t := ht'.1
            have ht2 : 0 < t + 2 := by linarith
            positivity
          exact div_nonpos_of_nonpos_of_nonneg hnum_le (le_of_lt hden_pos)
      have := hanti ⟨hx, le_of_not_ge hx1⟩ ⟨by norm_num, le_rfl⟩ (le_of_not_ge hx1)
      linarith
  dsimp [q] at hq_nonneg
  have hden_pos : 0 < 2 * x * (x + 2) := by positivity
  rw [sub_nonneg, div_le_iff₀ hden_pos] at hq_nonneg
  linarith

private lemma log_le_cubic_rational (x : ℝ) (hx : 0 < x) :
    6 * (x + 1) * Real.log x ≤ (x - 1) * (x ^ 2 - 2 * x + 13) := by
  let r : ℝ → ℝ := fun t => Real.log t - (t - 1) * (t ^ 2 - 2 * t + 13) / (6 * (t + 1))
  have hderiv : ∀ t ∈ Set.Ioi (0 : ℝ),
      HasDerivAt r (-((t - 1) ^ 3 * (t + 3)) / (3 * t * (t + 1) ^ 2)) t := by
    intro t ht
    have ht_pos : 0 < t := ht
    have ht0 : t ≠ 0 := ne_of_gt ht_pos
    have ht1 : t + 1 ≠ 0 := by linarith
    have hden : 6 * (t + 1) ≠ 0 := by linarith
    have h1 : HasDerivAt (fun s : ℝ => Real.log s) t⁻¹ t := Real.hasDerivAt_log ht0
    have hnum : HasDerivAt (fun s : ℝ => (s - 1) * (s ^ 2 - 2 * s + 13))
        (3 * t ^ 2 - 6 * t + 15) t := by
      have ha : HasDerivAt (fun s : ℝ => s - 1) 1 t := by simpa using (hasDerivAt_id t).sub_const 1
      have hsq : HasDerivAt (fun s : ℝ => s * s) (2 * t) t := by
        have hid : HasDerivAt (fun s : ℝ => s) 1 t := hasDerivAt_id t
        have hm := hid.fun_mul hid
        have hval : 1 * t + t * 1 = 2 * t := by ring
        simpa only [hval] using hm
      have hsq' : HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t := by
        simpa only [sq] using hsq
      have hlin : HasDerivAt (fun s : ℝ => 2 * s) 2 t := by
        simpa using (hasDerivAt_id t).const_mul 2
      have hb : HasDerivAt (fun s : ℝ => s ^ 2 - 2 * s + 13) (2 * t - 2) t :=
        (hsq'.fun_sub hlin).add_const 13
      have hmul := ha.fun_mul hb
      have hval : 1 * (t ^ 2 - 2 * t + 13) + (t - 1) * (2 * t - 2) = 3 * t ^ 2 - 6 * t + 15 := by
        ring
      simpa only [hval] using hmul
    have hden_d : HasDerivAt (fun s : ℝ => 6 * (s + 1)) 6 t := by
      simpa using ((hasDerivAt_id t).add_const 1).const_mul 6
    have hq := h1.fun_sub (hnum.fun_div hden_d hden)
    have hval : t⁻¹ - ((3 * t ^ 2 - 6 * t + 15) * (6 * (t + 1)) -
        (t - 1) * (t ^ 2 - 2 * t + 13) * 6) / (6 * (t + 1)) ^ 2 =
        -((t - 1) ^ 3 * (t + 3)) / (3 * t * (t + 1) ^ 2) := by
      field_simp; ring
    simpa only [hval] using hq
  have hr1 : r 1 = 0 := by simp [r]
  have hr_nonpos : r x ≤ 0 := by
    by_cases hx1 : 1 ≤ x
    · have hanti : AntitoneOn r (Set.Ici 1) := by
        apply antitoneOn_of_deriv_nonpos (convex_Ici 1)
        · intro t ht
          have ht_ge : 1 ≤ t := ht
          exact (hderiv t (show (0 : ℝ) < t by linarith)).continuousAt.continuousWithinAt
        · intro t ht
          have ht' : 1 < t := by simpa [interior_Ici] using ht
          exact (hderiv t (show (0 : ℝ) < t by linarith)).differentiableAt.differentiableWithinAt
        · intro t ht
          have ht' : 1 < t := by simpa [interior_Ici] using ht
          rw [(hderiv t (show (0 : ℝ) < t by linarith)).deriv]
          have hnum_le : -((t - 1) ^ 3 * (t + 3)) ≤ 0 := by
            have h1 : 0 < (t - 1) ^ 3 := cube_pos_of_pos (by linarith)
            have h2 : 0 < t + 3 := by linarith
            nlinarith
          have hden_pos : 0 < 3 * t * (t + 1) ^ 2 := by
            have ht0 : 0 < t := by linarith
            have ht1 : 0 < t + 1 := by linarith
            positivity
          exact div_nonpos_of_nonpos_of_nonneg hnum_le (le_of_lt hden_pos)
      have := hanti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hx1) hx1
      linarith
    · have hmono : MonotoneOn r (Set.Ioc 0 1) := by
        apply monotoneOn_of_deriv_nonneg (convex_Ioc 0 1)
        · intro t ht; exact (hderiv t ht.1).continuousAt.continuousWithinAt
        · intro t ht
          have ht' : 0 < t ∧ t < 1 := by simpa [interior_Ioc] using ht
          exact (hderiv t ht'.1).differentiableAt.differentiableWithinAt
        · intro t ht
          have ht' : 0 < t ∧ t < 1 := by simpa [interior_Ioc] using ht
          rw [(hderiv t ht'.1).deriv]
          have hnum_ge : 0 ≤ -((t - 1) ^ 3 * (t + 3)) := by
            have h1 : (t - 1) ^ 3 < 0 := cube_neg_of_neg (by linarith)
            have h2 : 0 < t + 3 := by linarith
            nlinarith
          have hden_pos : 0 < 3 * t * (t + 1) ^ 2 := by
            have ht0 : 0 < t := ht'.1
            have ht1 : 0 < t + 1 := by linarith
            positivity
          exact div_nonneg hnum_ge (le_of_lt hden_pos)
      have := hmono ⟨hx, le_of_not_ge hx1⟩ ⟨by norm_num, le_rfl⟩ (le_of_not_ge hx1)
      linarith
  dsimp [r] at hr_nonpos
  have hden_pos : 0 < 6 * (x + 1) := by linarith
  rw [sub_nonpos, le_div_iff₀ hden_pos] at hr_nonpos
  linarith

private lemma shearerF'_nonpos (d : ℝ) (hd : 0 < d) : shearerF' d ≤ 0 := by
  unfold shearerF'
  split_ifs with h1
  · norm_num
  · rcases lt_or_gt_of_ne h1 with hlt | hgt
    · have hlog := (log_le_or_ge_rational d hd).2 (le_of_lt hlt)
      have hd1_pos : 0 < d + 1 := by linarith
      rw [le_div_iff₀ hd1_pos] at hlog
      have hnum : 0 ≤ 2 * (d - 1) - (d + 1) * Real.log d := by linarith
      have hden : (d - 1) ^ 3 < 0 := cube_neg_of_neg (by linarith)
      exact div_nonpos_of_nonneg_of_nonpos hnum (le_of_lt hden)
    · have hlog := (log_le_or_ge_rational d hd).1 (le_of_lt hgt)
      have hd1_pos : 0 < d + 1 := by linarith
      rw [div_le_iff₀ hd1_pos] at hlog
      have hnum : 2 * (d - 1) - (d + 1) * Real.log d ≤ 0 := by linarith
      have hden : 0 < (d - 1) ^ 3 := cube_pos_of_pos (by linarith)
      exact div_nonpos_of_nonpos_of_nonneg hnum (le_of_lt hden)

private lemma shearerF_hasDerivAt {x : ℝ} (hx : 0 < x) (hx1 : x ≠ 1) :
    HasDerivAt shearerF (shearerF' x) x := by
  have hne0 : x ≠ 0 := ne_of_gt hx
  have hsub : x - 1 ≠ 0 := sub_ne_zero.mpr hx1
  have hEq : shearerF =ᶠ[nhds x] fun t => (t * Real.log t - t + 1) / (t - 1) ^ 2 := by
    have hopen : IsOpen ({t : ℝ | t ≠ 0 ∧ t ≠ 1}) :=
      (isOpen_ne (x := (0 : ℝ))).inter (isOpen_ne (x := (1 : ℝ)))
    filter_upwards [hopen.mem_nhds ⟨hne0, hx1⟩] with t ⟨ht0, ht1⟩
    simp [shearerF, ht0, ht1]
  rw [hEq.hasDerivAt_iff]
  have hnum : HasDerivAt (fun t : ℝ => t * Real.log t - t + 1) (Real.log x) x := by
    have hid : HasDerivAt (fun t : ℝ => t) 1 x := hasDerivAt_id x
    have hlog : HasDerivAt (fun t : ℝ => Real.log t) x⁻¹ x := Real.hasDerivAt_log hne0
    have h1 := (hid.fun_mul hlog).fun_sub hid
    have h2 := h1.add_const 1
    have hval : 1 * Real.log x + x * x⁻¹ - 1 = Real.log x := by field_simp; ring
    simpa only [hval] using h2
  have hden : HasDerivAt (fun t : ℝ => (t - 1) ^ 2) (2 * (x - 1)) x := by
    have h1 : HasDerivAt (fun t : ℝ => t - 1) 1 x := by simpa using (hasDerivAt_id x).sub_const 1
    have h2 := h1.fun_mul h1
    have hval : 1 * (x - 1) + (x - 1) * 1 = 2 * (x - 1) := by ring
    simpa only [sq, hval] using h2
  have hq := hnum.fun_div hden (pow_ne_zero 2 hsub)
  have hval : (Real.log x * (x - 1) ^ 2 - (x * Real.log x - x + 1) * (2 * (x - 1))) /
      ((x - 1) ^ 2) ^ 2 = shearerF' x := by
    simp only [shearerF', hx1, ↓reduceIte]
    field_simp; ring
  simpa only [hval] using hq

private lemma shearerF'_hasDerivAt {x : ℝ} (hx : 0 < x) (hx1 : x ≠ 1) :
    HasDerivAt shearerF' ((2 * x * (x + 2) * Real.log x - (x - 1) * (5 * x + 1)) /
      (x * (x - 1) ^ 4)) x := by
  have hne0 : x ≠ 0 := ne_of_gt hx
  have hsub : x - 1 ≠ 0 := sub_ne_zero.mpr hx1
  have hEq : shearerF' =ᶠ[nhds x] fun t => (2 * (t - 1) - (t + 1) * Real.log t) / (t - 1) ^ 3 := by
    filter_upwards [(isOpen_ne (x := (1 : ℝ))).mem_nhds hx1] with t ht1
    have ht1' : t ≠ 1 := ht1
    simp [shearerF', ht1']
  rw [hEq.hasDerivAt_iff]
  have hnum : HasDerivAt (fun t : ℝ => 2 * (t - 1) - (t + 1) * Real.log t)
      (2 - (Real.log x + (x + 1) * x⁻¹)) x := by
    have h1 : HasDerivAt (fun t : ℝ => 2 * (t - 1)) 2 x := by
      simpa using ((hasDerivAt_id x).sub_const 1).const_mul 2
    have h2 : HasDerivAt (fun t : ℝ => t + 1) 1 x := by simpa using (hasDerivAt_id x).add_const 1
    have hlog : HasDerivAt (fun t : ℝ => Real.log t) x⁻¹ x := Real.hasDerivAt_log hne0
    have h3 := h1.fun_sub (h2.fun_mul hlog)
    have hval : 2 - (1 * Real.log x + (x + 1) * x⁻¹) = 2 - (Real.log x + (x + 1) * x⁻¹) := by ring
    simpa only [hval] using h3
  have hden : HasDerivAt (fun t : ℝ => (t - 1) ^ 3) (3 * (x - 1) ^ 2) x := by
    have h1 : HasDerivAt (fun t : ℝ => t - 1) 1 x := by simpa using (hasDerivAt_id x).sub_const 1
    have h2 : HasDerivAt (fun t : ℝ => (t - 1) * (t - 1)) (2 * (x - 1)) x := by
      have hm := h1.fun_mul h1
      have hval : 1 * (x - 1) + (x - 1) * 1 = 2 * (x - 1) := by ring
      simpa only [hval] using hm
    have h3 := h2.fun_mul h1
    have hfn : (fun t : ℝ => (t - 1) * (t - 1) * (t - 1)) = (fun t : ℝ => (t - 1) ^ 3) := by
      ext t; ring
    have hval : 2 * (x - 1) * (x - 1) + (x - 1) * (x - 1) * 1 = 3 * (x - 1) ^ 2 := by ring
    rw [hfn, hval] at h3
    exact h3
  have hq := hnum.fun_div hden (pow_ne_zero 3 hsub)
  have hval : ((2 - (Real.log x + (x + 1) * x⁻¹)) * (x - 1) ^ 3 -
      (2 * (x - 1) - (x + 1) * Real.log x) * (3 * (x - 1) ^ 2)) / ((x - 1) ^ 3) ^ 2 =
      (2 * x * (x + 2) * Real.log x - (x - 1) * (5 * x + 1)) / (x * (x - 1) ^ 4) := by
    field_simp; ring
  simpa only [hval] using hq

private lemma shearerF_continuousAt_one : ContinuousAt shearerF 1 := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  refine ⟨min (1 / 2) (ε / 2), by positivity, fun x hx => ?_⟩
  rw [Real.dist_eq] at hx ⊢
  by_cases hx1 : x = 1
  · subst hx1; simpa using hε
  · have hx_lt_half : |x - 1| < 1 / 2 := lt_of_lt_of_le hx (min_le_left _ _)
    have hx_lt_eps : |x - 1| < ε / 2 := lt_of_lt_of_le hx (min_le_right _ _)
    have hx_pos : 0 < x := by linarith [(abs_lt.mp hx_lt_half).1]
    have hx_ne0 : x ≠ 0 := ne_of_gt hx_pos
    have hsub : x - 1 ≠ 0 := sub_ne_zero.mpr hx1
    have hf1 : shearerF 1 = 1 / 2 := by simp [shearerF]
    have hdiff : shearerF x - shearerF 1 =
        (2 * x * Real.log x - (x - 1) * (x + 1)) / (2 * (x - 1) ^ 2) := by
      rw [hf1]
      simp only [shearerF, hx_ne0, hx1, ↓reduceIte]
      field_simp; ring
    have hbound1 := log_le_or_ge_rational x hx_pos
    have hbound2 := log_ge_second_deriv_num x hx_pos
    have hbound3 := log_le_cubic_rational x hx_pos
    have hden_pos : 0 < 2 * (x - 1) ^ 2 := by positivity
    rw [hdiff, abs_div, abs_of_pos hden_pos, div_lt_iff₀ hden_pos]
    rcases lt_or_gt_of_ne hx1 with hlt | hgt
    · have hlo : (x - 1) * (5 * x + 1) / (2 * x * (x + 2)) ≤ Real.log x := by
        rw [div_le_iff₀ (by positivity)]; linarith
      have hhi : Real.log x ≤ 2 * (x - 1) / (x + 1) := hbound1.2 (le_of_lt hlt)
      have h1 : 2 * x * Real.log x - (x - 1) * (x + 1) ≤ (x - 1) ^ 2 * (1 - x) / (x + 1) := by
        have hmul : 2 * x * Real.log x ≤ 2 * x * (2 * (x - 1) / (x + 1)) :=
          mul_le_mul_of_nonneg_left hhi (by linarith)
        have hx1p : x + 1 ≠ 0 := by linarith
        have hcal : 2 * x * (2 * (x - 1) / (x + 1)) - (x - 1) * (x + 1) =
            (x - 1) ^ 2 * (1 - x) / (x + 1) := by field_simp; ring
        linarith
      have h2 : (x - 1) ^ 2 * (1 - x) / (x + 2) ≤ 2 * x * Real.log x - (x - 1) * (x + 1) := by
        have hmul : 2 * x * ((x - 1) * (5 * x + 1) / (2 * x * (x + 2))) ≤ 2 * x * Real.log x :=
          mul_le_mul_of_nonneg_left hlo (by linarith)
        have hx2p : x + 2 ≠ 0 := by linarith
        have hcal : 2 * x * ((x - 1) * (5 * x + 1) / (2 * x * (x + 2))) - (x - 1) * (x + 1) =
            (x - 1) ^ 2 * (1 - x) / (x + 2) := by field_simp; ring
        linarith
      have hpos_val : 0 ≤ 2 * x * Real.log x - (x - 1) * (x + 1) := by
        have : 0 ≤ (x - 1) ^ 2 * (1 - x) / (x + 2) := by
          have : 0 < 1 - x := by linarith
          positivity
        linarith
      rw [abs_of_nonneg hpos_val]
      have hstep : (x - 1) ^ 2 * (1 - x) / (x + 1) ≤ (x - 1) ^ 2 * (1 - x) := by
        rw [div_le_iff₀ (by linarith)]
        have : 0 ≤ (x - 1) ^ 2 * (1 - x) := by
          have : 0 < 1 - x := by linarith
          positivity
        nlinarith
      have h1x : 1 - x < ε / 2 := by linarith [(abs_lt.mp hx_lt_eps).1]
      have hsq_pos : 0 < (x - 1) ^ 2 := sq_pos_of_ne_zero hsub
      nlinarith
    · have hlo : 2 * (x - 1) / (x + 1) ≤ Real.log x := hbound1.1 (le_of_lt hgt)
      have hhi : Real.log x ≤ (x - 1) * (x ^ 2 - 2 * x + 13) / (6 * (x + 1)) := by
        rw [le_div_iff₀ (by linarith)]; linarith
      have hupper : 2 * x * Real.log x - (x - 1) * (x + 1) ≤ 0 := by
        have hmul : 2 * x * Real.log x ≤ 2 * x * ((x - 1) * (x ^ 2 - 2 * x + 13) / (6 * (x + 1))) :=
          mul_le_mul_of_nonneg_left hhi (by linarith)
        have hx1p : x + 1 ≠ 0 := by linarith
        have hcal : 2 * x * ((x - 1) * (x ^ 2 - 2 * x + 13) / (6 * (x + 1))) - (x - 1) * (x + 1) =
            (x - 1) ^ 3 * (x - 3) / (3 * (x + 1)) := by field_simp; ring
        have hneg : (x - 1) ^ 3 * (x - 3) / (3 * (x + 1)) ≤ 0 := by
          have hc : 0 < (x - 1) ^ 3 := cube_pos_of_pos (by linarith)
          have hx3 : x - 3 < 0 := by linarith [(abs_lt.mp hx_lt_half).2]
          have hden' : 0 < 3 * (x + 1) := by linarith
          exact div_nonpos_of_nonpos_of_nonneg (by nlinarith) (le_of_lt hden')
        linarith
      have hlower : -((x - 1) ^ 2 * (x - 1)) ≤ 2 * x * Real.log x - (x - 1) * (x + 1) := by
        have hmul : 2 * x * (2 * (x - 1) / (x + 1)) ≤ 2 * x * Real.log x :=
          mul_le_mul_of_nonneg_left hlo (by linarith)
        have hx1p : 0 < x + 1 := by linarith
        have hcal : 2 * x * (2 * (x - 1) / (x + 1)) - (x - 1) * (x + 1) =
            -((x - 1) ^ 2 * (x - 1) / (x + 1)) := by field_simp; ring
        have hdiv : (x - 1) ^ 2 * (x - 1) / (x + 1) ≤ (x - 1) ^ 2 * (x - 1) := by
          rw [div_le_iff₀ hx1p]
          have : 0 ≤ (x - 1) ^ 2 * (x - 1) := by nlinarith
          nlinarith
        linarith
      rw [abs_of_nonpos hupper]
      have hx1_lt : x - 1 < ε / 2 := by linarith [(abs_lt.mp hx_lt_eps).2]
      have hsq_pos : 0 < (x - 1) ^ 2 := sq_pos_of_ne_zero hsub
      nlinarith

private lemma shearerF'_mono : MonotoneOn shearerF' (Set.Ioi 0) := by
  have hmono_lo : MonotoneOn shearerF' (Set.Ioo 0 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ioo 0 1)
    · intro t ht; exact (shearerF'_hasDerivAt ht.1 (ne_of_lt ht.2)).continuousAt.continuousWithinAt
    · intro t ht
      have ht' : 0 < t ∧ t < 1 := by simpa [interior_Ioo] using ht
      exact (shearerF'_hasDerivAt ht'.1 (ne_of_lt ht'.2)).differentiableAt.differentiableWithinAt
    · intro t ht
      have ht' : 0 < t ∧ t < 1 := by simpa [interior_Ioo] using ht
      rw [(shearerF'_hasDerivAt ht'.1 (ne_of_lt ht'.2)).deriv]
      have hnum : 0 ≤ 2 * t * (t + 2) * Real.log t - (t - 1) * (5 * t + 1) := by
        linarith [log_ge_second_deriv_num t ht'.1]
      have hden : 0 < t * (t - 1) ^ 4 := by
        have ht0 : 0 < t := ht'.1
        have hsub : t - 1 ≠ 0 := sub_ne_zero.mpr (ne_of_lt ht'.2)
        have h4 : 0 < (t - 1) ^ 4 := by
          have : (t - 1) ^ 4 = ((t - 1) ^ 2) ^ 2 := by ring
          rw [this]; exact sq_pos_of_pos (sq_pos_of_ne_zero hsub)
        exact mul_pos ht0 h4
      exact div_nonneg hnum (le_of_lt hden)
  have hmono_hi : MonotoneOn shearerF' (Set.Ioi 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ioi 1)
    · intro t ht
      have ht1 : 1 < t := ht
      exact (shearerF'_hasDerivAt (by linarith) (ne_of_gt ht1)).continuousAt.continuousWithinAt
    · intro t ht
      have ht' : 1 < t := by simpa [interior_Ioi] using ht
      exact (shearerF'_hasDerivAt (by linarith) (ne_of_gt ht')).differentiableAt.differentiableWithinAt
    · intro t ht
      have ht' : 1 < t := by simpa [interior_Ioi] using ht
      rw [(shearerF'_hasDerivAt (by linarith) (ne_of_gt ht')).deriv]
      have hnum : 0 ≤ 2 * t * (t + 2) * Real.log t - (t - 1) * (5 * t + 1) := by
        linarith [log_ge_second_deriv_num t (by linarith)]
      have hden : 0 < t * (t - 1) ^ 4 := by
        have ht0 : 0 < t := by linarith
        have hsub : 0 < t - 1 := by linarith
        positivity
      exact div_nonneg hnum (le_of_lt hden)
  have hle1 : ∀ t, 0 < t → t < 1 → shearerF' t ≤ shearerF' 1 := by
    intro t ht0 ht1
    have hne : t ≠ 1 := ne_of_lt ht1
    simp only [shearerF', hne, ↓reduceIte]
    have hcub := log_le_cubic_rational t ht0
    have hden : (t - 1) ^ 3 < 0 := cube_neg_of_neg (by linarith)
    rw [div_le_iff_of_neg hden]
    nlinarith
  have hge1 : ∀ t, 1 < t → shearerF' 1 ≤ shearerF' t := by
    intro t ht1
    have hne : t ≠ 1 := ne_of_gt ht1
    simp only [shearerF', hne, ↓reduceIte]
    have hcub := log_le_cubic_rational t (by linarith)
    have hden : 0 < (t - 1) ^ 3 := cube_pos_of_pos (by linarith)
    rw [le_div_iff₀ hden]
    nlinarith
  intro x hx y hy hxy
  rcases lt_trichotomy x 1 with hx1 | rfl | hx1
  · rcases lt_trichotomy y 1 with hy1 | rfl | hy1
    · exact hmono_lo ⟨hx, hx1⟩ ⟨hy, hy1⟩ hxy
    · exact hle1 x hx hx1
    · exact (hle1 x hx hx1).trans (hge1 y hy1)
  · rcases lt_trichotomy y 1 with hy1 | rfl | hy1
    · linarith
    · exact le_rfl
    · exact hge1 y hy1
  · exact hmono_hi hx1 (lt_of_lt_of_le hx1 hxy) hxy

private lemma shearerF_anti : AntitoneOn shearerF (Set.Ioi 0) := by
  have hcont : ContinuousOn shearerF (Set.Ioi 0) := by
    intro t ht
    by_cases ht1 : t = 1
    · subst ht1; exact shearerF_continuousAt_one.continuousWithinAt
    · exact (shearerF_hasDerivAt ht ht1).continuousAt.continuousWithinAt
  have hanti_lo : AntitoneOn shearerF (Set.Ioc 0 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ioc 0 1)
    · exact hcont.mono (fun t ht => ht.1)
    · intro t ht
      have ht' : 0 < t ∧ t < 1 := by simpa [interior_Ioc] using ht
      exact (shearerF_hasDerivAt ht'.1 (ne_of_lt ht'.2)).differentiableAt.differentiableWithinAt
    · intro t ht
      have ht' : 0 < t ∧ t < 1 := by simpa [interior_Ioc] using ht
      rw [(shearerF_hasDerivAt ht'.1 (ne_of_lt ht'.2)).deriv]
      exact shearerF'_nonpos t ht'.1
  have hanti_hi : AntitoneOn shearerF (Set.Ici 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 1)
    · exact hcont.mono (fun t ht => show (0 : ℝ) < t by have : 1 ≤ t := ht; linarith)
    · intro t ht
      have ht' : 1 < t := by simpa [interior_Ici] using ht
      exact (shearerF_hasDerivAt (by linarith) (ne_of_gt ht')).differentiableAt.differentiableWithinAt
    · intro t ht
      have ht' : 1 < t := by simpa [interior_Ici] using ht
      rw [(shearerF_hasDerivAt (by linarith) (ne_of_gt ht')).deriv]
      exact shearerF'_nonpos t (by linarith)
  intro x hx y hy hxy
  rcases le_or_gt y 1 with hy1 | hy1
  · exact hanti_lo ⟨hx, hxy.trans hy1⟩ ⟨hy, hy1⟩ hxy
  · rcases le_or_gt x 1 with hx1 | hx1
    · exact (hanti_hi (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr (le_of_lt hy1)) (le_of_lt hy1)).trans
        (hanti_lo ⟨hx, hx1⟩ ⟨by norm_num, le_rfl⟩ hx1)
    · exact hanti_hi (Set.mem_Ici.mpr (le_of_lt hx1)) (Set.mem_Ici.mpr (le_of_lt hy1)) hxy

private lemma shearerF_ode (d : ℝ) (hd : 0 < d) :
    (1 + d) * shearerF d - 1 = d * (1 - d) * shearerF' d := by
  by_cases h1 : d = 1
  · subst h1; simp [shearerF, shearerF']; norm_num
  · have h0 : d ≠ 0 := ne_of_gt hd
    have hsub : d - 1 ≠ 0 := sub_ne_zero.mpr h1
    simp only [shearerF, shearerF', h0, h1, ↓reduceIte]
    field_simp
    ring

private lemma shearerF_tangent (d x : ℝ) (hd : 0 < d) (hx : 0 ≤ x) :
    shearerF d + (x - d) * shearerF' d ≤ shearerF x := by
  rcases eq_or_lt_of_le hx with rfl | hx_pos
  · have hf0 : shearerF 0 = 1 := by simp [shearerF]
    rw [hf0, zero_sub]
    by_cases hd1 : d = 1
    · subst hd1; simp [shearerF, shearerF']; norm_num
    · have hode := shearerF_ode d hd
      have hsub : 1 - d ≠ 0 := by intro h; apply hd1; linarith
      have hfd_rel : (1 - d) * (1 - shearerF d + d * shearerF' d) = d * (2 * shearerF d - 1) := by
        nlinarith [hode]
      have hprod_nonneg : 0 ≤ (1 - d) * (d * (2 * shearerF d - 1)) := by
        rcases lt_or_gt_of_ne hd1 with hlt | hgt
        · have hge : shearerF 1 ≤ shearerF d := shearerF_anti hd (by norm_num) (le_of_lt hlt)
          have hf1 : shearerF 1 = 1 / 2 := by simp [shearerF]
          rw [hf1] at hge
          have h1d : 0 < 1 - d := by linarith
          have h2f : 0 ≤ 2 * shearerF d - 1 := by linarith
          exact mul_nonneg (le_of_lt h1d) (mul_nonneg (le_of_lt hd) h2f)
        · have hle : shearerF d ≤ shearerF 1 := shearerF_anti (by norm_num) hd (le_of_lt hgt)
          have hf1 : shearerF 1 = 1 / 2 := by simp [shearerF]
          rw [hf1] at hle
          have h1d : 1 - d < 0 := by linarith
          have h2f : 2 * shearerF d - 1 ≤ 0 := by linarith
          exact mul_nonneg_of_nonpos_of_nonpos (le_of_lt h1d) (mul_nonpos_of_nonneg_of_nonpos (le_of_lt hd) h2f)
      have hsq : 0 < (1 - d) ^ 2 := sq_pos_of_ne_zero hsub
      have hmul_nn : 0 ≤ (1 - d) ^ 2 * (1 - shearerF d + d * shearerF' d) := by
        have h1 : (1 - d) ^ 2 * (1 - shearerF d + d * shearerF' d) =
            (1 - d) * ((1 - d) * (1 - shearerF d + d * shearerF' d)) := by ring
        rw [h1, hfd_rel]; exact hprod_nonneg
      have hres : 0 ≤ 1 - shearerF d + d * shearerF' d := nonneg_of_mul_nonneg_right hmul_nn hsq
      linarith
  · let g : ℝ → ℝ := fun t => shearerF t - shearerF d - (t - d) * shearerF' d
    have hg_cont : ContinuousOn g (Set.Ioi 0) := by
      intro t ht
      have hfc : ContinuousAt shearerF t := by
        by_cases ht1 : t = 1
        · subst ht1; exact shearerF_continuousAt_one
        · exact (shearerF_hasDerivAt ht ht1).continuousAt
      have hlin : ContinuousAt (fun s => shearerF d + (s - d) * shearerF' d) t := by fun_prop
      have : ContinuousAt g t := by
        have heq : g = fun s => shearerF s - (shearerF d + (s - d) * shearerF' d) := by
          ext s; dsimp [g]; ring
        rw [heq]; exact hfc.sub hlin
      exact this.continuousWithinAt
    have hg_deriv : ∀ t, 0 < t → t ≠ 1 → HasDerivAt g (shearerF' t - shearerF' d) t := by
      intro t ht ht1
      have h1 := (shearerF_hasDerivAt ht ht1).sub_const (shearerF d)
      have h2 : HasDerivAt (fun s : ℝ => (s - d) * shearerF' d) (shearerF' d) t := by
        simpa using ((hasDerivAt_id t).sub_const d).mul_const (shearerF' d)
      exact h1.sub h2
    have hgd : g d = 0 := by simp [g]
    have hgx : 0 ≤ g x := by
      by_cases hdx : d ≤ x
      · have hmono_seg : ∀ a b : ℝ, d ≤ a → a ≤ b → (1 ∉ Set.Ioo a b) → g a ≤ g b := by
          intro a b hda hab h1out
          rcases eq_or_lt_of_le hab with rfl | hlt
          · exact le_rfl
          · have hmono : MonotoneOn g (Set.Icc a b) := by
              apply monotoneOn_of_deriv_nonneg (convex_Icc a b)
              · exact hg_cont.mono (fun t ht => show (0 : ℝ) < t by linarith [ht.1])
              · intro t ht
                rw [interior_Icc] at ht
                have ht1 : t ≠ 1 := fun heq => h1out (heq ▸ ht)
                exact (hg_deriv t (by linarith [ht.1]) ht1).differentiableAt.differentiableWithinAt
              · intro t ht
                rw [interior_Icc] at ht
                have ht1 : t ≠ 1 := fun heq => h1out (heq ▸ ht)
                rw [(hg_deriv t (by linarith [ht.1]) ht1).deriv]
                have hdt : d ≤ t := by linarith [ht.1]
                have := shearerF'_mono hd (show (0 : ℝ) < t by linarith [ht.1]) hdt
                linarith
            exact hmono (Set.left_mem_Icc.mpr hab) (Set.right_mem_Icc.mpr hab) hab
        by_cases h1in : 1 ∈ Set.Ioo d x
        · have h1 := hmono_seg d 1 le_rfl (le_of_lt h1in.1) (fun h => lt_irrefl 1 h.2)
          have h2 := hmono_seg 1 x (le_of_lt h1in.1) (le_of_lt h1in.2) (fun h => lt_irrefl 1 h.1)
          linarith
        · have := hmono_seg d x le_rfl hdx h1in
          linarith
      · have hxd : x ≤ d := le_of_not_ge hdx
        have hanti_seg : ∀ a b : ℝ, 0 < a → a ≤ b → b ≤ d → (1 ∉ Set.Ioo a b) → g b ≤ g a := by
          intro a b ha hab hbd h1out
          rcases eq_or_lt_of_le hab with rfl | hlt
          · exact le_rfl
          · have hanti : AntitoneOn g (Set.Icc a b) := by
              apply antitoneOn_of_deriv_nonpos (convex_Icc a b)
              · exact hg_cont.mono (fun t ht => show (0 : ℝ) < t by linarith [ht.1])
              · intro t ht
                rw [interior_Icc] at ht
                have ht1 : t ≠ 1 := fun heq => h1out (heq ▸ ht)
                exact (hg_deriv t (by linarith [ht.1]) ht1).differentiableAt.differentiableWithinAt
              · intro t ht
                rw [interior_Icc] at ht
                have ht1 : t ≠ 1 := fun heq => h1out (heq ▸ ht)
                rw [(hg_deriv t (by linarith [ht.1]) ht1).deriv]
                have htd : t ≤ d := by linarith [ht.2]
                have := shearerF'_mono (show (0 : ℝ) < t by linarith [ht.1]) hd htd
                linarith
            exact hanti (Set.left_mem_Icc.mpr hab) (Set.right_mem_Icc.mpr hab) hab
        by_cases h1in : 1 ∈ Set.Ioo x d
        · have h1 := hanti_seg x 1 hx_pos (le_of_lt h1in.1) (le_of_lt h1in.2)
            (fun h => lt_irrefl 1 h.2)
          have h2 := hanti_seg 1 d (by norm_num) (le_of_lt h1in.2) le_rfl
            (fun h => lt_irrefl 1 h.1)
          linarith
        · have := hanti_seg x d hx_pos hxd le_rfl h1in
          linarith
    dsimp [g] at hgx
    linarith

private lemma shearer_indep_bound :
    ∀ n : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      Fintype.card V = n → G.CliqueFree 3 →
      ∃ I : Finset V, G.IsIndepSet (I : Set V) ∧
        (n : ℝ) * shearerF (if n = 0 then 0 else (2 * G.edgeFinset.card : ℝ) / n) ≤ (I.card : ℝ) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro V _ _ G _ hcard htri
    rcases Nat.eq_zero_or_pos n with rfl | hn_pos
    · refine ⟨∅, by simp [SimpleGraph.IsIndepSet], by simp⟩
    · have hn_ne : n ≠ 0 := by omega
      have hn_rpos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn_pos
      set d : ℝ := (2 * G.edgeFinset.card : ℝ) / (n : ℝ) with hd_def
      have hite : (if n = 0 then (0 : ℝ) else (2 * G.edgeFinset.card : ℝ) / n) = d := by
        simp [hn_ne, hd_def]
      rw [hite]
      rcases Nat.eq_zero_or_pos G.edgeFinset.card with he0 | he_pos
      · have hd0 : d = 0 := by simp [hd_def, he0]
        rw [hd0]
        refine ⟨Finset.univ, ?_, ?_⟩
        · intro u _ v _ huv hadj
          have hmem : s(u, v) ∈ G.edgeFinset := G.mem_edgeFinset.mpr hadj
          rw [Finset.card_eq_zero.mp he0] at hmem
          exact Finset.notMem_empty _ hmem
        · simp [shearerF, hcard]
      · have hd_pos : 0 < d := by
          rw [hd_def]
          have : (0 : ℝ) < (G.edgeFinset.card : ℝ) := Nat.cast_pos.mpr he_pos
          positivity
        have hstep : ∀ v : V, ∃ Iv : Finset V, G.IsIndepSet (Iv : Set V) ∧
            (1 : ℝ) + ((n - 1 - G.degree v : ℕ) : ℝ) * shearerF d +
              ((2 * (G.edgeFinset.filter fun e => ∀ u ∈ e, u ≠ v ∧ ¬ G.Adj v u).card : ℝ) -
                d * ((n - 1 - G.degree v : ℕ) : ℝ)) * shearerF' d ≤ (Iv.card : ℝ) := by
          intro v
          let U : Finset V := Finset.univ.filter fun w => w ≠ v ∧ ¬ G.Adj v w
          let W := {w : V // w ∈ U}
          let H : SimpleGraph W := G.induce (U : Set V)
          have hU_card : U.card = n - 1 - G.degree v := by
            have hv_not_nb : v ∉ G.neighborFinset v := by
              rw [SimpleGraph.mem_neighborFinset]
              exact G.loopless.irrefl v
            have hcompl : U = Finset.univ \ (insert v (G.neighborFinset v)) := by
              ext w
              simp [U, SimpleGraph.mem_neighborFinset]
            have hsub : insert v (G.neighborFinset v) ⊆ Finset.univ := Finset.subset_univ _
            rw [hcompl, Finset.card_sdiff, Finset.inter_eq_left.mpr hsub, Finset.card_univ, hcard,
              Finset.card_insert_of_notMem hv_not_nb, G.card_neighborFinset_eq_degree v]
            omega
          have hW_card : Fintype.card W = n - 1 - G.degree v := by
            rw [Fintype.card_coe, hU_card]
          have hW_lt : Fintype.card W < n := by
            rw [hW_card]; omega
          have hH_tri : H.CliqueFree 3 := by
            intro t ht
            apply htri (t.map ⟨Subtype.val, Subtype.val_injective⟩)
            refine ⟨?_, by simp [ht.2]⟩
            intro x hx y hy hxy
            rcases Finset.mem_map.mp hx with ⟨a, ha, rfl⟩
            rcases Finset.mem_map.mp hy with ⟨b, hb, rfl⟩
            exact ht.1 ha hb (fun h => hxy (congrArg Subtype.val h))
          obtain ⟨J, hJind, hJbound⟩ := ih (Fintype.card W) hW_lt W H rfl hH_tri
          let Jmap : Finset V := J.map ⟨Subtype.val, Subtype.val_injective⟩
          have hv_not_mem : v ∉ Jmap := by
            intro hv
            rcases Finset.mem_map.mp hv with ⟨w, _, hw⟩
            exact (Finset.mem_filter.mp w.2).2.1 hw
          let Iv : Finset V := insert v Jmap
          have hIv_ind : G.IsIndepSet (Iv : Set V) := by
            intro x hx y hy hxy hadj
            simp only [Iv, Finset.coe_insert, Set.mem_insert_iff] at hx hy
            rcases hx with rfl | hxJ
            · rcases hy with rfl | hyJ
              · exact hxy rfl
              · rcases Finset.mem_map.mp (Finset.mem_coe.mp hyJ) with ⟨w, _, rfl⟩
                exact (Finset.mem_filter.mp w.2).2.2 hadj
            · rcases Finset.mem_map.mp (Finset.mem_coe.mp hxJ) with ⟨w1, hw1, rfl⟩
              rcases hy with rfl | hyJ
              · exact (Finset.mem_filter.mp w1.2).2.2 hadj.symm
              · rcases Finset.mem_map.mp (Finset.mem_coe.mp hyJ) with ⟨w2, hw2, rfl⟩
                exact hJind hw1 hw2 (fun h => hxy (congrArg Subtype.val h)) hadj
          have hIv_card : (Iv.card : ℝ) = 1 + (J.card : ℝ) := by
            rw [Finset.card_insert_of_notMem hv_not_mem, Finset.card_map]
            push_cast; ring
          have hH_edges : H.edgeFinset.card =
              (G.edgeFinset.filter fun e => ∀ u ∈ e, u ≠ v ∧ ¬ G.Adj v u).card := by
            refine Finset.card_bij (fun e _ => e.map Subtype.val) ?_ ?_ ?_
            · intro e he
              rw [SimpleGraph.mem_edgeFinset] at he
              rw [Finset.mem_filter, SimpleGraph.mem_edgeFinset]
              induction e using Sym2.ind with
              | _ a b =>
                refine ⟨he, ?_⟩
                intro u hu
                simp only [Sym2.map_mk, Sym2.mem_iff] at hu
                rcases hu with rfl | rfl
                · exact (Finset.mem_filter.mp a.2).2
                · exact (Finset.mem_filter.mp b.2).2
            · intro e1 _ e2 _ hmap
              exact Sym2.map.injective Subtype.val_injective hmap
            · intro e he
              rw [Finset.mem_filter, SimpleGraph.mem_edgeFinset] at he
              induction e using Sym2.ind with
              | _ a b =>
                have ha : a ∈ U := Finset.mem_filter.mpr
                  ⟨Finset.mem_univ a, he.2 a (Sym2.mem_mk_left a b)⟩
                have hb : b ∈ U := Finset.mem_filter.mpr
                  ⟨Finset.mem_univ b, he.2 b (Sym2.mem_mk_right a b)⟩
                refine ⟨s(⟨a, ha⟩, ⟨b, hb⟩), ?_, rfl⟩
                rw [SimpleGraph.mem_edgeFinset]
                exact he.1
          refine ⟨Iv, hIv_ind, ?_⟩
          rw [hIv_card]
          rw [hW_card, hH_edges] at hJbound
          set nv := n - 1 - G.degree v
          set ev := (G.edgeFinset.filter fun e => ∀ u ∈ e, u ≠ v ∧ ¬ G.Adj v u).card
          rcases Nat.eq_zero_or_pos nv with hnv0 | hnv_pos
          · have hev0 : ev = 0 := by
              rw [Finset.card_eq_zero]
              ext e
              simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
              intro _ hall
              induction e using Sym2.ind with
              | _ a b =>
                have ha : a ∈ U := Finset.mem_filter.mpr
                  ⟨Finset.mem_univ a, hall a (Sym2.mem_mk_left a b)⟩
                have : 0 < U.card := Finset.card_pos.mpr ⟨a, ha⟩
                omega
            simp only [hnv0, hev0, Nat.cast_zero, mul_zero, zero_mul, sub_zero, add_zero]
            have : (0 : ℝ) ≤ (J.card : ℝ) := Nat.cast_nonneg _
            linarith
          · have hnv_ne : nv ≠ 0 := by omega
            have hnv_rpos : (0 : ℝ) < (nv : ℝ) := Nat.cast_pos.mpr hnv_pos
            simp only [hnv_ne, ↓reduceIte] at hJbound
            have htang := shearerF_tangent d ((2 * ev : ℝ) / (nv : ℝ)) hd_pos (by positivity)
            have hmul := mul_le_mul_of_nonneg_left htang (le_of_lt hnv_rpos)
            have hcancel : (nv : ℝ) * (((2 * ev : ℝ) / (nv : ℝ) - d) * shearerF' d) =
                ((2 * ev : ℝ) - d * (nv : ℝ)) * shearerF' d := by
              have hnv_rne : (nv : ℝ) ≠ 0 := ne_of_gt hnv_rpos
              field_simp
            have hcalc : (nv : ℝ) * shearerF d + ((2 * ev : ℝ) - d * (nv : ℝ)) * shearerF' d ≤
                (nv : ℝ) * shearerF ((2 * ev : ℝ) / (nv : ℝ)) := by
              linarith [mul_add (nv : ℝ) (shearerF d) (((2 * ev : ℝ) / (nv : ℝ) - d) * shearerF' d)]
            linarith
        choose Iv hIv_ind hIv_bound using hstep
        have hVne : (Finset.univ : Finset V).Nonempty :=
          Finset.univ_nonempty_iff.mpr (Fintype.card_pos_iff.mp (by omega))
        obtain ⟨v₀, _, hv₀_max⟩ := Finset.exists_max_image Finset.univ (fun v => (Iv v).card) hVne
        refine ⟨Iv v₀, hIv_ind v₀, ?_⟩
        have hsum_ub : ∑ v : V, ((Iv v).card : ℝ) ≤ (n : ℝ) * ((Iv v₀).card : ℝ) := by
          calc ∑ v : V, ((Iv v).card : ℝ)
              ≤ ∑ _v : V, ((Iv v₀).card : ℝ) :=
                Finset.sum_le_sum fun v _ => Nat.cast_le.mpr (hv₀_max v (Finset.mem_univ v))
            _ = (n : ℝ) * ((Iv v₀).card : ℝ) := by
                rw [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]
        have hedge_rem : ∀ v : V,
            (G.edgeFinset.filter fun e => ∀ u ∈ e, u ≠ v ∧ ¬ G.Adj v u).card +
              ∑ u ∈ G.neighborFinset v, G.degree u = G.edgeFinset.card := by
          intro v
          let S_keep := G.edgeFinset.filter fun e => ∀ u ∈ e, u ≠ v ∧ ¬ G.Adj v u
          let S_rem := G.edgeFinset.filter fun e => ¬ (∀ u ∈ e, u ≠ v ∧ ¬ G.Adj v u)
          have hpart : S_keep.card + S_rem.card = G.edgeFinset.card :=
            Finset.card_filter_add_card_filter_not _
          suffices hrem : S_rem.card = ∑ u ∈ G.neighborFinset v, G.degree u by
            change S_keep.card + ∑ u ∈ G.neighborFinset v, G.degree u = G.edgeFinset.card
            omega
          have hbi : ∑ u ∈ G.neighborFinset v, G.degree u =
              ((G.neighborFinset v).sigma fun u => G.neighborFinset u).card := by
            rw [Finset.card_sigma]
            refine Finset.sum_congr rfl fun u _ => (G.card_neighborFinset_eq_degree u).symm
          rw [hbi]
          refine (Finset.card_bij (fun p _ => s(p.1, p.2)) ?_ ?_ ?_).symm
          · intro p hp
            rcases Finset.mem_sigma.mp hp with ⟨hu, hw⟩
            rw [SimpleGraph.mem_neighborFinset] at hu hw
            rw [Finset.mem_filter, SimpleGraph.mem_edgeFinset]
            refine ⟨hw, fun hall => ?_⟩
            exact (hall p.1 (Sym2.mem_mk_left p.1 p.2)).2 hu
          · intro p1 hp1 p2 hp2 heq
            rcases Finset.mem_sigma.mp hp1 with ⟨hu1, hw1⟩
            rcases Finset.mem_sigma.mp hp2 with ⟨hu2, hw2⟩
            rw [SimpleGraph.mem_neighborFinset] at hu1 hw1 hu2 hw2
            rw [Sym2.eq_iff] at heq
            rcases heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · exact Sigma.ext h1 (heq_of_eq h2)
            · exfalso
              rw [h2] at hw1
              have hne1 : v ≠ p1.1 := G.ne_of_adj hu1
              have hne2 : v ≠ p2.1 := G.ne_of_adj hu2
              have hne3 : p1.1 ≠ p2.1 := G.ne_of_adj hw1
              apply htri {v, p1.1, p2.1}
              refine ⟨?_, ?_⟩
              · simp only [Finset.coe_insert, Finset.coe_singleton, SimpleGraph.isClique_iff,
                  Set.Pairwise]
                intro x hx y hy hxy
                simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
                rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
                · exact absurd rfl hxy
                · exact hu1
                · exact hu2
                · exact hu1.symm
                · exact absurd rfl hxy
                · exact hw1
                · exact hu2.symm
                · exact hw1.symm
                · exact absurd rfl hxy
              · rw [Finset.card_insert_of_notMem (by simp [hne1, hne2]),
                  Finset.card_insert_of_notMem (by simp [hne3]), Finset.card_singleton]
          · intro e he
            rw [Finset.mem_filter, SimpleGraph.mem_edgeFinset] at he
            induction e using Sym2.ind with
            | _ a b =>
              have hnot : ¬ (a ≠ v ∧ ¬ G.Adj v a) ∨ ¬ (b ≠ v ∧ ¬ G.Adj v b) := by
                by_contra hboth
                push Not at hboth
                apply he.2
                intro u hu
                rw [Sym2.mem_iff] at hu
                rcases hu with rfl | rfl
                · exact hboth.1
                · exact hboth.2
              rcases hnot with ha | hb
              · by_cases hav : a = v
                · subst hav
                  refine ⟨⟨b, a⟩, Finset.mem_sigma.mpr ⟨?_, ?_⟩, Sym2.eq_swap⟩
                  · exact (SimpleGraph.mem_neighborFinset G a b).mpr he.1
                  · exact (SimpleGraph.mem_neighborFinset G b a).mpr he.1.symm
                · have hva : G.Adj v a := by tauto
                  refine ⟨⟨a, b⟩, Finset.mem_sigma.mpr ⟨?_, ?_⟩, rfl⟩
                  · exact (SimpleGraph.mem_neighborFinset G v a).mpr hva
                  · exact (SimpleGraph.mem_neighborFinset G a b).mpr he.1
              · by_cases hbv : b = v
                · subst hbv
                  refine ⟨⟨a, b⟩, Finset.mem_sigma.mpr ⟨?_, ?_⟩, rfl⟩
                  · exact (SimpleGraph.mem_neighborFinset G b a).mpr he.1.symm
                  · exact (SimpleGraph.mem_neighborFinset G a b).mpr he.1
                · have hvb : G.Adj v b := by tauto
                  refine ⟨⟨b, a⟩, Finset.mem_sigma.mpr ⟨?_, ?_⟩, Sym2.eq_swap⟩
                  · exact (SimpleGraph.mem_neighborFinset G v b).mpr hvb
                  · exact (SimpleGraph.mem_neighborFinset G b a).mpr he.1.symm
        have hsum_deg : ∑ v : V, (G.degree v : ℝ) = (n : ℝ) * d := by
          have h1 : ∑ v : V, G.degree v = 2 * G.edgeFinset.card := G.sum_degrees_eq_twice_card_edges
          have h2 : ∑ v : V, (G.degree v : ℝ) = (2 * G.edgeFinset.card : ℝ) := by exact_mod_cast h1
          rw [h2, hd_def]
          have hn_rne : (n : ℝ) ≠ 0 := ne_of_gt hn_rpos
          field_simp
        have hsum_nv : ∑ v : V, ((n - 1 - G.degree v : ℕ) : ℝ) = (n : ℝ) * (n - 1 - d) := by
          have hle : ∀ v : V, G.degree v + 1 ≤ n := by
            intro v
            have hlt : G.degree v < Fintype.card V := G.degree_lt_card_verts v
            omega
          have h1 : ∑ v : V, ((n - 1 - G.degree v : ℕ) : ℝ) =
              ∑ v : V, ((n : ℝ) - 1 - (G.degree v : ℝ)) := by
            refine Finset.sum_congr rfl fun v _ => ?_
            have hv := hle v
            rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_one]
          rw [h1, Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_const,
            Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul, nsmul_eq_mul, mul_one,
            hsum_deg]
          ring
        have hsum_deg_sq_double :
            ∑ v : V, ∑ u ∈ G.neighborFinset v, (G.degree u : ℝ) =
              ∑ u : V, (G.degree u : ℝ) ^ 2 := by
          have hswap : ∀ v : V, ∑ u ∈ G.neighborFinset v, (G.degree u : ℝ) =
              ∑ u : V, if G.Adj v u then (G.degree u : ℝ) else 0 := by
            intro v
            rw [← Finset.sum_filter]
            refine Finset.sum_congr ?_ (fun _ _ => rfl)
            ext u; simp [SimpleGraph.mem_neighborFinset]
          simp_rw [hswap]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun u _ => ?_
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
          have hfilt : (Finset.univ.filter fun v => G.Adj v u).card = G.degree u := by
            rw [← G.card_neighborFinset_eq_degree u]
            congr 1
            ext v
            simp [SimpleGraph.mem_neighborFinset, SimpleGraph.adj_comm]
          rw [hfilt]; ring
        have hsum_ev :
            ∑ v : V, (2 * (G.edgeFinset.filter fun e => ∀ u ∈ e, u ≠ v ∧ ¬ G.Adj v u).card : ℝ) =
              (n : ℝ) ^ 2 * d - 2 * ∑ u : V, (G.degree u : ℝ) ^ 2 := by
          have hper : ∀ v : V,
              (2 * (G.edgeFinset.filter fun e => ∀ u ∈ e, u ≠ v ∧ ¬ G.Adj v u).card : ℝ) =
                (n : ℝ) * d - 2 * ∑ u ∈ G.neighborFinset v, (G.degree u : ℝ) := by
            intro v
            have h1 := hedge_rem v
            have h2 : ((G.edgeFinset.filter fun e => ∀ u ∈ e, u ≠ v ∧ ¬ G.Adj v u).card : ℝ) +
                ∑ u ∈ G.neighborFinset v, (G.degree u : ℝ) = (G.edgeFinset.card : ℝ) := by
              exact_mod_cast h1
            have h3 : (2 * G.edgeFinset.card : ℝ) = (n : ℝ) * d := by
              rw [hd_def]; have hn_rne : (n : ℝ) ≠ 0 := ne_of_gt hn_rpos; field_simp
            linarith
          simp_rw [hper]
          rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul,
            ← Finset.mul_sum, hsum_deg_sq_double]
          ring
        have hcs : (n : ℝ) * d ^ 2 ≤ ∑ u : V, (G.degree u : ℝ) ^ 2 := by
          have hnonneg : 0 ≤ ∑ u : V, ((G.degree u : ℝ) - d) ^ 2 :=
            Finset.sum_nonneg fun _ _ => sq_nonneg _
          have hexp : ∑ u : V, ((G.degree u : ℝ) - d) ^ 2 =
              (∑ u : V, (G.degree u : ℝ) ^ 2) - 2 * d * (∑ u : V, (G.degree u : ℝ)) +
                (n : ℝ) * d ^ 2 := by
            have h1 : ∀ u : V, ((G.degree u : ℝ) - d) ^ 2 =
                (G.degree u : ℝ) ^ 2 - 2 * d * (G.degree u : ℝ) + d ^ 2 := fun _ => by ring
            simp_rw [h1]
            rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
              Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]
          rw [hexp, hsum_deg] at hnonneg
          linarith
        have hsum_lb : (n : ℝ) * ((n : ℝ) * shearerF d) ≤ ∑ v : V, ((Iv v).card : ℝ) := by
          have h1 : ∑ v : V, ((1 : ℝ) + ((n - 1 - G.degree v : ℕ) : ℝ) * shearerF d +
              ((2 * (G.edgeFinset.filter fun e => ∀ u ∈ e, u ≠ v ∧ ¬ G.Adj v u).card : ℝ) -
                d * ((n - 1 - G.degree v : ℕ) : ℝ)) * shearerF' d) ≤
              ∑ v : V, ((Iv v).card : ℝ) :=
            Finset.sum_le_sum fun v _ => hIv_bound v
          have h2 : ∑ v : V, ((1 : ℝ) + ((n - 1 - G.degree v : ℕ) : ℝ) * shearerF d +
              ((2 * (G.edgeFinset.filter fun e => ∀ u ∈ e, u ≠ v ∧ ¬ G.Adj v u).card : ℝ) -
                d * ((n - 1 - G.degree v : ℕ) : ℝ)) * shearerF' d) =
              (n : ℝ) + (n : ℝ) * ((n : ℝ) - 1 - d) * shearerF d +
              (((n : ℝ) ^ 2 * d - 2 * ∑ u : V, (G.degree u : ℝ) ^ 2) -
                d * ((n : ℝ) * ((n : ℝ) - 1 - d))) * shearerF' d := by
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_mul,
              ← Finset.sum_mul, Finset.sum_sub_distrib, hsum_ev, ← Finset.mul_sum,
              Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul, mul_one,
              hsum_nv]
          have h3 : (n : ℝ) * (d * (1 - d)) * shearerF' d ≤
              (((n : ℝ) ^ 2 * d - 2 * ∑ u : V, (G.degree u : ℝ) ^ 2) -
                d * ((n : ℝ) * ((n : ℝ) - 1 - d))) * shearerF' d := by
            have hf'le : shearerF' d ≤ 0 := shearerF'_nonpos d hd_pos
            have hcoeff : ((n : ℝ) ^ 2 * d - 2 * ∑ u : V, (G.degree u : ℝ) ^ 2) -
                d * ((n : ℝ) * ((n : ℝ) - 1 - d)) ≤ (n : ℝ) * (d * (1 - d)) := by
              nlinarith [hcs]
            exact mul_le_mul_of_nonpos_right hcoeff hf'le
          have hode := shearerF_ode d hd_pos
          have halg : (n : ℝ) * ((n : ℝ) * shearerF d) =
              (n : ℝ) + (n : ℝ) * ((n : ℝ) - 1 - d) * shearerF d +
                (n : ℝ) * (d * (1 - d)) * shearerF' d := by
            nlinarith [hode]
          linarith
        have hfinal : (n : ℝ) * ((n : ℝ) * shearerF d) ≤ (n : ℝ) * ((Iv v₀).card : ℝ) :=
          hsum_lb.trans hsum_ub
        exact le_of_mul_le_mul_left hfinal hn_rpos

private lemma eventually_shearer_threshold (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ k : ℕ in atTop,
      2 < (k : ℝ) ∧
      (k : ℝ) ≤ (1 + δ) * ((k : ℝ) ^ 2 / (2 * Real.log k)) * shearerF ((k : ℝ) / 2) := by
  have hlog : Tendsto (fun k : ℕ => Real.log (k : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hconst : ∀ᶠ k : ℕ in atTop,
      (Real.log 2 + 1) * (1 + δ) / (δ / 2) < Real.log (k : ℝ) :=
    hlog.eventually_gt_atTop _
  have hbig : ∀ᶠ k : ℕ in atTop, 4 ≤ k := eventually_ge_atTop 4
  filter_upwards [hconst, hbig] with k hlk hk4
  have hkr : (4 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk4
  have hk_pos : (0 : ℝ) < (k : ℝ) := by linarith
  have hlogk_pos : 0 < Real.log (k : ℝ) := Real.log_pos (by linarith)
  have hd_gt1 : 1 < (k : ℝ) / 2 := by linarith
  have hd_ne0 : (k : ℝ) / 2 ≠ 0 := by linarith
  have hd_ne1 : (k : ℝ) / 2 ≠ 1 := by linarith
  refine ⟨by linarith, ?_⟩
  simp only [shearerF, hd_ne0, hd_ne1, ↓reduceIte]
  have hlog_half : Real.log ((k : ℝ) / 2) = Real.log (k : ℝ) - Real.log 2 :=
    Real.log_div (ne_of_gt hk_pos) (by norm_num)
  rw [hlog_half]
  have hnum_ge : (k : ℝ) / 2 * (Real.log (k : ℝ) - Real.log 2 - 1) ≤
      (k : ℝ) / 2 * (Real.log (k : ℝ) - Real.log 2) - (k : ℝ) / 2 + 1 := by linarith
  have hden_le : ((k : ℝ) / 2 - 1) ^ 2 ≤ ((k : ℝ) / 2) ^ 2 := by nlinarith
  have hden_pos : 0 < ((k : ℝ) / 2 - 1) ^ 2 := by nlinarith
  have hlog_ge : 0 ≤ Real.log (k : ℝ) - Real.log 2 - 1 := by
    have h1 : (Real.log 2 + 1) * (1 + δ) / (δ / 2) ≥ Real.log 2 + 1 := by
      rw [ge_iff_le, le_div_iff₀ (by positivity)]
      have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      nlinarith
    linarith
  have hsf_ge : (Real.log (k : ℝ) - Real.log 2 - 1) / ((k : ℝ) / 2) ≤
      ((k : ℝ) / 2 * (Real.log (k : ℝ) - Real.log 2) - (k : ℝ) / 2 + 1) / ((k : ℝ) / 2 - 1) ^ 2 := by
    calc (Real.log (k : ℝ) - Real.log 2 - 1) / ((k : ℝ) / 2)
        = ((k : ℝ) / 2 * (Real.log (k : ℝ) - Real.log 2 - 1)) / ((k : ℝ) / 2) ^ 2 := by
            field_simp
      _ ≤ ((k : ℝ) / 2 * (Real.log (k : ℝ) - Real.log 2 - 1)) / ((k : ℝ) / 2 - 1) ^ 2 := by
            exact div_le_div_of_nonneg_left (by positivity) hden_pos hden_le
      _ ≤ ((k : ℝ) / 2 * (Real.log (k : ℝ) - Real.log 2) - (k : ℝ) / 2 + 1) /
            ((k : ℝ) / 2 - 1) ^ 2 :=
            div_le_div_of_nonneg_right hnum_ge (le_of_lt hden_pos)
  have hprod_ge : (k : ℝ) ≤ (1 + δ) * ((k : ℝ) ^ 2 / (2 * Real.log (k : ℝ))) *
      ((Real.log (k : ℝ) - Real.log 2 - 1) / ((k : ℝ) / 2)) := by
    have hsimp : (1 + δ) * ((k : ℝ) ^ 2 / (2 * Real.log (k : ℝ))) *
        ((Real.log (k : ℝ) - Real.log 2 - 1) / ((k : ℝ) / 2)) =
        (k : ℝ) * ((1 + δ) * (Real.log (k : ℝ) - Real.log 2 - 1) / Real.log (k : ℝ)) := by
      field_simp
    rw [hsimp]
    have hone_le : 1 ≤ (1 + δ) * (Real.log (k : ℝ) - Real.log 2 - 1) / Real.log (k : ℝ) := by
      rw [one_le_div hlogk_pos]
      have hdiv : (Real.log 2 + 1) * (1 + δ) < (δ / 2) * Real.log (k : ℝ) := by
        rw [div_lt_iff₀ (by positivity)] at hlk
        linarith
      nlinarith
    nlinarith
  have hpref_nonneg : 0 ≤ (1 + δ) * ((k : ℝ) ^ 2 / (2 * Real.log (k : ℝ))) := by positivity
  exact hprod_ge.trans (mul_le_mul_of_nonneg_left hsf_ge hpref_nonneg)

end Erdos165R1H2Proof

open Erdos165R1H2Proof in
theorem OMA.solution : OMA.R_Erdos165_erdos_165_variants_conjecture_R1.H2 := by
  intro δ hδ
  filter_upwards [eventually_shearer_threshold δ hδ] with k ⟨hk2, hkthr⟩
  classical
  intro n G hn htri hedge hind
  have hlogk_pos : 0 < Real.log (k : ℝ) := Real.log_pos (by linarith)
  have hn_pos : 0 < n := by
    have : (0 : ℝ) < (n : ℝ) := lt_of_le_of_lt (by positivity) hn
    exact_mod_cast this
  have hn_ne : n ≠ 0 := by omega
  obtain ⟨I, hIind, hIbound⟩ := shearer_indep_bound n (Fin n) G (Fintype.card_fin n) htri
  simp only [hn_ne, ↓reduceIte] at hIbound
  have hedge_fin : G.edgeFinset.card = G.edgeSet.ncard := by
    rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
  have hd_le : (2 * G.edgeFinset.card : ℝ) / (n : ℝ) ≤ (k : ℝ) / 2 := by
    rw [hedge_fin]
    have h4 : (4 * G.edgeSet.ncard : ℝ) ≤ (n : ℝ) * (k : ℝ) := by exact_mod_cast hedge
    have hnr : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn_pos
    rw [div_le_div_iff₀ hnr (by norm_num : (0 : ℝ) < 2)]
    linarith
  have hk_half_pos : (0 : ℝ) < (k : ℝ) / 2 := by linarith
  have hsf_mono : shearerF ((k : ℝ) / 2) ≤ shearerF ((2 * G.edgeFinset.card : ℝ) / (n : ℝ)) := by
    rcases Nat.eq_zero_or_pos G.edgeFinset.card with he0 | he_pos
    · have h0 : (2 * G.edgeFinset.card : ℝ) / (n : ℝ) = 0 := by simp [he0]
      rw [h0]
      have hf0 : shearerF 0 = 1 := by simp [shearerF]
      have hf1 : shearerF 1 = 1 / 2 := by simp [shearerF]
      have hle1 : shearerF ((k : ℝ) / 2) ≤ shearerF 1 :=
        shearerF_anti (show (0 : ℝ) < 1 by norm_num) hk_half_pos (by linarith)
      linarith
    · have hd_pos : 0 < (2 * G.edgeFinset.card : ℝ) / (n : ℝ) := by
        have : (0 : ℝ) < (G.edgeFinset.card : ℝ) := Nat.cast_pos.mpr he_pos
        positivity
      exact shearerF_anti hd_pos hk_half_pos hd_le
  have hsf_pos : 0 < shearerF ((k : ℝ) / 2) := by
    have hd_gt1 : 1 < (k : ℝ) / 2 := by linarith
    have hd_ne0 : (k : ℝ) / 2 ≠ 0 := by linarith
    have hd_ne1 : (k : ℝ) / 2 ≠ 1 := by linarith
    simp only [shearerF, hd_ne0, hd_ne1, ↓reduceIte]
    have hlog_ge : 2 * ((k : ℝ) / 2 - 1) / ((k : ℝ) / 2 + 1) ≤ Real.log ((k : ℝ) / 2) :=
      (log_le_or_ge_rational ((k : ℝ) / 2) hk_half_pos).1 (le_of_lt hd_gt1)
    have hden_pos : 0 < ((k : ℝ) / 2 - 1) ^ 2 := by nlinarith
    have hnum_pos : 0 < (k : ℝ) / 2 * Real.log ((k : ℝ) / 2) - (k : ℝ) / 2 + 1 := by
      have h1 : 0 < (k : ℝ) / 2 + 1 := by linarith
      rw [div_le_iff₀ h1] at hlog_ge
      nlinarith
    exact div_pos hnum_pos hden_pos
  have hI_gt_k : (k : ℝ) < (I.card : ℝ) := by
    calc (k : ℝ) ≤ (1 + δ) * ((k : ℝ) ^ 2 / (2 * Real.log k)) * shearerF ((k : ℝ) / 2) := hkthr
      _ < (n : ℝ) * shearerF ((k : ℝ) / 2) := mul_lt_mul_of_pos_right hn hsf_pos
      _ ≤ (n : ℝ) * shearerF ((2 * G.edgeFinset.card : ℝ) / (n : ℝ)) :=
            mul_le_mul_of_nonneg_left hsf_mono (Nat.cast_nonneg n)
      _ ≤ (I.card : ℝ) := hIbound
  have hk_le_I : k ≤ I.card := by
    have : k < I.card := by exact_mod_cast hI_gt_k
    omega
  obtain ⟨S, hSI, hScard⟩ := Finset.exists_subset_card_eq hk_le_I
  exact hind S ⟨hIind.mono (Finset.coe_subset.mpr hSI), hScard⟩
