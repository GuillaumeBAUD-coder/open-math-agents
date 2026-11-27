import FormalConjectures.Wikipedia.SixStandardDeviations

/-!
# Self-contained proof of Spencer's "Six standard deviations suffice" theorem

We prove `SixStandardDeviations.six_standard_deviations`: for every `n : ℕ` and every family
`S : Fin n → Finset (Fin n)`, there exists `χ : Fin n → ℝ` with `χ j ∈ {-1, 1}` such that
`|∑ j ∈ S i, χ j| ≤ 6 * √n` for every `i`.

Outline:
1. For `n ≤ 36`, the constant coloring `χ ≡ 1` suffices.
2. For `37 ≤ n ≤ 10^14`, pairing coordinates `(2k, 2k+1)` with opposite independent random signs
   gives a Rademacher sum of at most `n/2` terms for each `S i`, so Hoeffding's inequality plus
   the union bound gives `2 n exp(-(6√n - 1)^2 / n) ≤ 2 n exp(-34) < 1`.
3. For `n > 10^14`, we use Spencer's entropy partial-coloring method:
   - Finite Shannon entropy on `Fin m → Bool` (`exists_fiber_large`, `H_le_log_card`, `H_prod_le`).
   - Croot–Lev–Pach algebraic proof over `ZMod 2` of Kleitman's diameter bound up to a factor of 2:
     any `C ⊆ (Fin m → Bool)` of Hamming diameter `≤ 2t` has `|C| ≤ 2 ∑_{k ≤ t} C(m, k)`.
   - Binomial Chernoff bound `∑_{k ≤ p m} C(m, k) ≤ exp(m h(p))` and quadratic entropy gap
     `log 2 - h(p) ≥ 2 (1/2 - p)^2` at `p = 43/100`.
   - Adding a single balance bucket `B₀(x) = #{j | x j = true}` forces `∑_{j ∈ U} χ j = 0`,
     letting every `S i ∩ U` be complemented to size `≤ m/2` (halving the Hoeffding variance).
   - Iterating with `β = 4/25` (`√β = 2/5`), `λ(m) = √(9 + (6/5) log(n/m))`, and stopping at
     `m ≤ (1/2) √n` yields total discrepancy `≤ (5 + 4/9 + 1/2) √n = (107/18) √n < 6 √n`.
-/

namespace OMA.Spencer

open Finset BigOperators Real
open scoped Classical

/- ## Section 1: Elementary real, exponential, and entropy inequalities -/

private noncomputable def nml (x : ℝ) : ℝ := -(x * Real.log x)

private lemma nml_zero : nml 0 = 0 := by simp [nml]

private lemma nml_one : nml 1 = 0 := by simp [nml]

private lemma nml_nonneg {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : 0 ≤ nml x := by
  unfold nml
  rcases eq_or_lt_of_le hx0 with rfl | hpos
  · simp
  · have hlog : Real.log x ≤ 0 := Real.log_nonpos hx0 hx1
    nlinarith

private lemma nml_mono_on_Icc {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ Real.exp (-1)) :
    nml a ≤ nml b := by
  rcases eq_or_lt_of_le ha with rfl | ha_pos
  · rw [nml_zero]
    exact nml_nonneg (ha.trans hab) (hb.trans (by rw [Real.exp_le_one_iff]; norm_num))
  · have hb_pos : 0 < b := lt_of_lt_of_le ha_pos hab
    have hmono : MonotoneOn (fun t : ℝ => -(t * Real.log t)) (Set.Icc a b) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc a b)
      · exact (Real.continuous_mul_log.neg).continuousOn
      · intro t ht
        rw [interior_Icc] at ht
        have ht_pos : 0 < t := lt_of_lt_of_le ha_pos ht.1.le
        exact (((hasDerivAt_id' t).mul (Real.hasDerivAt_log ht_pos.ne')).neg).differentiableAt.differentiableWithinAt
      · intro t ht
        rw [interior_Icc] at ht
        have ht_pos : 0 < t := lt_of_lt_of_le ha_pos ht.1.le
        have hd : HasDerivAt (fun x : ℝ => -(x * Real.log x)) (-(Real.log t + 1)) t := by
          have h1 := ((hasDerivAt_id' t).mul (Real.hasDerivAt_log ht_pos.ne')).neg
          have heq : -(1 * Real.log t + t * t⁻¹) = -(Real.log t + 1) := by
            rw [one_mul, mul_inv_cancel₀ ht_pos.ne']
          exact heq ▸ h1
        rw [hd.deriv]
        have hlt : Real.log t ≤ -1 := by
          have h1 : Real.log t ≤ Real.log (Real.exp (-1)) :=
            Real.log_le_log ht_pos (ht.2.le.trans hb)
          rwa [Real.log_exp] at h1
        linarith
    exact hmono ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab

private lemma nml_one_sub_le {u : ℝ} (_hu0 : 0 ≤ u) (hu1 : u < 1) :
    nml (1 - u) ≤ u := by
  unfold nml
  have hpos : 0 < 1 - u := by linarith
  have hlog : Real.log ((1 - u)⁻¹) ≤ (1 - u)⁻¹ - 1 :=
    Real.log_le_sub_one_of_pos (inv_pos.mpr hpos)
  rw [Real.log_inv] at hlog
  have hmul := mul_le_mul_of_nonneg_left hlog hpos.le
  have heq : (1 - u) * ((1 - u)⁻¹ - 1) = u := by
    rw [mul_sub, mul_inv_cancel₀ hpos.ne', mul_one]; ring
  linarith

private lemma nml_exp_neg {y : ℝ} : nml (Real.exp (-y)) = y * Real.exp (-y) := by
  unfold nml
  rw [Real.log_exp]
  ring

private lemma x_mul_exp_neg_le {x : ℝ} (_hx : 0 ≤ x) :
    x * Real.exp (-x) ≤ 2 * Real.exp (-(x / 2)) := by
  have h1 : x / 2 + 1 ≤ Real.exp (x / 2) := by
    have := Real.add_one_le_exp (x / 2); linarith
  have h2 : x ≤ 2 * Real.exp (x / 2) := by linarith
  have h3 : x * Real.exp (-x) ≤ (2 * Real.exp (x / 2)) * Real.exp (-x) :=
    mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
  have h4 : 2 * Real.exp (x / 2) * Real.exp (-x) = 2 * Real.exp (-(x / 2)) := by
    rw [mul_assoc, ← Real.exp_add]; congr 2; ring
  linarith

private lemma cosh_le_exp_sq_div_two (t : ℝ) : Real.cosh t ≤ Real.exp (t ^ 2 / 2) := by
  have hsym : ∀ s : ℝ, 0 ≤ s → Real.cosh s ≤ Real.exp (s ^ 2 / 2) := by
    intro s hs
    -- Show f(x) = exp(x^2/2) - cosh x is increasing on [0, ∞): f'(x) = x*exp(x^2/2) - sinh x ≥ 0.
    -- In turn g(x) = x*exp(x^2/2) - sinh x has g(0) = 0 and g'(x) = (1 + x^2)*exp(x^2/2) - cosh x ≥ 0!
    -- Even cleaner: prove directly via power series or via exp(-t^2/2) * cosh t ≤ 1!
    -- Let h(x) = exp(-x^2/2) * cosh x. h'(x) = exp(-x^2/2) * (sinh x - x * cosh x) ≤ 0 for x ≥ 0!
    -- And k(x) = x * cosh x - sinh x has k(0) = 0 and k'(x) = x * sinh x ≥ 0 for x ≥ 0!
    have hk : ∀ x : ℝ, 0 ≤ x → Real.sinh x ≤ x * Real.cosh x := by
      intro x hx
      have hmono : MonotoneOn (fun u : ℝ => u * Real.cosh u - Real.sinh u) (Set.Icc 0 x) := by
        apply monotoneOn_of_deriv_nonneg (convex_Icc 0 x)
        · exact ((continuous_id.mul Real.continuous_cosh).sub Real.continuous_sinh).continuousOn
        · intro u _
          exact (((hasDerivAt_id' u).mul (Real.hasDerivAt_cosh u)).sub
            (Real.hasDerivAt_sinh u)).differentiableAt.differentiableWithinAt
        · intro u hu
          rw [interior_Icc] at hu
          have hd : HasDerivAt (fun v : ℝ => v * Real.cosh v - Real.sinh v) (u * Real.sinh u) u := by
            have h1 := ((hasDerivAt_id' u).mul (Real.hasDerivAt_cosh u)).sub (Real.hasDerivAt_sinh u)
            have heq : 1 * Real.cosh u + u * Real.sinh u - Real.cosh u = u * Real.sinh u := by ring
            exact heq ▸ h1
          rw [hd.deriv]
          have hsinh_nn : 0 ≤ Real.sinh u := by
            rw [Real.sinh_eq]
            have hle : Real.exp (-u) ≤ Real.exp u := Real.exp_le_exp.mpr (by linarith [hu.1])
            linarith
          exact mul_nonneg hu.1.le hsinh_nn
      have h0 := hmono ⟨le_rfl, hx⟩ ⟨hx, le_rfl⟩ hx
      simp at h0
      linarith
    have hanti : AntitoneOn (fun u : ℝ => Real.exp (-(u ^ 2 / 2)) * Real.cosh u) (Set.Icc 0 s) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc 0 s)
      · exact ((Real.continuous_exp.comp (((continuous_pow 2).div_const 2).neg)).mul
          Real.continuous_cosh).continuousOn
      · intro u _
        have hd1 : HasDerivAt (fun v : ℝ => -(v ^ 2 / 2)) (-u) u := by
          have h1 := (((hasDerivAt_pow 2 u).div_const 2).neg)
          have heq : -(((2 : ℕ) : ℝ) * u ^ (2 - 1) / 2) = -u := by push_cast; ring
          exact heq ▸ h1
        exact ((hd1.exp).mul (Real.hasDerivAt_cosh u)).differentiableAt.differentiableWithinAt
      · intro u hu
        rw [interior_Icc] at hu
        have hd1 : HasDerivAt (fun v : ℝ => -(v ^ 2 / 2)) (-u) u := by
          have h1 := (((hasDerivAt_pow 2 u).div_const 2).neg)
          have heq : -(((2 : ℕ) : ℝ) * u ^ (2 - 1) / 2) = -u := by push_cast; ring
          exact heq ▸ h1
        have hd : HasDerivAt (fun v : ℝ => Real.exp (-(v ^ 2 / 2)) * Real.cosh v)
            (Real.exp (-(u ^ 2 / 2)) * -u * Real.cosh u + Real.exp (-(u ^ 2 / 2)) * Real.sinh u) u :=
          (hd1.exp).mul (Real.hasDerivAt_cosh u)
        rw [hd.deriv]
        have hku := hk u hu.1.le
        have hexp_pos := Real.exp_pos (-(u ^ 2 / 2))
        nlinarith
    have h0 := hanti ⟨le_rfl, hs⟩ ⟨hs, le_rfl⟩ hs
    simp only [zero_pow (by norm_num : 2 ≠ 0), zero_div, neg_zero, Real.exp_zero,
      Real.cosh_zero, mul_one] at h0
    have hmul := mul_le_mul_of_nonneg_left h0 (Real.exp_pos (s ^ 2 / 2)).le
    rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul, mul_one] at hmul
    exact hmul
  rcases le_total 0 t with ht | ht
  · exact hsym t ht
  · have := hsym (-t) (by linarith)
    simpa [Real.cosh_neg] using this

/-- Natural-log binary entropy `h(p) = -p log p - (1-p) log(1-p)`. -/
private noncomputable def binEnt (p : ℝ) : ℝ := nml p + nml (1 - p)

/-- Pinsker-type exact quadratic lower bound: `log 2 - h(p) ≥ 2 (1/2 - p)^2` for `p ∈ (0, 1/2]`. -/
private lemma log_two_sub_binEnt_ge {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1 / 2) :
    2 * (1 / 2 - p) ^ 2 ≤ Real.log 2 - binEnt p := by
  let F : ℝ → ℝ := fun x => Real.log 2 - binEnt x - 2 * (1 / 2 - x) ^ 2
  suffices hF : 0 ≤ F p by dsimp only [F] at hF; linarith
  have hF_half : F (1 / 2) = 0 := by
    dsimp only [F, binEnt, nml]
    have h1 : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
    rw [h1, one_div, Real.log_inv]
    ring
  have hF'_nonpos : ∀ x ∈ Set.Ioo p (1 / 2),
      Real.log (x / (1 - x)) + 4 * (1 / 2 - x) ≤ 0 := by
    intro x hx
    have hx0 : 0 < x := lt_trans hp0 hx.1
    have hx1 : x < 1 / 2 := hx.2
    have h1x : 0 < 1 - x := by linarith
    -- Show G(u) = log(u/(1-u)) + 4*(1/2 - u) is monotone increasing on [x, 1/2] with G(1/2) = 0!
    have hG_deriv : ∀ u ∈ Set.Ioo x (1 / 2),
        HasDerivAt (fun v : ℝ => Real.log v - Real.log (1 - v) + 4 * (1 / 2 - v))
          (u⁻¹ - -(1 - u)⁻¹ + -4) u := by
      intro u hu
      have hu0 : 0 < u := lt_of_lt_of_le hx0 hu.1.le
      have hu1 : 0 < 1 - u := by linarith [hu.2]
      have hd1 := Real.hasDerivAt_log hu0.ne'
      have hd2 : HasDerivAt (fun v : ℝ => Real.log (1 - v)) (-(1 - u)⁻¹) u := by
        have hsub : HasDerivAt (fun v : ℝ => 1 - v) (-1) u := by
          simpa using (hasDerivAt_id u).const_sub (1 : ℝ)
        have h1 := (Real.hasDerivAt_log hu1.ne').comp u hsub
        have heq : (1 - u)⁻¹ * -1 = -(1 - u)⁻¹ := by ring
        exact heq ▸ h1
      have hd3 : HasDerivAt (fun v : ℝ => 4 * (1 / 2 - v)) (-4) u := by
        have hsub : HasDerivAt (fun v : ℝ => 1 / 2 - v) (-1) u := by
          simpa using (hasDerivAt_id u).const_sub (1 / 2 : ℝ)
        have h1 := hsub.const_mul (4 : ℝ)
        have heq : (4 : ℝ) * -1 = -4 := by norm_num
        exact heq ▸ h1
      exact (hd1.sub hd2).add hd3
    have hG_mono : MonotoneOn (fun u : ℝ => Real.log u - Real.log (1 - u) + 4 * (1 / 2 - u))
        (Set.Icc x (1 / 2)) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc x (1 / 2))
      · intro u hu
        have hu0 : 0 < u := lt_of_lt_of_le hx0 hu.1
        have hu1 : 0 < 1 - u := by linarith [hu.2]
        exact (((Real.continuousAt_log hu0.ne').sub
          ((Real.continuousAt_log hu1.ne').comp (continuousAt_const.sub continuousAt_id))).add
          (continuousAt_const.mul (continuousAt_const.sub continuousAt_id))).continuousWithinAt
      · intro u hu
        rw [interior_Icc] at hu
        exact (hG_deriv u hu).differentiableAt.differentiableWithinAt
      · intro u hu
        rw [interior_Icc] at hu
        have hu0 : 0 < u := lt_of_lt_of_le hx0 hu.1.le
        have hu1 : 0 < 1 - u := by linarith [hu.2]
        rw [(hG_deriv u hu).deriv]
        have heq : u⁻¹ - -(1 - u)⁻¹ + -4 = (1 - 2 * u) ^ 2 / (u * (1 - u)) := by
          field_simp [hu0.ne', hu1.ne']; ring
        rw [heq]
        exact div_nonneg (sq_nonneg _) (mul_pos hu0 hu1).le
    have hle := hG_mono ⟨le_rfl, hx1.le⟩ ⟨hx1.le, le_rfl⟩ hx1.le
    rw [Real.log_div hx0.ne' h1x.ne']
    have hhalf : Real.log (1 / 2 : ℝ) - Real.log (1 - 1 / 2) + 4 * (1 / 2 - 1 / 2) = 0 := by
      have : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
      rw [this]; ring
    linarith
  have hdF_at : ∀ x ∈ Set.Ioo p (1 / 2),
      HasDerivAt F (Real.log (x / (1 - x)) + 4 * (1 / 2 - x)) x := by
    intro x hx
    have hx0 : 0 < x := lt_trans hp0 hx.1
    have h1x : 0 < 1 - x := by linarith [hx.2]
    have hd1 : HasDerivAt (fun t : ℝ => -(t * Real.log t)) (-(Real.log x + 1)) x := by
      have h := ((hasDerivAt_id' x).mul (Real.hasDerivAt_log hx0.ne')).neg
      have heq : -(1 * Real.log x + x * x⁻¹) = -(Real.log x + 1) := by
        rw [one_mul, mul_inv_cancel₀ hx0.ne']
      exact heq ▸ h
    have hd2 : HasDerivAt (fun t : ℝ => -((1 - t) * Real.log (1 - t))) (Real.log (1 - x) + 1) x := by
      have hsub : HasDerivAt (fun t : ℝ => 1 - t) (-1) x := by
        simpa using (hasDerivAt_id x).const_sub (1 : ℝ)
      have hlog : HasDerivAt (fun t : ℝ => Real.log (1 - t)) (-(1 - x)⁻¹) x := by
        have h1 := (Real.hasDerivAt_log h1x.ne').comp x hsub
        have heq : (1 - x)⁻¹ * -1 = -(1 - x)⁻¹ := by ring
        exact heq ▸ h1
      have hmul := (hsub.mul hlog).neg
      have heq : -(-1 * Real.log (1 - x) + (1 - x) * -(1 - x)⁻¹) = Real.log (1 - x) + 1 := by
        rw [neg_one_mul, mul_neg, mul_inv_cancel₀ h1x.ne']; ring
      exact heq ▸ hmul
    have hd3 : HasDerivAt (fun t : ℝ => 2 * (1 / 2 - t) ^ 2) (-4 * (1 / 2 - x)) x := by
      have hsub : HasDerivAt (fun t : ℝ => 1 / 2 - t) (-1) x := by
        simpa using (hasDerivAt_id x).const_sub (1 / 2 : ℝ)
      have hsq := (hsub.pow 2).const_mul (2 : ℝ)
      have heq : 2 * (((2 : ℕ) : ℝ) * (1 / 2 - x) ^ (2 - 1) * -1) = -4 * (1 / 2 - x) := by
        push_cast; ring
      exact heq ▸ hsq
    have h := ((hasDerivAt_const x (Real.log 2)).sub (hd1.add hd2)).sub hd3
    have heq : 0 - (-(Real.log x + 1) + (Real.log (1 - x) + 1)) - -4 * (1 / 2 - x) =
        Real.log (x / (1 - x)) + 4 * (1 / 2 - x) := by
      rw [Real.log_div hx0.ne' h1x.ne']; ring
    exact heq ▸ h
  have hF_anti : AntitoneOn F (Set.Icc p (1 / 2)) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc p (1 / 2))
    · intro x _
      dsimp only [F, binEnt, nml]
      have hc1 : Continuous (fun t : ℝ => -(t * Real.log t)) := Real.continuous_mul_log.neg
      have hc2 : Continuous (fun t : ℝ => -((1 - t) * Real.log (1 - t))) :=
        (Real.continuous_mul_log.comp (continuous_const.sub continuous_id)).neg
      have hc3 : Continuous (fun t : ℝ => 2 * (1 / 2 - t) ^ 2) :=
        continuous_const.mul ((continuous_const.sub continuous_id).pow 2)
      exact ((continuous_const.sub (hc1.add hc2)).sub hc3).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      exact (hdF_at x hx).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [(hdF_at x hx).deriv]
      exact hF'_nonpos x hx
  have hge := hF_anti ⟨le_rfl, hp1⟩ ⟨hp1, le_rfl⟩ hp1
  linarith

/-- Binomial Chernoff tail bound: for `0 < p ≤ 1/2` and `t ≤ p * m`,
`∑_{k ≤ t} C(m, k) ≤ exp(m * binEnt p)`. -/
private lemma sum_choose_le_exp_binEnt {m t : ℕ} {p : ℝ}
    (hp0 : 0 < p) (hp1 : p ≤ 1 / 2) (ht : (t : ℝ) ≤ p * m) :
    ((∑ k ∈ Finset.range (t + 1), m.choose k : ℕ) : ℝ) ≤ Real.exp (m * binEnt p) := by
  have h1p : 0 < 1 - p := by linarith
  have hratio : p / (1 - p) ≤ 1 := (div_le_one h1p).mpr (by linarith)
  have hterm : ∀ k ∈ Finset.range (t + 1),
      (m.choose k : ℝ) * Real.exp (-(m * binEnt p)) ≤
        (m.choose k : ℝ) * p ^ k * (1 - p) ^ (m - k) := by
    intro k hk
    have hkt : (k : ℝ) ≤ p * m := by
      have hk_le : k ≤ t := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      exact (Nat.cast_le.mpr hk_le).trans ht
    have hkm : k ≤ m := by
      have : (k : ℝ) ≤ m := hkt.trans (by nlinarith)
      exact_mod_cast this
    have hexp_eq : Real.exp (-(m * binEnt p)) = p ^ (p * (m : ℝ)) * (1 - p) ^ ((1 - p) * (m : ℝ)) := by
      rw [binEnt, nml, nml, Real.rpow_def_of_pos hp0, Real.rpow_def_of_pos h1p, ← Real.exp_add]
      congr 1; ring
    rw [hexp_eq, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    -- Show p^(pm) * (1-p)^((1-p)m) ≤ p^k * (1-p)^(m-k), i.e., (p/(1-p))^(pm - k) ≤ 1!
    have hpow_k : p ^ k = p ^ (k : ℝ) := (Real.rpow_natCast p k).symm
    have hpow_mk : (1 - p) ^ (m - k) = (1 - p) ^ ((m : ℝ) - k) := by
      rw [← Real.rpow_natCast, Nat.cast_sub hkm]
    rw [hpow_k, hpow_mk]
    have hdiv : p ^ (p * (m : ℝ)) * (1 - p) ^ ((1 - p) * (m : ℝ)) /
        (p ^ (k : ℝ) * (1 - p) ^ ((m : ℝ) - k)) = (p / (1 - p)) ^ (p * (m : ℝ) - k) := by
      rw [Real.div_rpow hp0.le h1p.le, mul_div_mul_comm, ← Real.rpow_sub hp0, ← Real.rpow_sub h1p]
      rw [show (1 - p) * (m : ℝ) - ((m : ℝ) - k) = -(p * (m : ℝ) - k) by ring]
      rw [Real.rpow_neg h1p.le, div_eq_mul_inv]
    have hdenom : 0 < p ^ (k : ℝ) * (1 - p) ^ ((m : ℝ) - k) :=
      mul_pos (Real.rpow_pos_of_pos hp0 _) (Real.rpow_pos_of_pos h1p _)
    rw [← div_le_one hdenom, hdiv]
    exact Real.rpow_le_one (div_nonneg hp0.le h1p.le) hratio (by linarith)
  have hsum_le : ((∑ k ∈ Finset.range (t + 1), m.choose k : ℕ) : ℝ) * Real.exp (-(m * binEnt p)) ≤ 1 := by
    rw [Nat.cast_sum, Finset.sum_mul]
    calc ∑ k ∈ Finset.range (t + 1), (m.choose k : ℝ) * Real.exp (-(m * binEnt p))
        ≤ ∑ k ∈ Finset.range (t + 1), (m.choose k : ℝ) * p ^ k * (1 - p) ^ (m - k) :=
          Finset.sum_le_sum hterm
      _ ≤ ∑ k ∈ Finset.range (m + 1), (m.choose k : ℝ) * p ^ k * (1 - p) ^ (m - k) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
          have htm : t ≤ m := by
            have : (t : ℝ) ≤ m := ht.trans (by nlinarith)
            exact_mod_cast this
          exact Finset.range_mono (Nat.succ_le_succ htm)
      _ = (p + (1 - p)) ^ m := by
          rw [add_pow]
          refine Finset.sum_congr rfl fun k _ => by ring
      _ = 1 := by ring_nf
  have hmul := mul_le_mul_of_nonneg_right hsum_le (Real.exp_pos (m * binEnt p)).le
  rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one, one_mul] at hmul
  exact hmul

/- ## Section 2: Finite Shannon entropy on the uniform hypercube `Fin m → Bool` -/

private noncomputable def uprob {m : ℕ} {α : Type*} (f : (Fin m → Bool) → α) (a : α) : ℝ :=
  ((Finset.univ.filter fun x : Fin m → Bool => f x = a).card : ℝ) / (2 ^ m : ℝ)

private lemma uprob_nonneg {m : ℕ} {α : Type*} (f : (Fin m → Bool) → α) (a : α) :
    0 ≤ uprob f a := by
  unfold uprob; positivity

private lemma uprob_sum_eq_one {m : ℕ} {α : Type*} [Fintype α] (f : (Fin m → Bool) → α) :
    ∑ a : α, uprob f a = 1 := by
  unfold uprob
  rw [← Finset.sum_div]
  have hcard : (∑ a : α, (Finset.univ.filter fun x : Fin m → Bool => f x = a).card) = 2 ^ m := by
    rw [← Finset.card_eq_sum_card_fiberwise (f := f) (fun _ _ => Finset.mem_univ _)]
    simp [Fintype.card_bool]
  have hpos : (0 : ℝ) < 2 ^ m := by positivity
  rw [← Nat.cast_sum, hcard, Nat.cast_pow, Nat.cast_ofNat, div_self hpos.ne']

private lemma uprob_le_one {m : ℕ} {α : Type*} [Fintype α] (f : (Fin m → Bool) → α) (a : α) :
    uprob f a ≤ 1 := by
  rw [← uprob_sum_eq_one f]
  exact Finset.single_le_sum (fun b _ => uprob_nonneg f b) (Finset.mem_univ a)

private lemma uprob_le_card_div {m : ℕ} {α : Type*} (f : (Fin m → Bool) → α) (a : α)
    (S : Finset (Fin m → Bool)) (himp : ∀ x, f x = a → x ∈ S) :
    uprob f a ≤ (S.card : ℝ) / (2 ^ m : ℝ) := by
  unfold uprob
  refine div_le_div_of_nonneg_right (Nat.cast_le.mpr (Finset.card_le_card fun x hx => ?_)) (by positivity)
  exact himp x (Finset.mem_filter.mp hx).2

private lemma one_sub_uprob_le_card_div {m : ℕ} {α : Type*} (f : (Fin m → Bool) → α) (a : α)
    (S : Finset (Fin m → Bool)) (himp : ∀ x, f x ≠ a → x ∈ S) :
    1 - uprob f a ≤ (S.card : ℝ) / (2 ^ m : ℝ) := by
  unfold uprob
  have h2pos : (0 : ℝ) < 2 ^ m := by positivity
  rw [sub_le_iff_le_add, ← add_div, one_le_div h2pos, ← Nat.cast_add]
  norm_cast
  have huniv : (Finset.univ : Finset (Fin m → Bool)).card = 2 ^ m := by simp [Fintype.card_bool]
  rw [← huniv]
  calc (Finset.univ : Finset (Fin m → Bool)).card
      ≤ (S ∪ Finset.univ.filter fun x => f x = a).card := by
        refine Finset.card_le_card fun x _ => ?_
        rw [Finset.mem_union]
        by_cases h : f x = a
        · right; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
        · left; exact himp x h
    _ ≤ S.card + (Finset.univ.filter fun x => f x = a).card :=
        Finset.card_union_le _ _

private noncomputable def uH {m : ℕ} {α : Type*} [Fintype α] (f : (Fin m → Bool) → α) : ℝ :=
  ∑ a : α, nml (uprob f a)

private lemma exists_fiber_large {m : ℕ} {α : Type*} [Fintype α] (f : (Fin m → Bool) → α) :
    ∃ a : α, (2 : ℝ) ^ m * Real.exp (-uH f) ≤
      ((Finset.univ.filter fun x : Fin m → Bool => f x = a).card : ℝ) := by
  have hne : (Finset.univ : Finset α).Nonempty := ⟨f (fun _ => false), Finset.mem_univ _⟩
  obtain ⟨a₀, _, ha₀_max⟩ := Finset.exists_max_image Finset.univ (uprob f) hne
  have ha₀_pos : 0 < uprob f a₀ := by
    by_contra hle
    have h0 : uprob f a₀ = 0 := le_antisymm (not_lt.mp hle) (uprob_nonneg f a₀)
    have hall : ∑ a : α, uprob f a = 0 := Finset.sum_eq_zero fun a _ =>
      le_antisymm ((ha₀_max a (Finset.mem_univ a)).trans_eq h0) (uprob_nonneg f a)
    linarith [uprob_sum_eq_one f]
  have hH_ge : -Real.log (uprob f a₀) ≤ uH f := by
    have hterm : ∀ a : α, uprob f a * (-Real.log (uprob f a₀)) ≤ nml (uprob f a) := by
      intro a
      rcases eq_or_lt_of_le (uprob_nonneg f a) with ha0 | ha_pos
      · rw [← ha0, zero_mul, nml_zero]
      · unfold nml
        have hlog : Real.log (uprob f a) ≤ Real.log (uprob f a₀) :=
          Real.log_le_log ha_pos (ha₀_max a (Finset.mem_univ a))
        nlinarith
    calc -Real.log (uprob f a₀)
        = (∑ a : α, uprob f a) * (-Real.log (uprob f a₀)) := by rw [uprob_sum_eq_one, one_mul]
      _ = ∑ a : α, uprob f a * (-Real.log (uprob f a₀)) := Finset.sum_mul _ _ _
      _ ≤ ∑ a : α, nml (uprob f a) := Finset.sum_le_sum fun a _ => hterm a
  have hexp : Real.exp (-uH f) ≤ uprob f a₀ := by
    rw [← Real.exp_log ha₀_pos]
    exact Real.exp_le_exp.mpr (by linarith)
  refine ⟨a₀, ?_⟩
  unfold uprob at hexp
  have hpos : (0 : ℝ) < 2 ^ m := by positivity
  exact (le_div_iff₀ hpos).mp hexp |> fun h => by linarith

private lemma uH_le_log_card {m : ℕ} {α : Type*} [Fintype α] (f : (Fin m → Bool) → α) :
    uH f ≤ Real.log (Fintype.card α : ℝ) := by
  have hcard_pos : (0 : ℝ) < Fintype.card α := by
    have : Nonempty α := ⟨f (fun _ => false)⟩
    exact_mod_cast Fintype.card_pos
  have hterm : ∀ a : α,
      nml (uprob f a) - uprob f a * Real.log (Fintype.card α : ℝ) ≤
        (Fintype.card α : ℝ)⁻¹ - uprob f a := by
    intro a
    rcases eq_or_lt_of_le (uprob_nonneg f a) with ha0 | ha_pos
    · rw [← ha0, nml_zero, zero_mul, sub_zero, sub_zero]; positivity
    · unfold nml
      have hlog := Real.log_le_sub_one_of_pos (div_pos (inv_pos.mpr hcard_pos) ha_pos)
      rw [Real.log_div (inv_pos.mpr hcard_pos).ne' ha_pos.ne', Real.log_inv] at hlog
      have hmul := mul_le_mul_of_nonneg_left hlog ha_pos.le
      have heq : uprob f a * ((Fintype.card α : ℝ)⁻¹ / uprob f a - 1) =
          (Fintype.card α : ℝ)⁻¹ - uprob f a := by
        field_simp [ha_pos.ne']
      linarith
  have hsum := Finset.sum_le_sum fun a (_ : a ∈ Finset.univ) => hterm a
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
    uprob_sum_eq_one, one_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_inv_cancel₀ hcard_pos.ne'] at hsum
  unfold uH
  linarith

private lemma uH_prod_le {m : ℕ} {α β : Type*} [Fintype α] [Fintype β]
    (f : (Fin m → Bool) → α) (g : (Fin m → Bool) → β) :
    uH (fun x => (f x, g x)) ≤ uH f + uH g := by
  have hmarg1 : ∀ a : α, ∑ b : β, uprob (fun x => (f x, g x)) (a, b) = uprob f a := by
    intro a; unfold uprob; rw [← Finset.sum_div]
    congr 1; rw [← Nat.cast_sum]
    congr 1
    have hfib := Finset.card_eq_sum_card_fiberwise (s := Finset.univ.filter fun x => f x = a)
      (t := Finset.univ) (f := g) (fun _ _ => Finset.mem_univ _)
    rw [hfib]
    refine Finset.sum_congr rfl fun b _ => ?_
    congr 1; ext x; simp [Finset.mem_filter, Prod.mk.injEq]
  have hmarg2 : ∀ b : β, ∑ a : α, uprob (fun x => (f x, g x)) (a, b) = uprob g b := by
    intro b; unfold uprob; rw [← Finset.sum_div]
    congr 1; rw [← Nat.cast_sum]
    congr 1
    have hfib := Finset.card_eq_sum_card_fiberwise (s := Finset.univ.filter fun x => g x = b)
      (t := Finset.univ) (f := f) (fun _ _ => Finset.mem_univ _)
    rw [hfib]
    refine Finset.sum_congr rfl fun a _ => ?_
    congr 1; ext x; simp [Finset.mem_filter, Prod.mk.injEq, and_comm]
  have hterm : ∀ p : α × β,
      (if 0 < uprob (fun x => (f x, g x)) p then
        uprob (fun x => (f x, g x)) p *
          (Real.log (uprob f p.1) + Real.log (uprob g p.2) - Real.log (uprob (fun x => (f x, g x)) p))
      else 0) ≤ uprob f p.1 * uprob g p.2 - uprob (fun x => (f x, g x)) p := by
    rintro ⟨a, b⟩
    split_ifs with hp
    · have ha : 0 < uprob f a := by
        rw [← hmarg1 a]
        exact lt_of_lt_of_le hp (Finset.single_le_sum (fun b' _ => uprob_nonneg _ (a, b')) (Finset.mem_univ b))
      have hb : 0 < uprob g b := by
        rw [← hmarg2 b]
        exact lt_of_lt_of_le hp (Finset.single_le_sum (fun a' _ => uprob_nonneg _ (a', b)) (Finset.mem_univ a))
      have hlog := Real.log_le_sub_one_of_pos (div_pos (mul_pos ha hb) hp)
      rw [Real.log_div (mul_pos ha hb).ne' hp.ne', Real.log_mul ha.ne' hb.ne'] at hlog
      have hmul := mul_le_mul_of_nonneg_left hlog hp.le
      have heq : uprob (fun x => (f x, g x)) (a, b) *
          (uprob f a * uprob g b / uprob (fun x => (f x, g x)) (a, b) - 1) =
          uprob f a * uprob g b - uprob (fun x => (f x, g x)) (a, b) := by
        field_simp [hp.ne']
      linarith
    · have hp0 : uprob (fun x => (f x, g x)) (a, b) = 0 :=
        le_antisymm (not_lt.mp hp) (uprob_nonneg _ (a, b))
      rw [hp0, sub_zero]
      exact mul_nonneg (uprob_nonneg f a) (uprob_nonneg g b)
  have hsum := Finset.sum_le_sum fun p (_ : p ∈ Finset.univ) => hterm p
  have hrhs : (∑ p : α × β, (uprob f p.1 * uprob g p.2 - uprob (fun x => (f x, g x)) p)) = 0 := by
    rw [Finset.sum_sub_distrib, Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, uprob_sum_eq_one, mul_one, uprob_sum_eq_one]
    exact sub_self 1
  have hlhs : (∑ p : α × β,
      if 0 < uprob (fun x => (f x, g x)) p then
        uprob (fun x => (f x, g x)) p *
          (Real.log (uprob f p.1) + Real.log (uprob g p.2) - Real.log (uprob (fun x => (f x, g x)) p))
      else 0) = uH (fun x => (f x, g x)) - uH f - uH g := by
    have hsplit : ∀ p : α × β,
        (if 0 < uprob (fun x => (f x, g x)) p then
          uprob (fun x => (f x, g x)) p *
            (Real.log (uprob f p.1) + Real.log (uprob g p.2) - Real.log (uprob (fun x => (f x, g x)) p))
        else 0) =
        nml (uprob (fun x => (f x, g x)) p) +
        uprob (fun x => (f x, g x)) p * Real.log (uprob f p.1) +
        uprob (fun x => (f x, g x)) p * Real.log (uprob g p.2) := by
      intro p
      split_ifs with hp
      · unfold nml; ring
      · have hp0 : uprob (fun x => (f x, g x)) p = 0 :=
          le_antisymm (not_lt.mp hp) (uprob_nonneg _ p)
        simp [hp0, nml_zero]
    simp_rw [hsplit, Finset.sum_add_distrib]
    have h1 : (∑ p : α × β, uprob (fun x => (f x, g x)) p * Real.log (uprob f p.1)) = -uH f := by
      rw [Fintype.sum_prod_type]
      simp_rw [← Finset.sum_mul, hmarg1]
      unfold uH nml; rw [← Finset.sum_neg_distrib]; simp only [neg_neg]
    have h2 : (∑ p : α × β, uprob (fun x => (f x, g x)) p * Real.log (uprob g p.2)) = -uH g := by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      simp_rw [← Finset.sum_mul, hmarg2]
      unfold uH nml; rw [← Finset.sum_neg_distrib]; simp only [neg_neg]
    rw [h1, h2]; unfold uH; ring
  linarith

private lemma uH_comp_equiv {m : ℕ} {α β : Type*} [Fintype α] [Fintype β]
    (f : (Fin m → Bool) → α) (e : α ≃ β) :
    uH (fun x => e (f x)) = uH f := by
  unfold uH
  refine Fintype.sum_equiv e.symm _ _ fun b => ?_
  congr 1; unfold uprob; congr 1
  exact_mod_cast congrArg Finset.card (by ext x; simp [Equiv.eq_symm_apply])

private lemma uH_fin_le {m : ℕ} {α : Type*} [Fintype α] :
    ∀ (k : ℕ) (f : Fin k → (Fin m → Bool) → α),
      uH (fun x (i : Fin k) => f i x) ≤ ∑ i : Fin k, uH (f i)
  | 0, f => by
    simp only [Finset.univ_eq_empty, Finset.sum_empty]
    have hle := uH_le_log_card (fun x (i : Fin 0) => f i x)
    simp at hle
    exact hle
  | k + 1, f => by
    let e : (Fin (k + 1) → α) ≃ (α × (Fin k → α)) :=
      ⟨fun v => (v 0, fun i => v i.succ),
       fun p => Fin.cons p.1 p.2,
       fun v => by funext j; refine Fin.cases rfl (fun _ => rfl) j,
       fun ⟨a, w⟩ => Prod.ext rfl (by funext i; rfl)⟩
    have h1 : uH (fun x (i : Fin (k + 1)) => f i x) =
        uH (fun x => (f 0 x, fun i : Fin k => f i.succ x)) :=
      (uH_comp_equiv (fun x (i : Fin (k + 1)) => f i x) e).symm
    rw [h1, Fin.sum_univ_succ]
    exact (uH_prod_le (f 0) (fun x (i : Fin k) => f i.succ x)).trans
      (add_le_add le_rfl (uH_fin_le k (fun i => f i.succ)))

/- ## Section 3: Hoeffding's inequality on `Fin m → Bool` & paired small-`n` case -/

private def sign (b : Bool) : ℝ := if b then 1 else -1

private lemma exp_sum_rademacher {m : ℕ} (w : Fin m → ℝ) (t : ℝ) :
    (∑ x : Fin m → Bool, Real.exp (t * ∑ j : Fin m, w j * sign (x j))) / (2 ^ m : ℝ) =
      ∏ j : Fin m, Real.cosh (t * w j) := by
  have hprod : ∀ x : Fin m → Bool,
      Real.exp (t * ∑ j : Fin m, w j * sign (x j)) =
        ∏ j : Fin m, Real.exp (t * w j * sign (x j)) := by
    intro x
    rw [Finset.mul_sum, Real.exp_sum]
    refine Finset.prod_congr rfl fun j _ => by ring_nf
  simp_rw [hprod]
  have hsum_prod : (∑ x : Fin m → Bool, ∏ j : Fin m, Real.exp (t * w j * sign (x j))) =
      ∏ j : Fin m, ∑ b : Bool, Real.exp (t * w j * sign b) := by
    simpa using (Fintype.prod_sum (fun (j : Fin m) (b : Bool) => Real.exp (t * w j * sign b))).symm
  rw [hsum_prod]
  have h2m : (2 ^ m : ℝ) = ∏ _j : Fin m, (2 : ℝ) := by simp
  rw [h2m, ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Fintype.sum_bool, Real.cosh_eq]
  simp only [sign, ↓reduceIte, Bool.false_eq_true, mul_one, mul_neg]

private lemma hoeffding_one_sided {m : ℕ} (w : Fin m → ℝ) (hw : ∀ j, w j = 1 ∨ w j = -1 ∨ w j = 0)
    (K : ℕ) (hK : ((Finset.univ.filter fun j => w j ≠ 0).card : ℝ) ≤ K)
    {d : ℝ} (hd : 0 ≤ d) (hKpos : 0 < (K : ℝ)) :
    ((Finset.univ.filter fun x : Fin m → Bool => d ≤ ∑ j : Fin m, w j * sign (x j)).card : ℝ) /
      (2 ^ m : ℝ) ≤ Real.exp (-(d ^ 2 / (2 * K))) := by
  let t : ℝ := d / K
  have ht : 0 ≤ t := div_nonneg hd hKpos.le
  have hmgf : (∑ x : Fin m → Bool, Real.exp (t * ∑ j : Fin m, w j * sign (x j))) / (2 ^ m : ℝ) ≤
      Real.exp (t ^ 2 * K / 2) := by
    rw [exp_sum_rademacher]
    have hle : ∀ j : Fin m, Real.cosh (t * w j) ≤
        Real.exp (if w j ≠ 0 then t ^ 2 / 2 else 0) := by
      intro j
      rcases hw j with h1 | h1 | h1
      · rw [h1, if_pos one_ne_zero, mul_one]; exact cosh_le_exp_sq_div_two t
      · rw [h1, if_pos (by norm_num), mul_neg, mul_one, Real.cosh_neg]
        exact cosh_le_exp_sq_div_two t
      · rw [h1, if_neg (not_not.mpr rfl), mul_zero, Real.cosh_zero, Real.exp_zero]
    calc ∏ j : Fin m, Real.cosh (t * w j)
        ≤ ∏ j : Fin m, Real.exp (if w j ≠ 0 then t ^ 2 / 2 else 0) :=
          Finset.prod_le_prod (fun j _ => (Real.cosh_pos _).le) (fun j _ => hle j)
      _ = Real.exp (∑ j : Fin m, if w j ≠ 0 then t ^ 2 / 2 else 0) := (Real.exp_sum _ _).symm
      _ = Real.exp (((Finset.univ.filter fun j => w j ≠ 0).card : ℝ) * (t ^ 2 / 2)) := by
          rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
      _ ≤ Real.exp (t ^ 2 * K / 2) := by
          apply Real.exp_le_exp.mpr
          have hsq : 0 ≤ t ^ 2 / 2 := by positivity
          have := mul_le_mul_of_nonneg_right hK hsq
          linarith
  -- Markov's inequality on exp(t * sum)!
  have hmarkov :
      ((Finset.univ.filter fun x : Fin m → Bool => d ≤ ∑ j : Fin m, w j * sign (x j)).card : ℝ) *
        Real.exp (t * d) ≤
        ∑ x : Fin m → Bool, Real.exp (t * ∑ j : Fin m, w j * sign (x j)) := by
    calc ((Finset.univ.filter fun x : Fin m → Bool => d ≤ ∑ j : Fin m, w j * sign (x j)).card : ℝ) *
          Real.exp (t * d)
        = ∑ _x ∈ Finset.univ.filter (fun x : Fin m → Bool => d ≤ ∑ j : Fin m, w j * sign (x j)),
            Real.exp (t * d) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ x ∈ Finset.univ.filter (fun x : Fin m → Bool => d ≤ ∑ j : Fin m, w j * sign (x j)),
            Real.exp (t * ∑ j : Fin m, w j * sign (x j)) := by
          refine Finset.sum_le_sum fun x hx => Real.exp_le_exp.mpr ?_
          exact mul_le_mul_of_nonneg_left (Finset.mem_filter.mp hx).2 ht
      _ ≤ ∑ x : Fin m → Bool, Real.exp (t * ∑ j : Fin m, w j * sign (x j)) :=
          Finset.sum_le_univ_sum_of_nonneg fun x => (Real.exp_pos _).le
  have h2pos : (0 : ℝ) < 2 ^ m := by positivity
  have hstep : ((Finset.univ.filter fun x : Fin m → Bool => d ≤ ∑ j : Fin m, w j * sign (x j)).card : ℝ) /
      (2 ^ m : ℝ) * Real.exp (t * d) ≤ Real.exp (t ^ 2 * K / 2) := by
    rw [div_mul_eq_mul_div]
    exact (div_le_div_of_nonneg_right hmarkov h2pos.le).trans hmgf
  have hmul := mul_le_mul_of_nonneg_right hstep (Real.exp_pos (-(t * d))).le
  rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one, ← Real.exp_add] at hmul
  refine hmul.trans (Real.exp_le_exp.mpr ?_)
  dsimp only [t]
  have heq : (d / K) ^ 2 * K / 2 + -(d / K * d) = -(d ^ 2 / (2 * K)) := by
    field_simp [hKpos.ne']; ring
  linarith

private lemma hoeffding_lower_tail {m : ℕ} (w : Fin m → ℝ)
    (hw : ∀ j, w j = 1 ∨ w j = -1 ∨ w j = 0)
    (K : ℕ) (hK : ((Finset.univ.filter fun j => w j ≠ 0).card : ℝ) ≤ K)
    {d : ℝ} (hd : 0 ≤ d) (hKpos : 0 < (K : ℝ)) :
    ((Finset.univ.filter fun x : Fin m → Bool => ∑ j : Fin m, w j * sign (x j) ≤ -d).card : ℝ) /
      (2 ^ m : ℝ) ≤ Real.exp (-(d ^ 2 / (2 * K))) := by
  have hneg : ∀ j, (-w j) = 1 ∨ (-w j) = -1 ∨ (-w j) = 0 := by
    intro j; rcases hw j with h | h | h
    · right; left; linarith
    · left; linarith
    · right; right; linarith
  have hK' : ((Finset.univ.filter fun j => -w j ≠ 0).card : ℝ) ≤ K := by
    convert hK using 3; ext j; simp
  have h := hoeffding_one_sided (fun j => -w j) hneg K hK' hd hKpos
  convert h using 3
  congr 1; ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, neg_mul, Finset.sum_neg_distrib]
  constructor <;> intro h1 <;> linarith

/-- Case `n ≤ 36`: constant `+1` coloring gives `|∑_{j ∈ S i} 1| ≤ n ≤ 6 √n`. -/
private lemma spencer_le_36 {n : ℕ} (hn : n ≤ 36) (S : Fin n → Finset (Fin n)) :
    ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 6 * Real.sqrt n := by
  refine ⟨fun _ => 1, fun _ => Or.inl rfl, fun i => ?_⟩
  rw [Finset.sum_const, nsmul_eq_mul, mul_one, abs_of_nonneg (Nat.cast_nonneg _)]
  have hcard : ((S i).card : ℝ) ≤ n := by
    have : (S i).card ≤ n := (Finset.card_le_univ (S i)).trans (by simp)
    exact_mod_cast this
  have hle : (n : ℝ) ≤ 6 * Real.sqrt n := by
    have hsq : (n : ℝ) ^ 2 ≤ (6 * Real.sqrt n) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
      have hnR : (n : ℝ) ≤ 36 := by exact_mod_cast hn
      nlinarith
    have hpos : 0 ≤ 6 * Real.sqrt n := by positivity
    nlinarith [sq_nonneg ((n : ℝ) - 6 * Real.sqrt n)]
  exact hcard.trans hle

/-- Case `37 ≤ n ≤ 10^14`: paired Rademacher signs `(2k, 2k+1)` + Hoeffding union bound. -/
private lemma spencer_mid {n : ℕ} (hn1 : 37 ≤ n) (hn2 : n ≤ 10 ^ 14)
    (S : Fin n → Finset (Fin n)) :
    ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 6 * Real.sqrt n := by
  let k : ℕ := n / 2
  have hk_pos : 0 < (k : ℝ) := by
    have : 0 < k := by omega
    exact_mod_cast this
  have h2k_le : (2 * k : ℝ) ≤ n := by
    have : 2 * k ≤ n := by omega
    exact_mod_cast this
  -- Build coloring from x : Fin k → Bool: pair (2r, 2r+1) gets (+sign(x r), -sign(x r)), leftover gets +1.
  let mkChi : (Fin k → Bool) → (Fin n → ℝ) := fun x j =>
    if h : j.val / 2 < k then
      if j.val % 2 = 0 then sign (x ⟨j.val / 2, h⟩) else -sign (x ⟨j.val / 2, h⟩)
    else 1
  have hmkChi_pm : ∀ x j, mkChi x j = 1 ∨ mkChi x j = -1 := by
    intro x j; dsimp only [mkChi]
    split_ifs with h1 h2
    · unfold sign; split_ifs <;> simp
    · unfold sign; split_ifs <;> simp
    · left; rfl
  -- For each i : Fin n, express ∑ j ∈ S i, mkChi x j = eps i + ∑ r : Fin k, w i r * sign (x r).
  let w : Fin n → Fin k → ℝ := fun i r =>
    (if (⟨2 * r.val, by omega⟩ : Fin n) ∈ S i then (1 : ℝ) else 0) -
    (if (⟨2 * r.val + 1, by omega⟩ : Fin n) ∈ S i then (1 : ℝ) else 0)
  let eps : Fin n → ℝ := fun i =>
    if h : 2 * k < n then if (⟨2 * k, h⟩ : Fin n) ∈ S i then 1 else 0 else 0
  have heps_abs : ∀ i, |eps i| ≤ 1 := by
    intro i; dsimp only [eps]; split_ifs <;> norm_num
  have hsum_eq : ∀ i x,
      (∑ j ∈ S i, mkChi x j) = eps i + ∑ r : Fin k, w i r * sign (x r) := by
    intro i x
    have hS_eq : (∑ j ∈ S i, mkChi x j) = ∑ j : Fin n, if j ∈ S i then mkChi x j else 0 := by
      simp [Finset.sum_ite_mem]
    rw [hS_eq]
    have hsplit : (∑ j : Fin n, if j ∈ S i then mkChi x j else 0) =
        (∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < 2 * k), if j ∈ S i then mkChi x j else 0) +
        (∑ j ∈ Finset.univ.filter (fun j : Fin n => ¬ j.val < 2 * k), if j ∈ S i then mkChi x j else 0) := by
      rw [Finset.sum_filter_add_sum_filter_not]
    rw [hsplit, add_comm]
    congr 1
    · -- ≥ 2k part equals eps i
      by_cases hodd : 2 * k < n
      · have hfilt : (Finset.univ.filter fun j : Fin n => ¬ j.val < 2 * k) = {⟨2 * k, hodd⟩} := by
          ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, Fin.ext_iff]
          have := j.isLt; omega
        rw [hfilt, Finset.sum_singleton]
        dsimp only [eps, mkChi]
        rw [dif_pos hodd]
        have hdiv : ¬ (2 * k) / 2 < k := by omega
        rw [dif_neg hdiv]
      · have hfilt : (Finset.univ.filter fun j : Fin n => ¬ j.val < 2 * k) = ∅ := by
          ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
          have := j.isLt; omega
        rw [hfilt, Finset.sum_empty]
        dsimp only [eps]; rw [dif_neg hodd]
    · -- < 2k part equals ∑ r : Fin k, w i r * sign (x r)
      let e : Fin k × Bool ≃ {j : Fin n // j.val < 2 * k} :=
        ⟨fun p => if p.2 then ⟨⟨2 * p.1.val, by omega⟩, by dsimp; omega⟩
                  else ⟨⟨2 * p.1.val + 1, by omega⟩, by dsimp; omega⟩,
         fun q => (⟨q.1.val / 2, by have := q.2; omega⟩, decide (q.1.val % 2 = 0)),
         fun ⟨r, b⟩ => by
           cases b
           · simp only [Bool.false_eq_true, ↓reduceIte, Prod.mk.injEq, Fin.ext_iff, decide_eq_false_iff_not]
             omega
           · simp only [↓reduceIte, Prod.mk.injEq, Fin.ext_iff, decide_eq_true_eq]
             omega,
         fun ⟨j, hj⟩ => by
           apply Subtype.ext; apply Fin.ext
           by_cases h0 : j.val % 2 = 0
           · simp [h0]; omega
           · simp [h0]; omega⟩
      have hsub : (∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < 2 * k),
          if j ∈ S i then mkChi x j else 0) =
          ∑ q : {j : Fin n // j.val < 2 * k}, if q.1 ∈ S i then mkChi x q.1 else 0 := by
        rw [← Finset.sum_coe_sort]
        refine Finset.sum_bij (fun q _ => ⟨q.1, (Finset.mem_filter.mp q.2).2⟩)
          (fun _ _ => Finset.mem_univ _)
          (fun a _ b _ h => Subtype.ext (congrArg (fun q : {j : Fin n // j.val < 2 * k} => q.1) h))
          (fun q _ => ⟨⟨q.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, q.2⟩⟩, Finset.mem_univ _, rfl⟩)
          (fun _ _ => rfl)
      rw [hsub, ← Fintype.sum_equiv e _ _ (fun _ => rfl), Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [Fintype.sum_bool]
      have hd1 : (2 * r.val) / 2 < k := by omega
      have hd2 : (2 * r.val + 1) / 2 < k := by omega
      have hm1 : (2 * r.val) % 2 = 0 := by omega
      have hm2 : ¬ (2 * r.val + 1) % 2 = 0 := by omega
      have hr1 : ∀ h, (⟨(2 * r.val) / 2, h⟩ : Fin k) = r := fun _ => Fin.ext (by dsimp; omega)
      have hr2 : ∀ h, (⟨(2 * r.val + 1) / 2, h⟩ : Fin k) = r := fun _ => Fin.ext (by dsimp; omega)
      simp only [e, Equiv.coe_fn_mk, mkChi, w, ↓reduceIte, Bool.false_eq_true, dif_pos hd1,
        dif_pos hd2, if_pos hm1, if_neg hm2, hr1, hr2]
      split_ifs <;> ring
  -- Now union bound over i : Fin n!
  let d : ℝ := 6 * Real.sqrt n - 1
  have hsqrt_ge : (6 : ℝ) ≤ Real.sqrt n := by
    have : (36 : ℝ) ≤ n := by exact_mod_cast (by omega : 36 ≤ n)
    calc (6 : ℝ) = Real.sqrt 36 := by norm_num
      _ ≤ Real.sqrt n := Real.sqrt_le_sqrt this
  have hd_pos : 0 ≤ d := by dsimp only [d]; linarith
  have hbad_i : ∀ i : Fin n,
      ((Finset.univ.filter fun x : Fin k → Bool => d < |∑ r : Fin k, w i r * sign (x r)|).card : ℝ) /
        (2 ^ k : ℝ) ≤ 2 * Real.exp (-34) := by
    intro i
    have hw_val : ∀ r, w i r = 1 ∨ w i r = -1 ∨ w i r = 0 := by
      intro r; dsimp only [w]; split_ifs <;> norm_num
    have hK : ((Finset.univ.filter fun r : Fin k => w i r ≠ 0).card : ℝ) ≤ k := by
      have : (Finset.univ.filter fun r : Fin k => w i r ≠ 0).card ≤ k :=
        (Finset.card_le_univ _).trans (by simp)
      exact_mod_cast this
    have hup := hoeffding_one_sided (w i) hw_val k hK hd_pos hk_pos
    have hlo := hoeffding_lower_tail (w i) hw_val k hK hd_pos hk_pos
    have hexp_le : Real.exp (-(d ^ 2 / (2 * k))) ≤ Real.exp (-34) := by
      apply Real.exp_le_exp.mpr
      have hn_pos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      have hd_ge : (35 / 6 : ℝ) * Real.sqrt n ≤ d := by
        dsimp only [d]; nlinarith
      have hd_sq : (34 : ℝ) * n ≤ d ^ 2 := by
        have h1 : ((35 / 6 : ℝ) * Real.sqrt n) ^ 2 ≤ d ^ 2 :=
          pow_le_pow_left₀ (by positivity) hd_ge 2
        rw [mul_pow, Real.sq_sqrt hn_pos.le] at h1
        nlinarith
      have hdiv : (34 : ℝ) ≤ d ^ 2 / (2 * k) := by
        rw [le_div_iff₀ (by positivity)]
        nlinarith
      linarith
    have hsub : (Finset.univ.filter fun x : Fin k → Bool => d < |∑ r : Fin k, w i r * sign (x r)|) ⊆
        (Finset.univ.filter fun x : Fin k → Bool => d ≤ ∑ r : Fin k, w i r * sign (x r)) ∪
        (Finset.univ.filter fun x : Fin k → Bool => ∑ r : Fin k, w i r * sign (x r) ≤ -d) := by
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hx ⊢
      rcases le_or_gt 0 (∑ r : Fin k, w i r * sign (x r)) with h | h
      · left; rw [abs_of_nonneg h] at hx; linarith
      · right; rw [abs_of_neg h] at hx; linarith
    have hcard : ((Finset.univ.filter fun x : Fin k → Bool =>
        d < |∑ r : Fin k, w i r * sign (x r)|).card : ℝ) ≤
        ((Finset.univ.filter fun x : Fin k → Bool => d ≤ ∑ r : Fin k, w i r * sign (x r)).card : ℝ) +
        ((Finset.univ.filter fun x : Fin k → Bool => ∑ r : Fin k, w i r * sign (x r) ≤ -d).card : ℝ) := by
      exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    have h2pos : (0 : ℝ) < 2 ^ k := by positivity
    calc ((Finset.univ.filter fun x : Fin k → Bool =>
            d < |∑ r : Fin k, w i r * sign (x r)|).card : ℝ) / (2 ^ k : ℝ)
        ≤ _ / (2 ^ k : ℝ) := div_le_div_of_nonneg_right hcard h2pos.le
      _ = _ + _ := add_div _ _ _
      _ ≤ Real.exp (-(d ^ 2 / (2 * k))) + Real.exp (-(d ^ 2 / (2 * k))) := add_le_add hup hlo
      _ ≤ 2 * Real.exp (-34) := by linarith
  -- Total bad x count < 2^k!
  let Bad := Finset.univ.biUnion fun i : Fin n =>
    Finset.univ.filter fun x : Fin k → Bool => d < |∑ r : Fin k, w i r * sign (x r)|
  have hBad_lt : (Bad.card : ℝ) < 2 ^ k := by
    have h2pos : (0 : ℝ) < 2 ^ k := by positivity
    rw [← div_lt_one h2pos]
    have hcard_le : (Bad.card : ℝ) ≤ ∑ i : Fin n,
        ((Finset.univ.filter fun x : Fin k → Bool =>
          d < |∑ r : Fin k, w i r * sign (x r)|).card : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le
    calc (Bad.card : ℝ) / (2 ^ k : ℝ)
        ≤ (∑ i : Fin n, ((Finset.univ.filter fun x : Fin k → Bool =>
            d < |∑ r : Fin k, w i r * sign (x r)|).card : ℝ)) / (2 ^ k : ℝ) :=
          div_le_div_of_nonneg_right hcard_le h2pos.le
      _ = ∑ i : Fin n, ((Finset.univ.filter fun x : Fin k → Bool =>
            d < |∑ r : Fin k, w i r * sign (x r)|).card : ℝ) / (2 ^ k : ℝ) := Finset.sum_div _ _ _
      _ ≤ ∑ _i : Fin n, (2 * Real.exp (-34)) := Finset.sum_le_sum fun i _ => hbad_i i
      _ = (n : ℝ) * (2 * Real.exp (-34)) := by simp
      _ < 1 := by
          have he1 : (271 / 100 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
          have he34 : (271 / 100 : ℝ) ^ 34 < Real.exp 34 := by
            have : Real.exp 34 = (Real.exp 1) ^ 34 := by
              rw [← Real.exp_nat_mul]; norm_num
            rw [this]
            exact pow_lt_pow_left₀ he1 (by norm_num) (by norm_num)
          have hnum : (2 : ℝ) * (10 ^ 14 : ℝ) < (271 / 100 : ℝ) ^ 34 := by norm_num
          have hnR : (n : ℝ) ≤ 10 ^ 14 := by exact_mod_cast hn2
          have hexp_inv : Real.exp (-34) = (Real.exp 34)⁻¹ := Real.exp_neg 34
          rw [hexp_inv]
          have hpos34 : 0 < Real.exp 34 := Real.exp_pos 34
          have hprod : (n : ℝ) * 2 < Real.exp 34 := by linarith
          calc (n : ℝ) * (2 * (Real.exp 34)⁻¹)
              = ((n : ℝ) * 2) / Real.exp 34 := by ring
            _ < 1 := (div_lt_one hpos34).mpr hprod
  have hlt_nat : Bad.card < (Finset.univ : Finset (Fin k → Bool)).card := by
    have hcard_univ : ((Finset.univ : Finset (Fin k → Bool)).card : ℝ) = 2 ^ k := by
      simp [Fintype.card_bool]
    exact_mod_cast (hcard_univ ▸ hBad_lt)
  obtain ⟨x, _, hx_not⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt_nat
  refine ⟨mkChi x, hmkChi_pm x, fun i => ?_⟩
  have hx_i : ¬ d < |∑ r : Fin k, w i r * sign (x r)| := by
    intro hlt
    exact hx_not (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩⟩)
  rw [hsum_eq i x]
  calc |eps i + ∑ r : Fin k, w i r * sign (x r)|
      ≤ |eps i| + |∑ r : Fin k, w i r * sign (x r)| := abs_add_le _ _
    _ ≤ 1 + d := add_le_add (heps_abs i) (not_lt.mp hx_i)
    _ = 6 * Real.sqrt n := by dsimp only [d]; ring

/- ## Section 4: Croot–Lev–Pach algebraic proof of Kleitman's diameter bound (up to factor 2) -/

private def boolToF2 {m : ℕ} (x : Fin m → Bool) : Fin m → ZMod 2 :=
  fun i => if x i then 1 else 0

private lemma boolToF2_add {m : ℕ} (x y : Fin m → Bool) (i : Fin m) :
    boolToF2 x i + boolToF2 y i = if x i ≠ y i then 1 else 0 := by
  dsimp only [boolToF2]
  cases x i <;> cases y i <;> decide

private def clpPoly {m : ℕ} (t : ℕ) (z : Fin m → ZMod 2) : ZMod 2 :=
  ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin m) => S.card ≤ 2 * t), ∏ i ∈ S, z i

private lemma clpPoly_eval {m : ℕ} (t : ℕ) (z : Fin m → ZMod 2)
    (hw : (Finset.univ.filter fun i : Fin m => z i ≠ 0).card ≤ 2 * t) :
    clpPoly t z = if z = 0 then 1 else 0 := by
  let supp := Finset.univ.filter fun i : Fin m => z i ≠ 0
  have hprod : ∀ S : Finset (Fin m),
      (∏ i ∈ S, z i) = if S ⊆ supp then (1 : ZMod 2) else 0 := by
    intro S
    by_cases hS : S ⊆ supp
    · rw [if_pos hS]
      refine Finset.prod_eq_one fun i hi => ?_
      have hne : z i ≠ 0 := (Finset.mem_filter.mp (hS hi)).2
      revert hne; generalize z i = a; fin_cases a
      · intro h; exact absurd rfl h
      · intro _; rfl
    · rw [if_neg hS]
      rw [Finset.not_subset] at hS
      obtain ⟨i, hiS, hni⟩ := hS
      have hz0 : z i = 0 := by
        by_contra hne
        exact hni (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩)
      exact Finset.prod_eq_zero hiS hz0
  unfold clpPoly
  simp_rw [hprod]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hfilt : (Finset.univ.filter fun S : Finset (Fin m) => S.card ≤ 2 * t).filter (· ⊆ supp) =
      supp.powerset := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_powerset]
    exact ⟨fun h => h.2, fun h => ⟨(Finset.card_le_card h).trans hw, h⟩⟩
  rw [hfilt, Finset.card_powerset]
  by_cases hz : z = 0
  · rw [if_pos hz]
    have hsupp : supp = ∅ := by ext i; simp [supp, hz]
    rw [hsupp, Finset.card_empty, pow_zero]; rfl
  · rw [if_neg hz]
    have hpos : 0 < supp.card := by
      refine Finset.card_pos.mpr ?_
      have hex : ∃ i, z i ≠ 0 := by
        by_contra hall; push Not at hall; exact hz (funext hall)
      obtain ⟨i, hi⟩ := hex
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
    obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
    rw [hr, pow_succ, Nat.cast_mul]
    have h2 : ((2 : ℕ) : ZMod 2) = 0 := by decide
    rw [h2, mul_zero]

/-- Croot–Lev–Pach diameter bound: any `C ⊆ (Fin m → Bool)` whose pairwise Hamming distance is
at most `2t` satisfies `|C| ≤ 2 * ∑_{k ≤ t} C(m, k)`. -/
private lemma clp_diameter_bound {m t : ℕ} (C : Finset (Fin m → Bool))
    (hdiam : ∀ x ∈ C, ∀ y ∈ C, (Finset.univ.filter fun i : Fin m => x i ≠ y i).card ≤ 2 * t) :
    C.card ≤ 2 * ∑ k ∈ Finset.range (t + 1), m.choose k := by
  let Small : Finset (Finset (Fin m)) := Finset.univ.filter fun A : Finset (Fin m) => A.card ≤ t
  have hSmall_card : Small.card = ∑ k ∈ Finset.range (t + 1), m.choose k := by
    have hbij : Small = (Finset.range (t + 1)).biUnion fun k =>
        (Finset.univ : Finset (Fin m)).powersetCard k := by
      ext A
      simp only [Small, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
        Finset.mem_range, Finset.mem_powersetCard, Finset.subset_univ, true_and]
      exact ⟨fun h => ⟨A.card, Nat.lt_succ_of_le h, rfl⟩, fun ⟨k, hk, hka⟩ => hka ▸ Nat.lt_succ_iff.mp hk⟩
    rw [hbij, Finset.card_biUnion]
    · refine Finset.sum_congr rfl fun k _ => by simp [Finset.card_powersetCard]
    · intro k₁ _ k₂ _ hne
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro A h1 h2
      exact hne ((Finset.mem_powersetCard.mp h1).2.symm.trans (Finset.mem_powersetCard.mp h2).2)
  rw [← hSmall_card]
  -- Decompose clpPoly t (u + v) into rank-1 sums indexed by Small × 2!
  let Big : Finset (Finset (Fin m)) := Finset.univ.filter fun S : Finset (Fin m) => S.card ≤ 2 * t
  let gFun : Finset (Fin m) → (Fin m → ZMod 2) → ZMod 2 := fun A v =>
    ∑ S ∈ Big.filter (fun S => A ⊆ S), ∏ i ∈ S \ A, v i
  let hFun : Finset (Fin m) → (Fin m → ZMod 2) → ZMod 2 := fun B u =>
    ∑ S ∈ Big.filter (fun S => B ⊆ S ∧ t < (S \ B).card), ∏ i ∈ S \ B, u i
  have hdecomp : ∀ u v : Fin m → ZMod 2,
      clpPoly t (u + v) =
        (∑ A ∈ Small, (∏ i ∈ A, u i) * gFun A v) +
        (∑ B ∈ Small, hFun B u * (∏ i ∈ B, v i)) := by
    intro u v
    unfold clpPoly
    change (∑ S ∈ Big, ∏ i ∈ S, (u i + v i)) = _
    have hprod_add : ∀ S : Finset (Fin m),
        (∏ i ∈ S, (u i + v i)) =
          (∑ A ∈ S.powerset.filter (fun A => A.card ≤ t), (∏ i ∈ A, u i) * (∏ i ∈ S \ A, v i)) +
          (∑ A ∈ S.powerset.filter (fun A => ¬ A.card ≤ t), (∏ i ∈ A, u i) * (∏ i ∈ S \ A, v i)) := by
      intro S
      rw [Finset.prod_add, Finset.sum_filter_add_sum_filter_not]
    simp_rw [hprod_add, Finset.sum_add_distrib]
    congr 1
    · -- First part: swap S ∈ Big and A ∈ Small!
      have h1 : (∑ S ∈ Big, ∑ A ∈ S.powerset.filter (fun A => A.card ≤ t),
          (∏ i ∈ A, u i) * (∏ i ∈ S \ A, v i)) =
          ∑ S ∈ Big, ∑ A ∈ Small, if A ⊆ S then (∏ i ∈ A, u i) * (∏ i ∈ S \ A, v i) else 0 := by
        refine Finset.sum_congr rfl fun S _ => ?_
        rw [← Finset.sum_filter]
        refine Finset.sum_congr ?_ fun _ _ => rfl
        ext A; simp [Small, Finset.mem_powerset, and_comm]
      rw [h1, Finset.sum_comm]
      refine Finset.sum_congr rfl fun A _ => ?_
      rw [← Finset.sum_filter, Finset.mul_sum]
    · -- Second part: reindex A ↦ B = S \ A, swap S ∈ Big and B ∈ Small!
      have h2 : ∀ S ∈ Big,
          (∑ A ∈ S.powerset.filter (fun A => ¬ A.card ≤ t), (∏ i ∈ A, u i) * (∏ i ∈ S \ A, v i)) =
          ∑ B ∈ Small, if B ⊆ S ∧ t < (S \ B).card then (∏ i ∈ S \ B, u i) * (∏ i ∈ B, v i) else 0 := by
        intro S hS
        have hScard : S.card ≤ 2 * t := (Finset.mem_filter.mp hS).2
        rw [← Finset.sum_filter]
        refine Finset.sum_bij (fun A _ => S \ A) ?_ ?_ ?_ ?_
        · intro A hA
          simp only [Finset.mem_filter, Finset.mem_powerset, not_le] at hA
          have hcard : (S \ A).card ≤ t := by
            rw [Finset.card_sdiff_of_subset hA.1]; omega
          have hsdiff : S \ (S \ A) = A := Finset.sdiff_sdiff_eq_self hA.1
          exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcard⟩,
            Finset.sdiff_subset, by rw [hsdiff]; exact hA.2⟩
        · intro A₁ hA₁ A₂ hA₂ heq
          have h1 : A₁ ⊆ S := Finset.mem_powerset.mp (Finset.mem_filter.mp hA₁).1
          have h2 : A₂ ⊆ S := Finset.mem_powerset.mp (Finset.mem_filter.mp hA₂).1
          calc A₁ = S \ (S \ A₁) := (Finset.sdiff_sdiff_eq_self h1).symm
            _ = S \ (S \ A₂) := by rw [heq]
            _ = A₂ := Finset.sdiff_sdiff_eq_self h2
        · intro B hB
          simp only [Finset.mem_filter, Small, Finset.mem_univ, true_and] at hB
          refine ⟨S \ B, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr Finset.sdiff_subset, not_le.mpr hB.2.2⟩,
            Finset.sdiff_sdiff_eq_self hB.2.1⟩
        · intro A hA
          have h1 : A ⊆ S := Finset.mem_powerset.mp (Finset.mem_filter.mp hA).1
          rw [Finset.sdiff_sdiff_eq_self h1]
      rw [Finset.sum_congr rfl h2, Finset.sum_comm]
      refine Finset.sum_congr rfl fun B _ => ?_
      rw [← Finset.sum_filter, Finset.sum_mul]
  -- Define injective map Φ : (C → ZMod 2) → (Small → ZMod 2) × (Small → ZMod 2)!
  let Φ : (C → ZMod 2) → (Small → ZMod 2) × (Small → ZMod 2) := fun c =>
    (fun A => ∑ y : C, c y * gFun A.1 (boolToF2 y.1),
     fun B => ∑ y : C, c y * (∏ i ∈ B.1, boolToF2 y.1 i))
  have hΦ_inj : Function.Injective Φ := by
    intro c₁ c₂ hEq
    have h1 : ∀ A : Small, (∑ y : C, c₁ y * gFun A.1 (boolToF2 y.1)) =
        ∑ y : C, c₂ y * gFun A.1 (boolToF2 y.1) := fun A => congrFun (congrArg Prod.fst hEq) A
    have h2 : ∀ B : Small, (∑ y : C, c₁ y * (∏ i ∈ B.1, boolToF2 y.1 i)) =
        ∑ y : C, c₂ y * (∏ i ∈ B.1, boolToF2 y.1 i) := fun B => congrFun (congrArg Prod.snd hEq) B
    have hrecover : ∀ (c : C → ZMod 2) (x : C),
        c x = (∑ A : Small, (∏ i ∈ A.1, boolToF2 x.1 i) * (∑ y : C, c y * gFun A.1 (boolToF2 y.1))) +
              (∑ B : Small, hFun B.1 (boolToF2 x.1) * (∑ y : C, c y * (∏ i ∈ B.1, boolToF2 y.1 i))) := by
      intro c x
      have hid : ∀ y : C, clpPoly t (boolToF2 x.1 + boolToF2 y.1) = if y = x then 1 else 0 := by
        intro y
        have hw : (Finset.univ.filter fun i : Fin m => (boolToF2 x.1 + boolToF2 y.1) i ≠ 0).card ≤ 2 * t := by
          have heq : (Finset.univ.filter fun i : Fin m => (boolToF2 x.1 + boolToF2 y.1) i ≠ 0) =
              Finset.univ.filter fun i : Fin m => x.1 i ≠ y.1 i := by
            ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pi.add_apply, boolToF2_add]
            split_ifs with h <;> simp [h]
          rw [heq]; exact hdiam x.1 x.2 y.1 y.2
        rw [clpPoly_eval t _ hw]
        have hzero : boolToF2 x.1 + boolToF2 y.1 = 0 ↔ y = x := by
          rw [funext_iff, Subtype.ext_iff, funext_iff]
          constructor
          · intro h i
            have hi := h i
            simp only [Pi.add_apply, Pi.zero_apply, boolToF2_add] at hi
            by_contra hne
            have hne' : x.1 i ≠ y.1 i := fun h' => hne h'.symm
            rw [if_pos hne'] at hi
            exact one_ne_zero hi
          · intro h i
            simp only [Pi.add_apply, Pi.zero_apply, boolToF2_add, h i, ne_eq, not_true_eq_false, ↓reduceIte]
        by_cases hyx : y = x
        · rw [if_pos (hzero.mpr hyx), if_pos hyx]
        · rw [if_neg (fun h => hyx (hzero.mp h)), if_neg hyx]
      calc c x = ∑ y : C, c y * (if y = x then 1 else 0) := by simp
        _ = ∑ y : C, c y * clpPoly t (boolToF2 x.1 + boolToF2 y.1) := by simp_rw [hid]
        _ = ∑ y : C, (c y * (∑ A ∈ Small, (∏ i ∈ A, boolToF2 x.1 i) * gFun A (boolToF2 y.1)) +
              c y * (∑ B ∈ Small, hFun B (boolToF2 x.1) * (∏ i ∈ B, boolToF2 y.1 i))) := by
            refine Finset.sum_congr rfl fun y _ => by rw [hdecomp, mul_add]
        _ = (∑ y : C, ∑ A : Small, c y * ((∏ i ∈ A.1, boolToF2 x.1 i) * gFun A.1 (boolToF2 y.1))) +
            (∑ y : C, ∑ B : Small, c y * (hFun B.1 (boolToF2 x.1) * (∏ i ∈ B.1, boolToF2 y.1 i))) := by
            rw [Finset.sum_add_distrib]
            congr 1 <;> refine Finset.sum_congr rfl fun y _ => by
              rw [Finset.mul_sum, ← Finset.sum_coe_sort]
        _ = (∑ A : Small, (∏ i ∈ A.1, boolToF2 x.1 i) * (∑ y : C, c y * gFun A.1 (boolToF2 y.1))) +
            (∑ B : Small, hFun B.1 (boolToF2 x.1) * (∑ y : C, c y * (∏ i ∈ B.1, boolToF2 y.1 i))) := by
            congr 1
            · rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun A _ => ?_
              rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun y _ => by ring
            · rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun B _ => ?_
              rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun y _ => by ring
    funext x
    rw [hrecover c₁ x, hrecover c₂ x]
    simp_rw [h1, h2]
  have hcard := Fintype.card_le_of_injective Φ hΦ_inj
  simp only [Fintype.card_fun, Fintype.card_prod, Fintype.card_coe, ZMod.card, ← pow_add,
    ← two_mul] at hcard
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hcard

/- ## Section 5: Bucketed sum entropy bound & Partial Coloring Lemma -/

private noncomputable def bucket {m : ℕ} (T : Finset (Fin m)) (lam : ℝ) (x : Fin m → Bool) :
    Finset.Icc (-(m : ℤ) - 1) (m + 1) :=
  ⟨max (-(m : ℤ) - 1) (min ((m : ℤ) + 1)
      ⌊((∑ j ∈ T, sign (x j)) + lam * Real.sqrt m) / (2 * lam * Real.sqrt m)⌋),
    Finset.mem_Icc.mpr ⟨le_max_left _ _, max_le (by omega) (min_le_left _ _)⟩⟩

private lemma bucket_val_eq {m : ℕ} (hm : 1 ≤ m) (T : Finset (Fin m)) {lam : ℝ} (hlam : 1 ≤ lam)
    (x : Fin m → Bool) :
    (bucket T lam x).1 =
      ⌊((∑ j ∈ T, sign (x j)) + lam * Real.sqrt m) / (2 * lam * Real.sqrt m)⌋ := by
  dsimp only [bucket]
  have hsqrt : (1 : ℝ) ≤ Real.sqrt m := by
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm
    calc (1 : ℝ) = Real.sqrt 1 := by norm_num
      _ ≤ Real.sqrt m := Real.sqrt_le_sqrt this
  have hden : (2 : ℝ) ≤ 2 * lam * Real.sqrt m := by nlinarith
  have hden_pos : 0 < 2 * lam * Real.sqrt m := by linarith
  have hsum_abs : |∑ j ∈ T, sign (x j)| ≤ m := by
    calc |∑ j ∈ T, sign (x j)|
        ≤ ∑ j ∈ T, |sign (x j)| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ _j ∈ T, (1 : ℝ) := Finset.sum_congr rfl fun j _ => by unfold sign; split_ifs <;> norm_num
      _ = (T.card : ℝ) := by simp
      _ ≤ m := by exact_mod_cast (Finset.card_le_univ T).trans (by simp)
  have hlo : (-(m : ℤ) - 1 : ℤ) ≤
      ⌊((∑ j ∈ T, sign (x j)) + lam * Real.sqrt m) / (2 * lam * Real.sqrt m)⌋ := by
    rw [Int.le_floor]; push_cast
    rw [le_div_iff₀ hden_pos]
    have := (abs_le.mp hsum_abs).1
    have h1 : (-(m : ℝ) - 1) * (2 * lam * Real.sqrt m) ≤ -(m : ℝ) - lam * Real.sqrt m := by nlinarith
    linarith
  have hhi : ⌊((∑ j ∈ T, sign (x j)) + lam * Real.sqrt m) / (2 * lam * Real.sqrt m)⌋ ≤
      (m : ℤ) + 1 := by
    have hlt : ((∑ j ∈ T, sign (x j)) + lam * Real.sqrt m) / (2 * lam * Real.sqrt m) <
        (((m : ℤ) + 1 + 1 : ℤ) : ℝ) := by
      push_cast; rw [div_lt_iff₀ hden_pos]
      have := (abs_le.mp hsum_abs).2
      nlinarith
    exact Int.lt_add_one_iff.mp (Int.floor_lt.mpr hlt)
  rw [min_eq_right hhi, max_eq_right hlo]

private lemma uH_bucket_le {m : ℕ} (hm : 2 ≤ m) (T : Finset (Fin m)) (hT : 2 * T.card ≤ m)
    {lam : ℝ} (hlam : 2 ≤ lam) :
    uH (bucket T lam) ≤ (2 * lam ^ 2 + 3) * Real.exp (-lam ^ 2) := by
  have hm1 : 1 ≤ m := by omega
  have hlam1 : 1 ≤ lam := by linarith
  have hm_pos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hsqrt_pos : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm_pos
  have hden_pos : 0 < 2 * lam * Real.sqrt m := by positivity
  -- Indicator weight w : Fin m → ℝ for T!
  let w : Fin m → ℝ := fun j => if j ∈ T then 1 else 0
  have hw_val : ∀ j, w j = 1 ∨ w j = -1 ∨ w j = 0 := fun j => by
    dsimp only [w]; split_ifs <;> simp
  have hsum_w : ∀ x : Fin m → Bool, (∑ j : Fin m, w j * sign (x j)) = ∑ j ∈ T, sign (x j) := by
    intro x; dsimp only [w]
    simp_rw [ite_mul, one_mul, zero_mul, Finset.sum_ite_mem, Finset.univ_inter]
  let K : ℕ := m / 2
  have hK_pos : 0 < (K : ℝ) := by
    have : 0 < K := by omega
    exact_mod_cast this
  have h2K_le : (2 * K : ℝ) ≤ m := by exact_mod_cast (by omega : 2 * K ≤ m)
  have hT_le_K : ((Finset.univ.filter fun j : Fin m => w j ≠ 0).card : ℝ) ≤ K := by
    have heq : (Finset.univ.filter fun j : Fin m => w j ≠ 0) = T := by
      ext j; simp [w]
    rw [heq]; exact_mod_cast (by omega : T.card ≤ K)
  -- Tail probability bounds for b ≥ k and b ≤ -k (k ≥ 1)!
  have htail_pos : ∀ k : ℕ, 1 ≤ k →
      ∀ b : Finset.Icc (-(m : ℤ) - 1) (m + 1), (k : ℤ) ≤ b.1 →
        uprob (bucket T lam) b ≤ Real.exp (-((2 * (k : ℝ) - 1) ^ 2 * lam ^ 2)) := by
    intro k hk b hb
    let d : ℝ := (2 * (k : ℝ) - 1) * lam * Real.sqrt m
    have h2k : (0 : ℝ) ≤ 2 * (k : ℝ) - 1 := by
      have : (1 : ℝ) ≤ k := by exact_mod_cast hk
      linarith
    have hd_nn : 0 ≤ d := by dsimp only [d]; positivity
    have h1 : uprob (bucket T lam) b ≤
        ((Finset.univ.filter fun x : Fin m → Bool => d ≤ ∑ j : Fin m, w j * sign (x j)).card : ℝ) /
          (2 ^ m : ℝ) := by
      refine uprob_le_card_div (bucket T lam) b _ fun x hx2 => ?_
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rw [hsum_w]
      have hb_eq : (k : ℤ) ≤
          ⌊((∑ j ∈ T, sign (x j)) + lam * Real.sqrt m) / (2 * lam * Real.sqrt m)⌋ := by
        rw [← bucket_val_eq hm1 T hlam1 x, hx2]; exact hb
      have hle := Int.le_floor.mp hb_eq
      push_cast at hle
      rw [le_div_iff₀ hden_pos] at hle
      dsimp only [d]; linarith
    refine h1.trans ((hoeffding_one_sided w hw_val K hT_le_K hd_nn hK_pos).trans ?_)
    apply Real.exp_le_exp.mpr
    have hd_sq : d ^ 2 = (2 * (k : ℝ) - 1) ^ 2 * lam ^ 2 * m := by
      dsimp only [d]; rw [mul_pow, mul_pow, Real.sq_sqrt hm_pos.le]
    rw [hd_sq]
    have hdiv : (2 * (k : ℝ) - 1) ^ 2 * lam ^ 2 ≤
        (2 * (k : ℝ) - 1) ^ 2 * lam ^ 2 * m / (2 * K) := by
      rw [le_div_iff₀ (by positivity)]
      have hfac : 0 ≤ (2 * (k : ℝ) - 1) ^ 2 * lam ^ 2 := by positivity
      nlinarith
    linarith
  have htail_neg : ∀ k : ℕ, 1 ≤ k →
      ∀ b : Finset.Icc (-(m : ℤ) - 1) (m + 1), b.1 ≤ -(k : ℤ) →
        uprob (bucket T lam) b ≤ Real.exp (-((2 * (k : ℝ) - 1) ^ 2 * lam ^ 2)) := by
    intro k hk b hb
    let d : ℝ := (2 * (k : ℝ) - 1) * lam * Real.sqrt m
    have h2k : (0 : ℝ) ≤ 2 * (k : ℝ) - 1 := by
      have : (1 : ℝ) ≤ k := by exact_mod_cast hk
      linarith
    have hd_nn : 0 ≤ d := by dsimp only [d]; positivity
    have h1 : uprob (bucket T lam) b ≤
        ((Finset.univ.filter fun x : Fin m → Bool => ∑ j : Fin m, w j * sign (x j) ≤ -d).card : ℝ) /
          (2 ^ m : ℝ) := by
      refine uprob_le_card_div (bucket T lam) b _ fun x hx2 => ?_
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rw [hsum_w]
      have hb_eq : ⌊((∑ j ∈ T, sign (x j)) + lam * Real.sqrt m) / (2 * lam * Real.sqrt m)⌋ ≤
          -(k : ℤ) := by
        rw [← bucket_val_eq hm1 T hlam1 x, hx2]; exact hb
      have hlt : ((∑ j ∈ T, sign (x j)) + lam * Real.sqrt m) / (2 * lam * Real.sqrt m) <
          (-(k : ℤ) + 1 : ℤ) := Int.floor_lt.mp (by omega)
      push_cast at hlt
      rw [div_lt_iff₀ hden_pos] at hlt
      dsimp only [d]; linarith
    refine h1.trans ((hoeffding_lower_tail w hw_val K hT_le_K hd_nn hK_pos).trans ?_)
    apply Real.exp_le_exp.mpr
    have hd_sq : d ^ 2 = (2 * (k : ℝ) - 1) ^ 2 * lam ^ 2 * m := by
      dsimp only [d]; rw [mul_pow, mul_pow, Real.sq_sqrt hm_pos.le]
    rw [hd_sq]
    have hdiv : (2 * (k : ℝ) - 1) ^ 2 * lam ^ 2 ≤
        (2 * (k : ℝ) - 1) ^ 2 * lam ^ 2 * m / (2 * K) := by
      rw [le_div_iff₀ (by positivity)]
      have hfac : 0 ≤ (2 * (k : ℝ) - 1) ^ 2 * lam ^ 2 := by positivity
      nlinarith
    linarith
  -- Also bound P(bucket ≠ 0) ≤ 2 * exp(-lam^2)!
  have h0_mem : (0 : ℤ) ∈ Finset.Icc (-(m : ℤ) - 1) (m + 1) :=
    Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  let b0 : Finset.Icc (-(m : ℤ) - 1) (m + 1) := ⟨0, h0_mem⟩
  have hneq0_le : 1 - uprob (bucket T lam) b0 ≤ 2 * Real.exp (-lam ^ 2) := by
    let d1 : ℝ := lam * Real.sqrt m
    have hd1 : 0 ≤ d1 := by positivity
    let S1 : Finset (Fin m → Bool) :=
      Finset.univ.filter fun x : Fin m → Bool => d1 ≤ ∑ j : Fin m, w j * sign (x j)
    let S2 : Finset (Fin m → Bool) :=
      Finset.univ.filter fun x : Fin m → Bool => ∑ j : Fin m, w j * sign (x j) ≤ -d1
    have h1 : 1 - uprob (bucket T lam) b0 ≤ ((S1 ∪ S2).card : ℝ) / (2 ^ m : ℝ) := by
      refine one_sub_uprob_le_card_div (bucket T lam) b0 (S1 ∪ S2) fun x hx => ?_
      simp only [S1, S2, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hsum_w]
      have hval : ⌊((∑ j ∈ T, sign (x j)) + lam * Real.sqrt m) / (2 * lam * Real.sqrt m)⌋ ≠ 0 := by
        intro h0; exact hx (Subtype.ext (by rw [bucket_val_eq hm1 T hlam1 x]; exact h0))
      rcases lt_or_gt_of_ne hval with hlt | hgt
      · right
        have hle : ⌊((∑ j ∈ T, sign (x j)) + lam * Real.sqrt m) / (2 * lam * Real.sqrt m)⌋ ≤ -1 := by omega
        have hlt' : ((∑ j ∈ T, sign (x j)) + lam * Real.sqrt m) / (2 * lam * Real.sqrt m) < 0 := by
          have := Int.floor_lt.mp (by omega : ⌊_⌋ < (0 : ℤ)); simpa using this
        rw [div_lt_iff₀ hden_pos, zero_mul] at hlt'
        dsimp only [d1]; linarith
      · left
        have hge : (1 : ℤ) ≤ ⌊((∑ j ∈ T, sign (x j)) + lam * Real.sqrt m) / (2 * lam * Real.sqrt m)⌋ := by omega
        have hge' : (1 : ℝ) ≤ ((∑ j ∈ T, sign (x j)) + lam * Real.sqrt m) / (2 * lam * Real.sqrt m) := by
          have := Int.le_floor.mp hge; simpa using this
        rw [le_div_iff₀ hden_pos, one_mul] at hge'
        dsimp only [d1]; linarith
    have hcard : ((S1 ∪ S2).card : ℝ) ≤ (S1.card : ℝ) + (S2.card : ℝ) := by
      exact_mod_cast Finset.card_union_le S1 S2
    have hup := hoeffding_one_sided w hw_val K hT_le_K hd1 hK_pos
    have hlo := hoeffding_lower_tail w hw_val K hT_le_K hd1 hK_pos
    have hexp_le : Real.exp (-(d1 ^ 2 / (2 * K))) ≤ Real.exp (-lam ^ 2) := by
      apply Real.exp_le_exp.mpr
      have hd1_sq : d1 ^ 2 = lam ^ 2 * m := by dsimp only [d1]; rw [mul_pow, Real.sq_sqrt hm_pos.le]
      rw [hd1_sq]
      have : lam ^ 2 ≤ lam ^ 2 * m / (2 * K) := by
        rw [le_div_iff₀ (by positivity)]; nlinarith [sq_nonneg lam]
      linarith
    have h2pos : (0 : ℝ) < 2 ^ m := by positivity
    calc 1 - uprob (bucket T lam) b0
        ≤ ((S1 ∪ S2).card : ℝ) / (2 ^ m : ℝ) := h1
      _ ≤ ((S1.card : ℝ) + (S2.card : ℝ)) / (2 ^ m : ℝ) := div_le_div_of_nonneg_right hcard h2pos.le
      _ = (S1.card : ℝ) / (2 ^ m : ℝ) + (S2.card : ℝ) / (2 ^ m : ℝ) := add_div _ _ _
      _ ≤ 2 * Real.exp (-lam ^ 2) := by linarith
  -- Bound nml(uprob b0) ≤ 2 * exp(-lam^2)!
  have hnml0 : nml (uprob (bucket T lam) b0) ≤ 2 * Real.exp (-lam ^ 2) := by
    let u := 1 - uprob (bucket T lam) b0
    have hu0 : 0 ≤ u := by dsimp only [u]; linarith [uprob_le_one (bucket T lam) b0]
    have hu1 : u < 1 := by
      have hexp : 2 * Real.exp (-lam ^ 2) < 1 := by
        have h4 : (4 : ℝ) ≤ lam ^ 2 := by nlinarith
        have he4 : (2 : ℝ) < Real.exp 4 := by
          have he1 : (2 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
          have hpow : (2 : ℝ) ^ 4 < (Real.exp 1) ^ 4 := pow_lt_pow_left₀ he1 (by norm_num) (by norm_num)
          have heq4 : Real.exp 4 = (Real.exp 1) ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
          rw [heq4]; linarith [show (2 : ℝ) < (2 : ℝ) ^ 4 by norm_num]
        have hle4 : Real.exp (-lam ^ 2) ≤ (Real.exp 4)⁻¹ :=
          (Real.exp_le_exp.mpr (by linarith : -lam ^ 2 ≤ -4)).trans_eq (Real.exp_neg 4)
        have hpos4 : 0 < Real.exp 4 := Real.exp_pos 4
        have hlt1 : 2 * (Real.exp 4)⁻¹ < 1 := by rw [← div_eq_mul_inv, div_lt_one hpos4]; exact he4
        linarith
      dsimp only [u]; linarith
    have heq : uprob (bucket T lam) b0 = 1 - u := by dsimp only [u]; ring
    rw [heq]
    exact (nml_one_sub_le hu0 hu1).trans hneq0_le
  -- Bound each nonzero term b using k = b.1.natAbs ≥ 1!
  have hnml_k : ∀ k : ℕ, 1 ≤ k →
      ∀ b : Finset.Icc (-(m : ℤ) - 1) (m + 1), b.1.natAbs = k →
        nml (uprob (bucket T lam) b) ≤
          (2 * (k : ℝ) - 1) ^ 2 * lam ^ 2 * Real.exp (-((2 * (k : ℝ) - 1) ^ 2 * lam ^ 2)) := by
    intro k hk b hbk
    have hprob : uprob (bucket T lam) b ≤ Real.exp (-((2 * (k : ℝ) - 1) ^ 2 * lam ^ 2)) := by
      rcases Int.natAbs_eq b.1 with hpos | hneg
      · exact htail_pos k hk b (by omega)
      · exact htail_neg k hk b (by omega)
    have hle_e : Real.exp (-((2 * (k : ℝ) - 1) ^ 2 * lam ^ 2)) ≤ Real.exp (-1) := by
      apply Real.exp_le_exp.mpr
      have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
      have h1 : (1 : ℝ) ≤ (2 * (k : ℝ) - 1) ^ 2 := by nlinarith
      have h2 : (4 : ℝ) ≤ lam ^ 2 := by nlinarith
      nlinarith
    calc nml (uprob (bucket T lam) b)
        ≤ nml (Real.exp (-((2 * (k : ℝ) - 1) ^ 2 * lam ^ 2))) :=
          nml_mono_on_Icc (uprob_nonneg _ _) hprob hle_e
      _ = (2 * (k : ℝ) - 1) ^ 2 * lam ^ 2 * Real.exp (-((2 * (k : ℝ) - 1) ^ 2 * lam ^ 2)) :=
          nml_exp_neg
  -- Clamped constructor for elements of Icc (-(m+1)) (m+1)
  let mkB : ℤ → Finset.Icc (-(m : ℤ) - 1) (m + 1) := fun z =>
    ⟨max (-(m : ℤ) - 1) (min ((m : ℤ) + 1) z),
      Finset.mem_Icc.mpr ⟨le_max_left _ _, max_le (by omega) (min_le_left _ _)⟩⟩
  have hmkB_val : ∀ z : ℤ, -(m : ℤ) - 1 ≤ z → z ≤ (m : ℤ) + 1 → (mkB z).1 = z := by
    intro z h1 h2; dsimp only [mkB]; rw [min_eq_right h2, max_eq_right h1]
  -- Sum over all b ∈ Icc (-(m+1)) (m+1) = {0} ∪ {±1} ∪ {±k | 2 ≤ k ≤ m+1}!
  have hsum_split : uH (bucket T lam) =
      nml (uprob (bucket T lam) b0) +
      ∑ k ∈ Finset.Icc 1 (m + 1),
        (nml (uprob (bucket T lam) (mkB (k : ℤ))) +
         nml (uprob (bucket T lam) (mkB (-(k : ℤ))))) := by
    unfold uH
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ b0)]
    congr 1
    let e : (Finset.Icc 1 (m + 1)) × Bool ≃ {b : Finset.Icc (-(m : ℤ) - 1) (m + 1) // b ≠ b0} :=
      ⟨fun p => if p.2 then ⟨mkB (p.1.1 : ℤ), by
                   intro h; have h1 := congrArg Subtype.val h
                   have hp := Finset.mem_Icc.mp p.1.2
                   rw [hmkB_val _ (by omega) (by omega)] at h1; dsimp [b0] at h1; omega⟩
                else ⟨mkB (-(p.1.1 : ℤ)), by
                   intro h; have h1 := congrArg Subtype.val h
                   have hp := Finset.mem_Icc.mp p.1.2
                   rw [hmkB_val _ (by omega) (by omega)] at h1; dsimp [b0] at h1; omega⟩,
       fun q => (⟨q.1.1.natAbs, Finset.mem_Icc.mpr ⟨by
                    have hne : q.1.1 ≠ 0 := fun h0 => q.2 (Subtype.ext h0)
                    omega,
                  by have := Finset.mem_Icc.mp q.1.2; omega⟩⟩, decide (0 < q.1.1)),
       fun ⟨⟨k, hk⟩, sgn⟩ => by
         have hk1 := (Finset.mem_Icc.mp hk).1
         have hk2 := (Finset.mem_Icc.mp hk).2
         cases sgn
         · apply Prod.ext
           · apply Subtype.ext
             simp only [Bool.false_eq_true, ↓reduceIte, hmkB_val (-(k : ℤ)) (by omega) (by omega),
               Int.natAbs_neg, Int.natAbs_natCast]
           · simp only [Bool.false_eq_true, ↓reduceIte, hmkB_val (-(k : ℤ)) (by omega) (by omega),
               decide_eq_false_iff_not]; omega
         · apply Prod.ext
           · apply Subtype.ext
             simp only [↓reduceIte, hmkB_val (k : ℤ) (by omega) (by omega), Int.natAbs_natCast]
           · simp only [↓reduceIte, hmkB_val (k : ℤ) (by omega) (by omega), decide_eq_true_eq]; omega,
       fun ⟨⟨z, hz⟩, hne⟩ => by
         have hz0 : z ≠ 0 := fun h => hne (Subtype.ext h)
         have hz_mem := Finset.mem_Icc.mp hz
         apply Subtype.ext; apply Subtype.ext
         by_cases hp : 0 < z
         · simp only [decide_eq_true hp, ↓reduceIte]
           rw [hmkB_val _ (by omega) (by omega), Int.natAbs_of_nonneg (by omega)]
         · simp only [decide_eq_false hp, Bool.false_eq_true, ↓reduceIte]
           rw [hmkB_val _ (by omega) (by omega)]
           have hneg := Int.ofNat_natAbs_of_nonpos (by omega : z ≤ 0)
           linarith⟩
    have hcoe : (∑ b ∈ Finset.univ.erase b0, nml (uprob (bucket T lam) b)) =
        ∑ q : {b : Finset.Icc (-(m : ℤ) - 1) (m + 1) // b ≠ b0}, nml (uprob (bucket T lam) q.1) := by
      rw [← Finset.sum_coe_sort]
      refine Finset.sum_bij (fun q _ => ⟨q.1, (Finset.mem_erase.mp q.2).1⟩)
        (fun _ _ => Finset.mem_univ _)
        (fun a _ b _ h => Subtype.ext (congrArg (fun x : {b : Finset.Icc (-(m : ℤ) - 1) (m + 1) // b ≠ b0} => x.1) h))
        (fun q _ => ⟨⟨q.1, Finset.mem_erase.mpr ⟨q.2, Finset.mem_univ _⟩⟩, Finset.mem_univ _, rfl⟩)
        (fun _ _ => rfl)
    rw [hcoe, ← Fintype.sum_equiv e _ _ (fun _ => rfl), Fintype.sum_prod_type]
    rw [← Finset.sum_coe_sort (Finset.Icc 1 (m + 1))]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Fintype.sum_bool]
    simp only [e, Equiv.coe_fn_mk, ↓reduceIte, Bool.false_eq_true]
  rw [hsum_split]
  -- Split Icc 1 (m+1) into k = 1 and Icc 2 (m+1)!
  have hIcc : Finset.Icc 1 (m + 1) = insert 1 (Finset.Icc 2 (m + 1)) := by
    ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  have h1_not : (1 : ℕ) ∉ Finset.Icc 2 (m + 1) := by simp
  rw [hIcc, Finset.sum_insert h1_not]
  -- k = 1 term: ≤ 2 * lam^2 * exp(-lam^2)
  have hk1_le :
      nml (uprob (bucket T lam) (mkB ((1 : ℕ) : ℤ))) +
      nml (uprob (bucket T lam) (mkB (-((1 : ℕ) : ℤ)))) ≤
        2 * lam ^ 2 * Real.exp (-lam ^ 2) := by
    have h1 := hnml_k 1 le_rfl (mkB ((1 : ℕ) : ℤ)) (by rw [hmkB_val _ (by omega) (by omega)]; simp)
    have h2 := hnml_k 1 le_rfl (mkB (-((1 : ℕ) : ℤ))) (by rw [hmkB_val _ (by omega) (by omega)]; simp)
    norm_num at h1 h2
    simp only [Nat.cast_one]
    linarith
  -- k ≥ 2 terms: each ≤ 4 * exp(-2 * k * lam^2), sum ≤ exp(-lam^2)!
  have htail_sum :
      (∑ k ∈ Finset.Icc 2 (m + 1),
        (nml (uprob (bucket T lam) (mkB (k : ℤ))) +
         nml (uprob (bucket T lam) (mkB (-(k : ℤ)))))) ≤
        Real.exp (-lam ^ 2) := by
    have hterm : ∀ k ∈ Finset.Icc 2 (m + 1),
        nml (uprob (bucket T lam) (mkB (k : ℤ))) +
        nml (uprob (bucket T lam) (mkB (-(k : ℤ)))) ≤
          4 * (Real.exp (-2 * lam ^ 2)) ^ k := by
      intro k hk
      have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
      have hkm : k ≤ m + 1 := (Finset.mem_Icc.mp hk).2
      have h1 := hnml_k k (by omega) (mkB (k : ℤ)) (by rw [hmkB_val _ (by omega) (by omega)]; exact Int.natAbs_natCast k)
      have h2 := hnml_k k (by omega) (mkB (-(k : ℤ))) (by rw [hmkB_val _ (by omega) (by omega)]; simp)
      have hx_nn : 0 ≤ (2 * (k : ℝ) - 1) ^ 2 * lam ^ 2 := by positivity
      have hxe := x_mul_exp_neg_le hx_nn
      have h4k : 4 * (k : ℝ) ≤ (2 * (k : ℝ) - 1) ^ 2 := by
        have : (2 : ℝ) ≤ k := by exact_mod_cast hk2
        nlinarith
      have hexp_k : Real.exp (-((2 * (k : ℝ) - 1) ^ 2 * lam ^ 2 / 2)) ≤ (Real.exp (-2 * lam ^ 2)) ^ k := by
        rw [← Real.exp_nat_mul]
        apply Real.exp_le_exp.mpr
        nlinarith [sq_nonneg lam]
      linarith
    have hgeom : (∑ k ∈ Finset.Icc 2 (m + 1), 4 * (Real.exp (-2 * lam ^ 2)) ^ k) ≤
        8 * Real.exp (-4 * lam ^ 2) := by
      let r : ℝ := Real.exp (-2 * lam ^ 2)
      have hr_nn : 0 ≤ r := (Real.exp_pos _).le
      have hr_half : r ≤ 1 / 2 := by
        dsimp only [r]
        have h1 : Real.exp (-2 * lam ^ 2) ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by nlinarith)
        have h2 : Real.exp (-1) ≤ 1 / 2 := by
          rw [Real.exp_neg, ← one_div]
          exact one_div_le_one_div_of_le (by norm_num) (by linarith [Real.exp_one_gt_d9])
        exact h1.trans h2
      have hsub : Finset.Icc 2 (m + 1) = (Finset.range m).image (· + 2) := by
        ext k; simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
        exact ⟨fun h => ⟨k - 2, by omega, by omega⟩, fun ⟨j, hj, hjk⟩ => by omega⟩
      rw [hsub, Finset.sum_image (fun _ _ _ _ h => by omega), ← Finset.mul_sum]
      have hpow_sum : (∑ j ∈ Finset.range m, (Real.exp (-2 * lam ^ 2)) ^ (j + 2)) =
          r ^ 2 * ∑ j ∈ Finset.range m, r ^ j := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => by dsimp only [r]; rw [pow_add]; ring
      rw [hpow_sum]
      have hgeom_le : ∑ j ∈ Finset.range m, r ^ j ≤ 2 := by
        have hsum_eq := geom_sum_eq (by linarith : r ≠ 1) m
        rw [hsum_eq, ← neg_div_neg_eq, neg_sub, neg_sub]
        rw [div_le_iff₀ (by linarith)]
        have : 0 ≤ r ^ m := pow_nonneg hr_nn m
        linarith
      have hr2 : r ^ 2 = Real.exp (-4 * lam ^ 2) := by
        dsimp only [r]; rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
      rw [hr2]
      have : 0 ≤ Real.exp (-4 * lam ^ 2) := (Real.exp_pos _).le
      nlinarith
    have h8_le : 8 * Real.exp (-4 * lam ^ 2) ≤ Real.exp (-lam ^ 2) := by
      have he12 : (8 : ℝ) ≤ Real.exp (3 * lam ^ 2) := by
        have h1 : (2 : ℝ) ^ 12 ≤ Real.exp 12 := by
          have he1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
          have : Real.exp 12 = (Real.exp 1) ^ 12 := by rw [← Real.exp_nat_mul]; norm_num
          rw [this]; exact pow_le_pow_left₀ (by norm_num) he1 12
        have h2 : Real.exp 12 ≤ Real.exp (3 * lam ^ 2) := Real.exp_le_exp.mpr (by nlinarith)
        linarith [show (8 : ℝ) ≤ (2 : ℝ) ^ 12 by norm_num]
      have hmul := mul_le_mul_of_nonneg_right he12 (Real.exp_pos (-4 * lam ^ 2)).le
      rw [← Real.exp_add, show 3 * lam ^ 2 + -4 * lam ^ 2 = -lam ^ 2 by ring] at hmul
      exact hmul
    exact (Finset.sum_le_sum hterm).trans (hgeom.trans h8_le)
  linarith

/-- Partial Coloring Lemma: given `n > 10^14`, `U ⊆ Fin n` with `m = |U| > (1/2) √n`, and
`S : Fin n → Finset (Fin n)`, there exists a partial coloring `χ₀ : Fin n → ℝ` supported on `D ⊆ U`
with `25 * (U \ D).card ≤ 4 * m`, `∑ j ∈ U, χ₀ j = 0`, and for every `i : Fin n`:
`|∑ j ∈ S i ∩ U, χ₀ j| ≤ √(9 + (6/5) log (n / m)) * √m`. -/
private lemma partial_coloring_step {n : ℕ} (hn : 10 ^ 14 < n)
    (S : Fin n → Finset (Fin n)) (U : Finset (Fin n))
    (hU_gt : (1 / 2 : ℝ) * Real.sqrt n < U.card) :
    ∃ (D : Finset (Fin n)) (χ₀ : Fin n → ℝ),
      D ⊆ U ∧
      25 * (U \ D).card ≤ 4 * U.card ∧
      (∀ j ∈ D, χ₀ j = 1 ∨ χ₀ j = -1) ∧
      (∀ j ∉ D, χ₀ j = 0) ∧
      ∀ i : Fin n,
        |∑ j ∈ S i ∩ U, χ₀ j| ≤
          Real.sqrt (9 + (6 / 5 : ℝ) * Real.log ((n : ℝ) / (U.card : ℝ))) * Real.sqrt U.card := by
  let m : ℕ := U.card
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hm_big : 5 * 10 ^ 6 ≤ m := by
    have hsqrt_n : (10 ^ 7 : ℝ) < Real.sqrt n := by
      have : ((10 ^ 7 : ℝ)) ^ 2 < n := by
        have : (10 ^ 14 : ℝ) < n := by exact_mod_cast hn
        norm_num at this ⊢; linarith
      calc (10 ^ 7 : ℝ) = Real.sqrt ((10 ^ 7 : ℝ) ^ 2) := (Real.sqrt_sq (by positivity)).symm
        _ < Real.sqrt n := Real.sqrt_lt_sqrt (by positivity) this
    have : (5 * 10 ^ 6 : ℝ) < m := by linarith
    exact_mod_cast this.le
  have hm2 : 2 ≤ m := by omega
  have hm_pos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hm_le_n : (m : ℝ) ≤ n := by
    have : m ≤ n := (Finset.card_le_univ U).trans (by simp)
    exact_mod_cast this
  let R : ℝ := (n : ℝ) / (m : ℝ)
  have hR_ge1 : 1 ≤ R := (one_le_div hm_pos).mpr hm_le_n
  have hlogR_nn : 0 ≤ Real.log R := Real.log_nonneg hR_ge1
  let lam : ℝ := Real.sqrt (9 + (6 / 5 : ℝ) * Real.log R)
  have hlam_sq : lam ^ 2 = 9 + (6 / 5 : ℝ) * Real.log R :=
    Real.sq_sqrt (by linarith)
  have hlam_ge3 : 3 ≤ lam := by
    have : (3 : ℝ) ^ 2 ≤ 9 + (6 / 5 : ℝ) * Real.log R := by linarith
    calc (3 : ℝ) = Real.sqrt ((3 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ lam := Real.sqrt_le_sqrt this
  -- Identify U with Fin m via an equivalence!
  let eU : Fin m ≃ U := (Fintype.equivFinOfCardEq (Fintype.card_coe U)).symm
  -- Complement each S i ∩ U to T i ⊆ Fin m with 2 * (T i).card ≤ m!
  let A_set : Fin n → Finset (Fin m) := fun i =>
    Finset.univ.filter fun r : Fin m => (eU r).1 ∈ S i
  let T : Fin n → Finset (Fin m) := fun i =>
    if 2 * (A_set i).card ≤ m then A_set i else (A_set i)ᶜ
  have hT_card : ∀ i, 2 * (T i).card ≤ m := by
    intro i; dsimp only [T]
    split_ifs with h
    · exact h
    · have hcomp : (A_set i)ᶜ.card = m - (A_set i).card := by
        rw [Finset.card_compl, Fintype.card_fin]
      omega
  -- Define combined bucket map B(x) = (B₀(x), fun i => bucket (T i) lam x)!
  let B0 : (Fin m → Bool) → Fin (m + 1) := fun x =>
    ⟨(Finset.univ.filter fun r : Fin m => x r = true).card,
      Nat.lt_succ_of_le ((Finset.card_le_univ _).trans (by simp))⟩
  let B : (Fin m → Bool) → Fin (m + 1) × (Fin n → Finset.Icc (-(m : ℤ) - 1) (m + 1)) :=
    fun x => (B0 x, fun i => bucket (T i) lam x)
  -- Bound uH B!
  have hH_B : uH B ≤ Real.log ((m : ℝ) + 1) + (n : ℝ) * ((2 * lam ^ 2 + 3) * Real.exp (-lam ^ 2)) := by
    have h1 := uH_prod_le B0 (fun x (i : Fin n) => bucket (T i) lam x)
    have h2 : uH B0 ≤ Real.log ((m : ℝ) + 1) := by
      have := uH_le_log_card B0
      simpa [Fintype.card_fin, Nat.cast_add, Nat.cast_one] using this
    have h3 : uH (fun x (i : Fin n) => bucket (T i) lam x) ≤
        (n : ℝ) * ((2 * lam ^ 2 + 3) * Real.exp (-lam ^ 2)) := by
      calc uH (fun x (i : Fin n) => bucket (T i) lam x)
          ≤ ∑ i : Fin n, uH (bucket (T i) lam) := uH_fin_le n (fun i => bucket (T i) lam)
        _ ≤ ∑ _i : Fin n, ((2 * lam ^ 2 + 3) * Real.exp (-lam ^ 2)) :=
            Finset.sum_le_sum fun i _ => uH_bucket_le hm2 (T i) (hT_card i) (by linarith)
        _ = (n : ℝ) * ((2 * lam ^ 2 + 3) * Real.exp (-lam ^ 2)) := by simp
    linarith
  -- Key numerical comparison: uH B + log 2 < m * (log 2 - binEnt (43/100))!
  let p : ℝ := 43 / 100
  have hgap : uH B + Real.log 2 < m * (Real.log 2 - binEnt p) := by
    have hp_gap : (49 / 5000 : ℝ) * m ≤ m * (Real.log 2 - binEnt p) := by
      have h1 := log_two_sub_binEnt_ge (p := p) (by norm_num) (by norm_num)
      have h2 : (49 / 5000 : ℝ) = 2 * (1 / 2 - p) ^ 2 := by dsimp only [p]; norm_num
      nlinarith
    -- Term 1: log(m+1) + log 2 < (2 / 1000) * m
    have hterm1 : Real.log ((m : ℝ) + 1) + Real.log 2 < (2 / 1000 : ℝ) * m := by
      rw [← Real.log_mul (by positivity) (by norm_num)]
      have h2m2_pos : (0 : ℝ) < (m + 1) * 2 := by positivity
      have hlog_sqrt : Real.log (((m : ℝ) + 1) * 2) ≤ 2 * Real.sqrt (((m : ℝ) + 1) * 2) := by
        have hsq : Real.log (((m : ℝ) + 1) * 2) = 2 * Real.log (Real.sqrt (((m : ℝ) + 1) * 2)) := by
          rw [Real.log_sqrt h2m2_pos.le]; ring
        rw [hsq]
        have := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr h2m2_pos)
        linarith
      have hsq_lt : (2 * Real.sqrt (((m : ℝ) + 1) * 2)) ^ 2 < ((2 / 1000 : ℝ) * m) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt h2m2_pos.le]
        have hmR : (5 * 10 ^ 6 : ℝ) ≤ m := by exact_mod_cast hm_big
        nlinarith
      have hlt : 2 * Real.sqrt (((m : ℝ) + 1) * 2) < (2 / 1000 : ℝ) * m := by
        nlinarith [sq_nonneg (2 * Real.sqrt (((m : ℝ) + 1) * 2) - (2 / 1000 : ℝ) * m),
          Real.sqrt_nonneg (((m : ℝ) + 1) * 2)]
      linarith
    -- Term 2: n * (2*lam^2 + 3) * exp(-lam^2) ≤ 21 * exp(-9) * m < (3 / 1000) * m
    have hterm2 : (n : ℝ) * ((2 * lam ^ 2 + 3) * Real.exp (-lam ^ 2)) < (3 / 1000 : ℝ) * m := by
      have hn_eq : (n : ℝ) = R * m := by dsimp only [R]; field_simp [hm_pos.ne']
      rw [hn_eq, hlam_sq]
      have hR_exp : R * Real.exp (-(9 + (6 / 5 : ℝ) * Real.log R)) =
          Real.exp (-9) * Real.exp (-((1 / 5 : ℝ) * Real.log R)) := by
        have hR_pos : 0 < R := by linarith
        calc R * Real.exp (-(9 + (6 / 5 : ℝ) * Real.log R))
            = Real.exp (Real.log R) * Real.exp (-(9 + (6 / 5 : ℝ) * Real.log R)) := by
                rw [Real.exp_log hR_pos]
          _ = Real.exp (Real.log R + -(9 + (6 / 5 : ℝ) * Real.log R)) := (Real.exp_add _ _).symm
          _ = Real.exp (-9 + -((1 / 5 : ℝ) * Real.log R)) := by congr 1; ring
          _ = Real.exp (-9) * Real.exp (-((1 / 5 : ℝ) * Real.log R)) := Real.exp_add _ _
      have hlin : (2 * (9 + (6 / 5 : ℝ) * Real.log R) + 3) * Real.exp (-((1 / 5 : ℝ) * Real.log R)) ≤ 21 := by
        have h1 : 1 + (1 / 5 : ℝ) * Real.log R ≤ Real.exp ((1 / 5 : ℝ) * Real.log R) := by
          linarith [Real.add_one_le_exp ((1 / 5 : ℝ) * Real.log R)]
        have h2 : 2 * (9 + (6 / 5 : ℝ) * Real.log R) + 3 ≤ 21 * (1 + (1 / 5 : ℝ) * Real.log R) := by
          linarith
        have h3 : 2 * (9 + (6 / 5 : ℝ) * Real.log R) + 3 ≤ 21 * Real.exp ((1 / 5 : ℝ) * Real.log R) := by
          linarith
        have hmul := mul_le_mul_of_nonneg_right h3 (Real.exp_pos (-((1 / 5 : ℝ) * Real.log R))).le
        rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one] at hmul
        exact hmul
      have h21 : 21 * Real.exp (-9) < (3 / 1000 : ℝ) := by
        have he1 : (27 / 10 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
        have he9 : (27 / 10 : ℝ) ^ 9 < Real.exp 9 := by
          have : Real.exp 9 = (Real.exp 1) ^ 9 := by rw [← Real.exp_nat_mul]; norm_num
          rw [this]; exact pow_lt_pow_left₀ he1 (by norm_num) (by norm_num)
        have hnum : (7000 : ℝ) < (27 / 10 : ℝ) ^ 9 := by norm_num
        rw [Real.exp_neg, ← div_eq_mul_inv, div_lt_iff₀ (Real.exp_pos 9)]
        linarith
      calc R * m * ((2 * (9 + (6 / 5 : ℝ) * Real.log R) + 3) * Real.exp (-(9 + (6 / 5 : ℝ) * Real.log R)))
          = m * (Real.exp (-9) * ((2 * (9 + (6 / 5 : ℝ) * Real.log R) + 3) *
              Real.exp (-((1 / 5 : ℝ) * Real.log R)))) := by
              rw [show R * m * ((2 * (9 + (6 / 5 : ℝ) * Real.log R) + 3) *
                  Real.exp (-(9 + (6 / 5 : ℝ) * Real.log R))) =
                m * ((2 * (9 + (6 / 5 : ℝ) * Real.log R) + 3) *
                  (R * Real.exp (-(9 + (6 / 5 : ℝ) * Real.log R)))) by ring]
              rw [hR_exp]; ring
        _ ≤ m * (Real.exp (-9) * 21) := by
              exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlin (Real.exp_pos _).le) hm_pos.le
        _ < (3 / 1000 : ℝ) * m := by nlinarith
    linarith
  -- Find a large fiber C = B⁻¹(b) with |C| > 2 * ∑_{k ≤ t} C(m, k)!
  obtain ⟨b_star, hb_card⟩ := exists_fiber_large B
  let C : Finset (Fin m → Bool) := Finset.univ.filter fun x => B x = b_star
  let t : ℕ := (43 * m) / 100
  have ht_le : (t : ℝ) ≤ p * m := by
    dsimp only [t, p]
    have : (100 * ((43 * m) / 100) : ℕ) ≤ 43 * m := Nat.mul_div_le (43 * m) 100
    have hR : (100 : ℝ) * ((43 * m / 100 : ℕ) : ℝ) ≤ 43 * m := by exact_mod_cast this
    linarith
  have hC_gt : 2 * ∑ k ∈ Finset.range (t + 1), m.choose k < C.card := by
    have hR : ((2 * ∑ k ∈ Finset.range (t + 1), m.choose k : ℕ) : ℝ) < (C.card : ℝ) := by
      have h1 := sum_choose_le_exp_binEnt (m := m) (t := t) (p := p) (by norm_num) (by norm_num) ht_le
      have h2 : (2 : ℝ) * Real.exp (m * binEnt p) < (2 : ℝ) ^ m * Real.exp (-uH B) := by
        have hL : (2 : ℝ) * Real.exp (m * binEnt p) = Real.exp (Real.log 2 + m * binEnt p) := by
          rw [Real.exp_add, Real.exp_log (by norm_num)]
        have hR : (2 : ℝ) ^ m * Real.exp (-uH B) = Real.exp (m * Real.log 2 + -uH B) := by
          rw [Real.exp_add, mul_comm (m : ℝ), Real.exp_mul, Real.exp_log (by norm_num),
            Real.rpow_natCast]
        rw [hL, hR]
        exact Real.exp_lt_exp.mpr (by linarith)
      have hb_C : (2 : ℝ) ^ m * Real.exp (-uH B) ≤ (C.card : ℝ) :=
        hb_card.trans_eq (by
          congr 1
          exact congrArg Finset.card (by ext x; simp only [C, Finset.mem_filter]))
      rw [Nat.cast_mul, Nat.cast_ofNat]
      linarith [h1, h2, hb_C]
    exact_mod_cast hR
  -- By CLP diameter bound, ∃ x, y ∈ C with Hamming distance > 2t!
  have hex_pair : ∃ x ∈ C, ∃ y ∈ C, 2 * t < (Finset.univ.filter fun r : Fin m => x r ≠ y r).card := by
    by_contra hno
    push Not at hno
    have hle := clp_diameter_bound C hno
    omega
  obtain ⟨x, hxC, y, hyC, hdist⟩ := hex_pair
  have hBx : B x = b_star := (Finset.mem_filter.mp hxC).2
  have hBy : B y = b_star := (Finset.mem_filter.mp hyC).2
  have hBxy : B x = B y := hBx.trans hBy.symm
  -- Build D ⊆ U and χ₀ : Fin n → ℝ from (x, y)!
  let diffR : Finset (Fin m) := Finset.univ.filter fun r : Fin m => x r ≠ y r
  let D : Finset (Fin n) := diffR.image fun r => (eU r).1
  have hD_sub : D ⊆ U := by
    intro j hj
    rcases Finset.mem_image.mp hj with ⟨r, _, rfl⟩
    exact (eU r).2
  have hD_card : D.card = diffR.card := by
    refine Finset.card_image_of_injective _ fun r₁ r₂ h => eU.injective (Subtype.ext h)
  have hrem : 25 * (U \ D).card ≤ 4 * m := by
    rw [Finset.card_sdiff_of_subset hD_sub, hD_card]
    have h100t : 43 * m - 99 ≤ 100 * t := by dsimp only [t]; omega
    have hdist' : 2 * t + 1 ≤ diffR.card := hdist
    omega
  let χ₀ : Fin n → ℝ := fun j =>
    if hj : j ∈ U then (sign (x (eU.symm ⟨j, hj⟩)) - sign (y (eU.symm ⟨j, hj⟩))) / 2 else 0
  have hχ_D : ∀ j ∈ D, χ₀ j = 1 ∨ χ₀ j = -1 := by
    intro j hj
    rcases Finset.mem_image.mp hj with ⟨r, hr, rfl⟩
    have hne : x r ≠ y r := (Finset.mem_filter.mp hr).2
    dsimp only [χ₀]
    rw [dif_pos (eU r).2]
    have hsymm : eU.symm ⟨(eU r).1, (eU r).2⟩ = r := eU.symm_apply_apply r
    rw [hsymm]
    unfold sign
    cases hx : x r <;> cases hy : y r
    · exact absurd (hx.trans hy.symm) hne
    · right; norm_num
    · left; norm_num
    · exact absurd (hx.trans hy.symm) hne
  have hχ_notD : ∀ j ∉ D, χ₀ j = 0 := by
    intro j hj
    dsimp only [χ₀]
    split_ifs with hjU
    · have heq : x (eU.symm ⟨j, hjU⟩) = y (eU.symm ⟨j, hjU⟩) := by
        by_contra hne
        apply hj
        refine Finset.mem_image.mpr ⟨eU.symm ⟨j, hjU⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩, ?_⟩
        simp
      rw [heq]; ring
    · rfl
  -- Balance property: ∑ r : Fin m, (sign (x r) - sign (y r)) = 0!
  have hbal : (∑ r : Fin m, (sign (x r) - sign (y r))) = 0 := by
    have hB0 : B0 x = B0 y := congrArg Prod.fst hBxy
    have hcnt : (Finset.univ.filter fun r : Fin m => x r = true).card =
        (Finset.univ.filter fun r : Fin m => y r = true).card := congrArg Fin.val hB0
    have hsign_sum : ∀ z : Fin m → Bool,
        (∑ r : Fin m, sign (z r)) = 2 * ((Finset.univ.filter fun r => z r = true).card : ℝ) - m := by
      intro z
      have h1 : ∀ r : Fin m, sign (z r) = (if z r = true then (2 : ℝ) else 0) - 1 := by
        intro r; unfold sign; cases z r <;> norm_num
      simp_rw [h1, Finset.sum_sub_distrib, Finset.sum_ite, Finset.sum_const_zero, add_zero,
        Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
      ring
    rw [Finset.sum_sub_distrib, hsign_sum x, hsign_sum y, hcnt]; ring
  -- Discrepancy bound for every i : Fin n!
  refine ⟨D, χ₀, hD_sub, hrem, hχ_D, hχ_notD, fun i => ?_⟩
  have hBi : bucket (T i) lam x = bucket (T i) lam y := congrFun (congrArg Prod.snd hBxy) i
  have hT_disc : |(∑ r ∈ T i, (sign (x r) - sign (y r))) / 2| ≤ lam * Real.sqrt m := by
    have hfl : ⌊((∑ r ∈ T i, sign (x r)) + lam * Real.sqrt m) / (2 * lam * Real.sqrt m)⌋ =
        ⌊((∑ r ∈ T i, sign (y r)) + lam * Real.sqrt m) / (2 * lam * Real.sqrt m)⌋ := by
      rw [← bucket_val_eq (by omega) (T i) (by linarith) x,
          ← bucket_val_eq (by omega) (T i) (by linarith) y, hBi]
    have hden_pos : 0 < 2 * lam * Real.sqrt m := by positivity
    set fx := ((∑ r ∈ T i, sign (x r)) + lam * Real.sqrt m) / (2 * lam * Real.sqrt m)
    set fy := ((∑ r ∈ T i, sign (y r)) + lam * Real.sqrt m) / (2 * lam * Real.sqrt m)
    have hx1 : (⌊fx⌋ : ℝ) ≤ fx := Int.floor_le fx
    have hx2 : fx < (⌊fx⌋ : ℝ) + 1 := Int.lt_floor_add_one fx
    have hy1 : (⌊fy⌋ : ℝ) ≤ fy := Int.floor_le fy
    have hy2 : fy < (⌊fy⌋ : ℝ) + 1 := Int.lt_floor_add_one fy
    rw [hfl] at hx1 hx2
    have hdiff : |fx - fy| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
    have hdiff_eq : fx - fy = (∑ r ∈ T i, (sign (x r) - sign (y r))) / (2 * lam * Real.sqrt m) := by
      dsimp only [fx, fy]; rw [Finset.sum_sub_distrib]; ring
    rw [hdiff_eq, abs_div, abs_of_pos hden_pos, div_le_one hden_pos] at hdiff
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  -- Relate ∑ j ∈ S i ∩ U, χ₀ j to ± (∑ r ∈ T i, (sign(x r) - sign(y r))) / 2!
  have hsum_A : (∑ j ∈ S i ∩ U, χ₀ j) = (∑ r ∈ A_set i, (sign (x r) - sign (y r))) / 2 := by
    rw [Finset.sum_div]
    refine Finset.sum_bij (fun j hj => eU.symm ⟨j, (Finset.mem_inter.mp hj).2⟩) ?_ ?_ ?_ ?_
    · intro j hj
      have hj' := Finset.mem_inter.mp hj
      simp only [A_set, Finset.mem_filter, Finset.mem_univ, true_and, Equiv.apply_symm_apply]
      exact hj'.1
    · intro j₁ hj₁ j₂ hj₂ h
      have := congrArg (fun r => (eU r).1) h
      simpa using this
    · intro r hr
      have hrS : (eU r).1 ∈ S i := (Finset.mem_filter.mp hr).2
      refine ⟨(eU r).1, Finset.mem_inter.mpr ⟨hrS, (eU r).2⟩, eU.symm_apply_apply r⟩
    · intro j hj
      have hjU : j ∈ U := (Finset.mem_inter.mp hj).2
      dsimp only [χ₀]; rw [dif_pos hjU]
  rw [hsum_A]
  have hAT : |(∑ r ∈ A_set i, (sign (x r) - sign (y r))) / 2| =
      |(∑ r ∈ T i, (sign (x r) - sign (y r))) / 2| := by
    dsimp only [T]
    split_ifs with h
    · rfl
    · have hadd := Finset.sum_add_sum_compl (A_set i) (fun r => sign (x r) - sign (y r))
      rw [hbal] at hadd
      have hneg : (∑ r ∈ A_set i, (sign (x r) - sign (y r))) / 2 =
          -((∑ r ∈ (A_set i)ᶜ, (sign (x r) - sign (y r))) / 2) := by linarith
      rw [hneg, abs_neg]
  rw [hAT]
  exact hT_disc

/- ## Section 6: Monotonicity of `λ(m) √m`, telescoping induction, and final theorem -/

private lemma disc_bound_mono {n : ℕ} {m₁ m₂ : ℝ} (hn : 0 < (n : ℝ))
    (hm1 : 0 < m₁) (h12 : m₁ ≤ m₂) (hm2 : m₂ ≤ n) :
    Real.sqrt (9 + (6 / 5 : ℝ) * Real.log (n / m₁)) * Real.sqrt m₁ ≤
      Real.sqrt (9 + (6 / 5 : ℝ) * Real.log (n / m₂)) * Real.sqrt m₂ := by
  have hnn1 : 0 ≤ 9 + (6 / 5 : ℝ) * Real.log (n / m₁) := by
    have : 0 ≤ Real.log (n / m₁) := Real.log_nonneg ((one_le_div hm1).mpr (h12.trans hm2))
    linarith
  have hnn2 : 0 ≤ 9 + (6 / 5 : ℝ) * Real.log (n / m₂) := by
    have : 0 ≤ Real.log (n / m₂) := Real.log_nonneg ((one_le_div (lt_of_lt_of_le hm1 h12)).mpr hm2)
    linarith
  rw [← Real.sqrt_mul hnn1, ← Real.sqrt_mul hnn2]
  apply Real.sqrt_le_sqrt
  -- Show g(x) = x * (9 + (6/5) * log(n / x)) is increasing on [m₁, m₂]!
  have hd_at : ∀ x ∈ Set.Ioo m₁ m₂,
      HasDerivAt (fun t : ℝ => t * (9 + (6 / 5 : ℝ) * (Real.log n - Real.log t)))
        (1 * (9 + (6 / 5 : ℝ) * (Real.log n - Real.log x)) + x * (-(6 / 5 : ℝ) * x⁻¹)) x := by
    intro x hx
    have hx_pos : 0 < x := lt_of_lt_of_le hm1 hx.1.le
    have hd1 : HasDerivAt (fun t : ℝ => 9 + (6 / 5 : ℝ) * (Real.log n - Real.log t))
        (-(6 / 5 : ℝ) * x⁻¹) x := by
      have hsub := (Real.hasDerivAt_log hx_pos.ne').const_sub (Real.log n)
      have h2 := (hsub.const_mul (6 / 5 : ℝ)).const_add (9 : ℝ)
      have heq : (6 / 5 : ℝ) * -x⁻¹ = -(6 / 5 : ℝ) * x⁻¹ := by ring
      exact heq ▸ h2
    exact (hasDerivAt_id' x).mul hd1
  have hmono : MonotoneOn (fun x : ℝ => x * (9 + (6 / 5 : ℝ) * (Real.log n - Real.log x)))
      (Set.Icc m₁ m₂) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc m₁ m₂)
    · intro x hx
      have hx_pos : 0 < x := lt_of_lt_of_le hm1 hx.1
      exact (continuousAt_id.mul (continuousAt_const.add
        (continuousAt_const.mul (continuousAt_const.sub (Real.continuousAt_log hx_pos.ne'))))).continuousWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      exact (hd_at x hx).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have hx_pos : 0 < x := lt_of_lt_of_le hm1 hx.1.le
      rw [(hd_at x hx).deriv]
      have hheq : 1 * (9 + (6 / 5 : ℝ) * (Real.log n - Real.log x)) + x * (-(6 / 5 : ℝ) * x⁻¹) =
          39 / 5 + (6 / 5 : ℝ) * (Real.log n - Real.log x) := by
        have : x * (-(6 / 5 : ℝ) * x⁻¹) = -(6 / 5 : ℝ) := by field_simp [hx_pos.ne']
        linarith
      rw [hheq]
      have hlog : Real.log x ≤ Real.log n := Real.log_le_log hx_pos (hx.2.le.trans hm2)
      linarith
  have hle := hmono ⟨le_rfl, h12⟩ ⟨h12, le_rfl⟩ h12
  rw [Real.log_div hn.ne' hm1.ne', Real.log_div hn.ne' (lt_of_lt_of_le hm1 h12).ne']
  linarith

private noncomputable def phi (r : ℕ) : ℝ :=
  (2 / 5 : ℝ) ^ r * (5 + 4 / 9 + (2 / 3 : ℝ) * r)

private lemma phi_nonneg (r : ℕ) : 0 ≤ phi r := by
  unfold phi; positivity

private lemma phi_telescope (r : ℕ) :
    phi r - phi (r + 1) = (2 / 5 : ℝ) ^ r * (3 + (2 / 5 : ℝ) * r) := by
  unfold phi
  rw [pow_succ, Nat.cast_add, Nat.cast_one]
  ring

private lemma spencer_large_ind {n : ℕ} (hn : 10 ^ 14 < n) (S : Fin n → Finset (Fin n)) :
    ∀ (M : ℕ) (r : ℕ) (U : Finset (Fin n)),
      U.card ≤ M →
      (U.card : ℝ) ≤ (4 / 25 : ℝ) ^ r * n →
      ∃ χ : Fin n → ℝ,
        (∀ j ∈ U, χ j = 1 ∨ χ j = -1) ∧
        (∀ j ∉ U, χ j = 0) ∧
        ∀ i : Fin n, |∑ j ∈ S i ∩ U, χ j| ≤ (phi r + 1 / 2) * Real.sqrt n
  | 0, r, U, hUM, _ => by
      have hU0 : U = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hUM)
      refine ⟨fun _ => 0, fun j hj => absurd hj (by simp [hU0]), fun _ _ => rfl, fun i => ?_⟩
      simp only [hU0, Finset.inter_empty, Finset.sum_empty, abs_zero]
      exact mul_nonneg (by linarith [phi_nonneg r]) (Real.sqrt_nonneg _)
  | M + 1, r, U, hUM, hUr => by
      by_cases hsmall : (U.card : ℝ) ≤ (1 / 2 : ℝ) * Real.sqrt n
      · refine ⟨fun j => if j ∈ U then 1 else 0,
          fun j hj => Or.inl (if_pos hj),
          fun j hj => if_neg hj,
          fun i => ?_⟩
        have hsum : (∑ j ∈ S i ∩ U, if j ∈ U then (1 : ℝ) else 0) = ((S i ∩ U).card : ℝ) := by
          have : ∀ j ∈ S i ∩ U, (if j ∈ U then (1 : ℝ) else 0) = 1 :=
            fun j hj => if_pos (Finset.mem_inter.mp hj).2
          rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul, mul_one]
        rw [hsum, abs_of_nonneg (Nat.cast_nonneg _)]
        have hsub : ((S i ∩ U).card : ℝ) ≤ U.card :=
          Nat.cast_le.mpr (Finset.card_le_card Finset.inter_subset_right)
        have hphi := phi_nonneg r
        have hsq := Real.sqrt_nonneg (n : ℝ)
        nlinarith
      · push Not at hsmall
        obtain ⟨D, χ₀, hDU, hrem, hχ₀_D, hχ₀_notD, hχ₀_disc⟩ :=
          partial_coloring_step hn S U hsmall
        let U' : Finset (Fin n) := U \ D
        have hU'_lt : U'.card < U.card := by
          have hUpos : 0 < U.card := by
            have : (0 : ℝ) < U.card := lt_of_le_of_lt (by positivity) hsmall
            exact_mod_cast this
          dsimp only [U']; omega
        have hU'_le_M : U'.card ≤ M := by omega
        have hU'_bound : (U'.card : ℝ) ≤ (4 / 25 : ℝ) ^ (r + 1) * n := by
          have h1 : (U'.card : ℝ) ≤ (4 / 25 : ℝ) * U.card := by
            have : (25 : ℝ) * (U'.card : ℝ) ≤ 4 * (U.card : ℝ) := by exact_mod_cast hrem
            linarith
          rw [pow_succ']; nlinarith
        obtain ⟨χ₁, hχ₁_U', hχ₁_notU', hχ₁_disc⟩ :=
          spencer_large_ind hn S M (r + 1) U' hU'_le_M hU'_bound
        -- Combine χ = χ₀ + χ₁ (disjoint supports D and U' = U \ D)!
        refine ⟨fun j => χ₀ j + χ₁ j, ?_, ?_, fun i => ?_⟩
        · intro j hj
          dsimp only
          by_cases hjD : j ∈ D
          · have hjU' : j ∉ U' := by simp [U', hjD]
            rw [hχ₁_notU' j hjU', add_zero]; exact hχ₀_D j hjD
          · have hjU' : j ∈ U' := Finset.mem_sdiff.mpr ⟨hj, hjD⟩
            rw [hχ₀_notD j hjD, zero_add]; exact hχ₁_U' j hjU'
        · intro j hj
          dsimp only
          have hjD : j ∉ D := fun h => hj (hDU h)
          have hjU' : j ∉ U' := fun h => hj (Finset.mem_sdiff.mp h).1
          rw [hχ₀_notD j hjD, hχ₁_notU' j hjU', add_zero]
        · -- Step discrepancy bound!
          have hn_pos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
          have hm_pos : (0 : ℝ) < U.card := lt_of_le_of_lt (by positivity) hsmall
          have hm2_le : (4 / 25 : ℝ) ^ r * n ≤ n := by
            have : (4 / 25 : ℝ) ^ r ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
            nlinarith
          have hstep_le :
              Real.sqrt (9 + (6 / 5 : ℝ) * Real.log ((n : ℝ) / (U.card : ℝ))) * Real.sqrt U.card ≤
                (phi r - phi (r + 1)) * Real.sqrt n := by
            have h1 := disc_bound_mono hn_pos hm_pos hUr hm2_le
            have hdiv : (n : ℝ) / ((4 / 25 : ℝ) ^ r * n) = (25 / 4 : ℝ) ^ r := by
              field_simp [hn_pos.ne']; rw [← mul_pow]; norm_num
            have hsqrt_m2 : Real.sqrt ((4 / 25 : ℝ) ^ r * n) = (2 / 5 : ℝ) ^ r * Real.sqrt n := by
              rw [Real.sqrt_mul (by positivity)]
              congr 1
              have h425 : (4 / 25 : ℝ) ^ r = ((2 / 5 : ℝ) ^ r) ^ 2 := by
                rw [← pow_mul, mul_comm, pow_mul]; norm_num
              rw [h425, Real.sqrt_sq (by positivity)]
            have hlog25 : Real.log (25 / 4 : ℝ) < 2 := by
              rw [Real.log_lt_iff_lt_exp (by norm_num)]
              have he1 : (27 / 10 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
              have he2 : (27 / 10 : ℝ) ^ 2 < Real.exp 2 := by
                have : Real.exp 2 = (Real.exp 1) ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
                rw [this]; exact pow_lt_pow_left₀ he1 (by norm_num) (by norm_num)
              linarith [show (25 / 4 : ℝ) < (27 / 10 : ℝ) ^ 2 by norm_num]
            have hsqrt_lam :
                Real.sqrt (9 + (6 / 5 : ℝ) * Real.log ((25 / 4 : ℝ) ^ r)) ≤ 3 + (2 / 5 : ℝ) * r := by
              rw [Real.log_pow]
              have hsq : 9 + (6 / 5 : ℝ) * ((r : ℝ) * Real.log (25 / 4 : ℝ)) ≤
                  (3 + (2 / 5 : ℝ) * r) ^ 2 := by
                have hr_nn : (0 : ℝ) ≤ r := Nat.cast_nonneg r
                nlinarith
              calc Real.sqrt (9 + (6 / 5 : ℝ) * ((r : ℝ) * Real.log (25 / 4 : ℝ)))
                  ≤ Real.sqrt ((3 + (2 / 5 : ℝ) * r) ^ 2) := Real.sqrt_le_sqrt hsq
                _ = 3 + (2 / 5 : ℝ) * r := Real.sqrt_sq (by positivity)
            rw [hdiv, hsqrt_m2] at h1
            rw [phi_telescope]
            have hmul := mul_le_mul_of_nonneg_right hsqrt_lam
              (mul_nonneg (by positivity : 0 ≤ (2 / 5 : ℝ) ^ r) (Real.sqrt_nonneg (n : ℝ)))
            linarith
          have hsum_split : (∑ j ∈ S i ∩ U, (χ₀ j + χ₁ j)) =
              (∑ j ∈ S i ∩ U, χ₀ j) + (∑ j ∈ S i ∩ U', χ₁ j) := by
            rw [Finset.sum_add_distrib]
            congr 1
            have hsub : S i ∩ U' ⊆ S i ∩ U :=
              Finset.inter_subset_inter_left Finset.sdiff_subset
            symm
            refine Finset.sum_subset hsub fun j hj hnj => hχ₁_notU' j fun hju =>
              hnj (Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hj).1, hju⟩)
          rw [hsum_split]
          calc |(∑ j ∈ S i ∩ U, χ₀ j) + (∑ j ∈ S i ∩ U', χ₁ j)|
              ≤ |∑ j ∈ S i ∩ U, χ₀ j| + |∑ j ∈ S i ∩ U', χ₁ j| := abs_add_le _ _
            _ ≤ (phi r - phi (r + 1)) * Real.sqrt n + (phi (r + 1) + 1 / 2) * Real.sqrt n :=
                add_le_add ((hχ₀_disc i).trans hstep_le) (hχ₁_disc i)
            _ = (phi r + 1 / 2) * Real.sqrt n := by ring

theorem six_standard_deviations_proof :
    ∀ (n : ℕ) (S : Fin n → Finset (Fin n)),
      ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
        ∀ i, |∑ j ∈ S i, χ j| ≤ 6 * Real.sqrt n := by
  intro n S
  by_cases h1 : n ≤ 36
  · exact spencer_le_36 h1 S
  · by_cases h2 : n ≤ 10 ^ 14
    · exact spencer_mid (by omega) h2 S
    · push Not at h2
      obtain ⟨χ, hχ_pm, _, hχ_disc⟩ := spencer_large_ind h2 S n 0 Finset.univ
        (by simp) (by simp)
      refine ⟨χ, fun j => hχ_pm j (Finset.mem_univ j), fun i => ?_⟩
      have hi := hχ_disc i
      simp only [Finset.inter_univ] at hi
      have hphi0 : phi 0 + 1 / 2 ≤ 6 := by unfold phi; norm_num
      exact hi.trans (mul_le_mul_of_nonneg_right hphi0 (Real.sqrt_nonneg _))

end OMA.Spencer

theorem OMA.solution : type_of% @SixStandardDeviations.six_standard_deviations :=
  OMA.Spencer.six_standard_deviations_proof
