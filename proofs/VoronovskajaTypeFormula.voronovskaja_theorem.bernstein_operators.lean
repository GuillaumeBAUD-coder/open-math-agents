import FormalConjectures.Paper.VoronovskajaTypeFormula

/-!
# Classical Voronovskaja Theorem for Bernstein Operators

Proof of the classical Voronovskaja asymptotic formula (`α = 1`) for the Bézier--Bernstein
operators on `C^2` functions on `[0, 1]`.
-/

-- Problem: Voronovskaja-type Formula for the Bezier Variant of the Bernstein Operators
-- Upstream: formal-conjectures FormalConjectures/Paper/VoronovskajaTypeFormula.lean:448 (declaration VoronovskajaTypeFormula.voronovskaja_theorem.bernstein_operators)
-- Credit: @TheWaler (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Topology Filter unitInterval

private noncomputable def bernWeight (n k : ℕ) (x : ℝ) : ℝ :=
  (n.choose k : ℝ) * x ^ k * (1 - x) ^ (n - k)

private lemma bernWeight_nonneg {n k : ℕ} {x : ℝ} (hx : x ∈ I) : 0 ≤ bernWeight n k x := by
  rcases hx with ⟨hx0, hx1⟩
  unfold bernWeight
  have h1 : 0 ≤ 1 - x := sub_nonneg.mpr hx1
  positivity

private lemma bezierBernstein_one_eq (n : ℕ) (f : ℝ → ℝ) (x : ℝ) :
    VoronovskajaTypeFormula.bezierBernstein n 1 f x =
      ∑ k ∈ Finset.range (n + 1), f ((k : ℝ) / n) * bernWeight n k x := by
  unfold VoronovskajaTypeFormula.bezierBernstein
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  rw [Real.rpow_one, Real.rpow_one,
    VoronovskajaTypeFormula.bernsteinTail_eval_eq_binomial_tail,
    VoronovskajaTypeFormula.bernsteinTail_eval_eq_binomial_tail,
    ← Finset.insert_Icc_add_one_left_eq_Icc hkn, Finset.sum_insert]
  · unfold bernWeight
    ring
  · simp

private lemma bernWeight_sum_one (n : ℕ) (x : ℝ) :
    ∑ k ∈ Finset.range (n + 1), bernWeight n k x = 1 := by
  have h := congrArg (Polynomial.eval x) (bernsteinPolynomial.sum ℝ n)
  simpa [bernWeight, Polynomial.eval_finsetSum, bernsteinPolynomial] using h

private lemma bernWeight_shift (n : ℕ) (x : ℝ) (g : ℕ → ℝ) :
    (∑ k ∈ Finset.range (n + 2), (k : ℝ) * g k * bernWeight (n + 1) k x) =
      ((n + 1 : ℕ) : ℝ) * x * ∑ j ∈ Finset.range (n + 1), g (j + 1) * bernWeight n j x := by
  rw [Finset.sum_range_succ', Nat.cast_zero, zero_mul, zero_mul, add_zero, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold bernWeight
  have hch : (((n + 1).choose (j + 1) : ℕ) : ℝ) * ((j + 1 : ℕ) : ℝ) =
      ((n + 1 : ℕ) : ℝ) * ((n.choose j : ℕ) : ℝ) := by
    exact_mod_cast (Nat.add_one_mul_choose_eq n j).symm
  rw [Nat.succ_sub_succ_eq_sub, pow_succ]
  calc ((j + 1 : ℕ) : ℝ) * g (j + 1) *
        (((n + 1).choose (j + 1) : ℝ) * (x ^ j * x) * (1 - x) ^ (n - j))
      = g (j + 1) * ((((n + 1).choose (j + 1) : ℝ) * ((j + 1 : ℕ) : ℝ)) *
          (x ^ j * x * (1 - x) ^ (n - j))) := by ring
    _ = g (j + 1) * ((((n + 1 : ℕ) : ℝ) * (n.choose j : ℝ)) *
          (x ^ j * x * (1 - x) ^ (n - j))) := by rw [hch]
    _ = ((n + 1 : ℕ) : ℝ) * x *
          (g (j + 1) * ((n.choose j : ℝ) * x ^ j * (1 - x) ^ (n - j))) := by ring

private lemma bernWeight_ff1 (n : ℕ) (x : ℝ) :
    ∑ k ∈ Finset.range (n + 1), (k : ℝ) * bernWeight n k x = (n : ℝ) * x := by
  cases n with
  | zero => simp
  | succ n =>
    have h := bernWeight_shift n x (fun _ => 1)
    simp only [mul_one, one_mul, bernWeight_sum_one] at h
    exact h

private lemma bernWeight_ff2 (n : ℕ) (x : ℝ) :
    ∑ k ∈ Finset.range (n + 1), (k : ℝ) * ((k : ℝ) - 1) * bernWeight n k x =
      (n : ℝ) * ((n : ℝ) - 1) * x ^ 2 := by
  cases n with
  | zero => simp
  | succ n =>
    have h := bernWeight_shift n x (fun k => (k : ℝ) - 1)
    have hsimp : (∑ j ∈ Finset.range (n + 1), (((j + 1 : ℕ) : ℝ) - 1) * bernWeight n j x) =
        (n : ℝ) * x := by
      simpa [Nat.cast_add, Nat.cast_one] using bernWeight_ff1 n x
    rw [hsimp] at h
    rw [h]
    push_cast
    ring

private lemma bernWeight_ff3 (n : ℕ) (x : ℝ) :
    ∑ k ∈ Finset.range (n + 1), (k : ℝ) * ((k : ℝ) - 1) * ((k : ℝ) - 2) * bernWeight n k x =
      (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) * x ^ 3 := by
  cases n with
  | zero => simp
  | succ n =>
    have h := bernWeight_shift n x (fun k => ((k : ℝ) - 1) * ((k : ℝ) - 2))
    have hsimp : (∑ j ∈ Finset.range (n + 1),
        ((((j + 1 : ℕ) : ℝ) - 1) * (((j + 1 : ℕ) : ℝ) - 2)) * bernWeight n j x) =
        (n : ℝ) * ((n : ℝ) - 1) * x ^ 2 := by
      convert bernWeight_ff2 n x using 2 with j
      push_cast
      ring
    rw [hsimp] at h
    calc (∑ k ∈ Finset.range (n + 2),
            (k : ℝ) * ((k : ℝ) - 1) * ((k : ℝ) - 2) * bernWeight (n + 1) k x)
        = ∑ k ∈ Finset.range (n + 2),
            (k : ℝ) * (((k : ℝ) - 1) * ((k : ℝ) - 2)) * bernWeight (n + 1) k x := by
          refine Finset.sum_congr rfl fun k _ => by ring
      _ = ((n + 1 : ℕ) : ℝ) * x * ((n : ℝ) * ((n : ℝ) - 1) * x ^ 2) := h
      _ = ((n + 1 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ) - 1) * (((n + 1 : ℕ) : ℝ) - 2) * x ^ 3 := by
          push_cast
          ring

private lemma bernWeight_ff4 (n : ℕ) (x : ℝ) :
    ∑ k ∈ Finset.range (n + 1),
        (k : ℝ) * ((k : ℝ) - 1) * ((k : ℝ) - 2) * ((k : ℝ) - 3) * bernWeight n k x =
      (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) * ((n : ℝ) - 3) * x ^ 4 := by
  cases n with
  | zero => simp
  | succ n =>
    have h := bernWeight_shift n x (fun k => ((k : ℝ) - 1) * ((k : ℝ) - 2) * ((k : ℝ) - 3))
    have hsimp : (∑ j ∈ Finset.range (n + 1),
        ((((j + 1 : ℕ) : ℝ) - 1) * (((j + 1 : ℕ) : ℝ) - 2) * (((j + 1 : ℕ) : ℝ) - 3)) *
          bernWeight n j x) =
        (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) * x ^ 3 := by
      convert bernWeight_ff3 n x using 2 with j
      push_cast
      ring
    rw [hsimp] at h
    calc (∑ k ∈ Finset.range (n + 2),
            (k : ℝ) * ((k : ℝ) - 1) * ((k : ℝ) - 2) * ((k : ℝ) - 3) * bernWeight (n + 1) k x)
        = ∑ k ∈ Finset.range (n + 2),
            (k : ℝ) * (((k : ℝ) - 1) * ((k : ℝ) - 2) * ((k : ℝ) - 3)) * bernWeight (n + 1) k x := by
          refine Finset.sum_congr rfl fun k _ => by ring
      _ = ((n + 1 : ℕ) : ℝ) * x * ((n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) * x ^ 3) := h
      _ = ((n + 1 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ) - 1) * (((n + 1 : ℕ) : ℝ) - 2) *
            (((n + 1 : ℕ) : ℝ) - 3) * x ^ 4 := by
          push_cast
          ring

private lemma bernWeight_central1 (n : ℕ) (x : ℝ) :
    ∑ k ∈ Finset.range (n + 1), ((k : ℝ) - (n : ℝ) * x) * bernWeight n k x = 0 := by
  have h1 := bernWeight_ff1 n x
  have h0 := bernWeight_sum_one n x
  calc (∑ k ∈ Finset.range (n + 1), ((k : ℝ) - (n : ℝ) * x) * bernWeight n k x)
      = (∑ k ∈ Finset.range (n + 1), (k : ℝ) * bernWeight n k x) -
          (n : ℝ) * x * ∑ k ∈ Finset.range (n + 1), bernWeight n k x := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun k _ => by ring
    _ = 0 := by rw [h1, h0]; ring

private lemma bernWeight_central2 (n : ℕ) (x : ℝ) :
    ∑ k ∈ Finset.range (n + 1), ((k : ℝ) - (n : ℝ) * x) ^ 2 * bernWeight n k x =
      (n : ℝ) * x * (1 - x) := by
  have h2 := bernWeight_ff2 n x
  have h1 := bernWeight_ff1 n x
  have h0 := bernWeight_sum_one n x
  calc (∑ k ∈ Finset.range (n + 1), ((k : ℝ) - (n : ℝ) * x) ^ 2 * bernWeight n k x)
      = (∑ k ∈ Finset.range (n + 1), (k : ℝ) * ((k : ℝ) - 1) * bernWeight n k x) +
          (1 - 2 * (n : ℝ) * x) * (∑ k ∈ Finset.range (n + 1), (k : ℝ) * bernWeight n k x) +
          ((n : ℝ) * x) ^ 2 * (∑ k ∈ Finset.range (n + 1), bernWeight n k x) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun k _ => by ring
    _ = (n : ℝ) * x * (1 - x) := by rw [h2, h1, h0]; ring

private lemma bernWeight_central4 (n : ℕ) (x : ℝ) :
    ∑ k ∈ Finset.range (n + 1), ((k : ℝ) - (n : ℝ) * x) ^ 4 * bernWeight n k x =
      (n : ℝ) * x * (1 - x) * (1 + 3 * ((n : ℝ) - 2) * x * (1 - x)) := by
  have h4 := bernWeight_ff4 n x
  have h3 := bernWeight_ff3 n x
  have h2 := bernWeight_ff2 n x
  have h1 := bernWeight_ff1 n x
  have h0 := bernWeight_sum_one n x
  let a : ℝ := (n : ℝ) * x
  calc (∑ k ∈ Finset.range (n + 1), ((k : ℝ) - a) ^ 4 * bernWeight n k x)
      = (∑ k ∈ Finset.range (n + 1),
            (k : ℝ) * ((k : ℝ) - 1) * ((k : ℝ) - 2) * ((k : ℝ) - 3) * bernWeight n k x) +
          (6 - 4 * a) * (∑ k ∈ Finset.range (n + 1),
            (k : ℝ) * ((k : ℝ) - 1) * ((k : ℝ) - 2) * bernWeight n k x) +
          (7 - 12 * a + 6 * a ^ 2) * (∑ k ∈ Finset.range (n + 1),
            (k : ℝ) * ((k : ℝ) - 1) * bernWeight n k x) +
          (1 - 4 * a + 6 * a ^ 2 - 4 * a ^ 3) * (∑ k ∈ Finset.range (n + 1),
            (k : ℝ) * bernWeight n k x) +
          a ^ 4 * (∑ k ∈ Finset.range (n + 1), bernWeight n k x) := by
        simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun k _ => by ring
    _ = (n : ℝ) * x * (1 - x) * (1 + 3 * ((n : ℝ) - 2) * x * (1 - x)) := by
        rw [h4, h3, h2, h1, h0]
        dsimp only [a]
        ring

private lemma bernWeight_scaled_moment1 {n : ℕ} (hn : n ≠ 0) (x : ℝ) :
    ∑ k ∈ Finset.range (n + 1), ((k : ℝ) / n - x) * bernWeight n k x = 0 := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  calc (∑ k ∈ Finset.range (n + 1), ((k : ℝ) / n - x) * bernWeight n k x)
      = (1 / (n : ℝ)) * ∑ k ∈ Finset.range (n + 1), ((k : ℝ) - (n : ℝ) * x) * bernWeight n k x := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        field_simp
    _ = 0 := by rw [bernWeight_central1]; ring

private lemma bernWeight_scaled_moment2 {n : ℕ} (hn : n ≠ 0) (x : ℝ) :
    ∑ k ∈ Finset.range (n + 1), ((k : ℝ) / n - x) ^ 2 * bernWeight n k x =
      x * (1 - x) / n := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  calc (∑ k ∈ Finset.range (n + 1), ((k : ℝ) / n - x) ^ 2 * bernWeight n k x)
      = (1 / (n : ℝ) ^ 2) *
          ∑ k ∈ Finset.range (n + 1), ((k : ℝ) - (n : ℝ) * x) ^ 2 * bernWeight n k x := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        field_simp
    _ = x * (1 - x) / n := by
        rw [bernWeight_central2]
        field_simp

private lemma bernWeight_scaled_moment4_le {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : x ∈ I) :
    ∑ k ∈ Finset.range (n + 1), ((k : ℝ) / n - x) ^ 4 * bernWeight n k x ≤
      4 / (n : ℝ) ^ 2 := by
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (by omega))
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hrew : (∑ k ∈ Finset.range (n + 1), ((k : ℝ) / n - x) ^ 4 * bernWeight n k x) =
      (1 / (n : ℝ) ^ 4) *
        ∑ k ∈ Finset.range (n + 1), ((k : ℝ) - (n : ℝ) * x) ^ 4 * bernWeight n k x := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hn' : (n : ℝ) ≠ 0 := hn0.ne'
    field_simp
  rw [hrew, bernWeight_central4]
  rcases hx with ⟨hx0, hx1⟩
  have h1x : 0 ≤ 1 - x := sub_nonneg.mpr hx1
  have hv0 : 0 ≤ x * (1 - x) := mul_nonneg hx0 h1x
  have hv1 : x * (1 - x) ≤ 1 := by nlinarith
  have hnum : (n : ℝ) * x * (1 - x) * (1 + 3 * ((n : ℝ) - 2) * x * (1 - x)) ≤
      4 * (n : ℝ) ^ 2 := by
    have hinner : 1 + 3 * ((n : ℝ) - 2) * x * (1 - x) ≤ 4 * (n : ℝ) := by
      have hsub : ((n : ℝ) - 2) * (x * (1 - x)) ≤ n := by nlinarith
      nlinarith
    have hprod1 : (n : ℝ) * (x * (1 - x)) * (1 + 3 * ((n : ℝ) - 2) * x * (1 - x)) ≤
        (n : ℝ) * (x * (1 - x)) * (4 * (n : ℝ)) := by
      apply mul_le_mul_of_nonneg_left hinner
      positivity
    have hprod2 : (n : ℝ) * (x * (1 - x)) * (4 * (n : ℝ)) ≤ (n : ℝ) * 1 * (4 * (n : ℝ)) := by
      gcongr
    linarith
  calc (1 / (n : ℝ) ^ 4) * ((n : ℝ) * x * (1 - x) * (1 + 3 * ((n : ℝ) - 2) * x * (1 - x)))
      ≤ (1 / (n : ℝ) ^ 4) * (4 * (n : ℝ) ^ 2) := by
        apply mul_le_mul_of_nonneg_left hnum
        positivity
    _ = 4 / (n : ℝ) ^ 2 := by
        have hn' : (n : ℝ) ≠ 0 := hn0.ne'
        field_simp

private lemma taylorWithinEval_two_eq (f : ℝ → ℝ) (x t : ℝ) :
    taylorWithinEval f 2 I x t =
      f x + iteratedDerivWithin 1 f I x * (t - x) +
        (1 / 2) * iteratedDerivWithin 2 f I x * (t - x) ^ 2 := by
  rw [taylor_within_apply]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
    Nat.factorial_zero, Nat.factorial_one, Nat.factorial_two, Nat.cast_one, Nat.cast_ofNat,
    inv_one, pow_zero, pow_one, mul_one, one_mul, smul_eq_mul, iteratedDerivWithin_zero]
  ring

theorem OMA.solution : type_of% @VoronovskajaTypeFormula.voronovskaja_theorem.bernstein_operators := by
  intro f x hx hf
  dsimp only
  set f' : ℝ := iteratedDerivWithin 1 f I x
  set f'' : ℝ := iteratedDerivWithin 2 f I x
  let r : ℝ → ℝ := fun t => f t - (f x + f' * (t - x) + (1 / 2) * f'' * (t - x) ^ 2)
  have hr_cont : ContinuousOn r I := by
    have hpoly : Continuous fun t : ℝ => f x + f' * (t - x) + (1 / 2) * f'' * (t - x) ^ 2 := by
      fun_prop
    exact hf.continuousOn.sub hpoly.continuousOn
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hr_cont
  let M₀ : ℝ := max M 1
  have hM₀_pos : 0 < M₀ := lt_of_lt_of_le zero_lt_one (le_max_right M 1)
  have hM₀ : ∀ t ∈ I, |r t| ≤ M₀ := fun t ht => by
    have ht' := hM t ht
    rw [Real.norm_eq_abs] at ht'
    exact ht'.trans (le_max_left M 1)
  have hr_littleO : r =o[𝓝[I] x] fun t => (t - x) ^ 2 := by
    have h := taylor_isLittleO (convex_Icc (0 : ℝ) 1) hx hf
    refine h.congr' (Eventually.of_forall fun t => ?_) EventuallyEq.rfl
    simp only [r, f', f'', taylorWithinEval_two_eq]
  have hdiff : ∀ {n : ℕ}, 1 ≤ n →
      (n : ℝ) * (VoronovskajaTypeFormula.bezierBernstein n 1 f x - f x) -
        (1 / 2) * x * (1 - x) * f'' =
      (n : ℝ) * ∑ k ∈ Finset.range (n + 1), r ((k : ℝ) / n) * bernWeight n k x := by
    intro n hn
    have hn0 : n ≠ 0 := by omega
    have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn0
    rw [bezierBernstein_one_eq]
    have hsplit : ∑ k ∈ Finset.range (n + 1), f ((k : ℝ) / n) * bernWeight n k x =
        f x * (∑ k ∈ Finset.range (n + 1), bernWeight n k x) +
        f' * (∑ k ∈ Finset.range (n + 1), ((k : ℝ) / n - x) * bernWeight n k x) +
        (1 / 2) * f'' * (∑ k ∈ Finset.range (n + 1), ((k : ℝ) / n - x) ^ 2 * bernWeight n k x) +
        ∑ k ∈ Finset.range (n + 1), r ((k : ℝ) / n) * bernWeight n k x := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      dsimp only [r]
      ring
    rw [hsplit, bernWeight_sum_one, bernWeight_scaled_moment1 hn0, bernWeight_scaled_moment2 hn0]
    field_simp
    ring
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε2 : 0 < ε / 2 := half_pos hε
  have hev := hr_littleO.bound hε2
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
  obtain ⟨δ, hδ_pos, hδ⟩ := hev
  have hpt : ∀ t ∈ I, |r t| ≤ (ε / 2) * (t - x) ^ 2 + (M₀ / δ ^ 4) * (t - x) ^ 4 := by
    intro t ht
    by_cases hdist : dist t x < δ
    · have h1 := hδ hdist ht
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (t - x))] at h1
      have h2 : 0 ≤ (M₀ / δ ^ 4) * (t - x) ^ 4 := by positivity
      linarith
    · have hdist : δ ≤ dist t x := le_of_not_gt hdist
      rw [Real.dist_eq] at hdist
      have hpow : δ ^ 4 ≤ (t - x) ^ 4 := by
        have h1 : δ ^ 4 ≤ |t - x| ^ 4 := pow_le_pow_left₀ hδ_pos.le hdist 4
        have h2 : |t - x| ^ 4 = (t - x) ^ 4 := by
          rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, pow_mul, sq_abs]
        linarith
      have h1 : 1 ≤ (t - x) ^ 4 / δ ^ 4 := (one_le_div (pow_pos hδ_pos 4)).mpr hpow
      have h2 : |r t| ≤ (M₀ / δ ^ 4) * (t - x) ^ 4 := by
        calc |r t| ≤ M₀ := hM₀ t ht
          _ = M₀ * 1 := (mul_one M₀).symm
          _ ≤ M₀ * ((t - x) ^ 4 / δ ^ 4) := mul_le_mul_of_nonneg_left h1 hM₀_pos.le
          _ = (M₀ / δ ^ 4) * (t - x) ^ 4 := by ring
      have h3 : 0 ≤ (ε / 2) * (t - x) ^ 2 := by positivity
      linarith
  obtain ⟨N, hN⟩ := exists_nat_gt ((4 * M₀ / δ ^ 4) / (ε / 2))
  refine ⟨max N 1, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_right N 1) hn
  have hnN : N ≤ n := le_trans (le_max_left N 1) hn
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (by omega))
  have hn0 : n ≠ 0 := by omega
  rw [Real.dist_eq, hdiff hn1, abs_mul, abs_of_pos hn_pos]
  have hsum_le : |∑ k ∈ Finset.range (n + 1), r ((k : ℝ) / n) * bernWeight n k x| ≤
      (ε / 2) * (x * (1 - x) / n) + (M₀ / δ ^ 4) * (4 / (n : ℝ) ^ 2) := by
    calc |∑ k ∈ Finset.range (n + 1), r ((k : ℝ) / n) * bernWeight n k x|
        ≤ ∑ k ∈ Finset.range (n + 1), |r ((k : ℝ) / n) * bernWeight n k x| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ k ∈ Finset.range (n + 1), |r ((k : ℝ) / n)| * bernWeight n k x := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [abs_mul, abs_of_nonneg (bernWeight_nonneg hx)]
      _ ≤ ∑ k ∈ Finset.range (n + 1),
            ((ε / 2) * ((k : ℝ) / n - x) ^ 2 + (M₀ / δ ^ 4) * ((k : ℝ) / n - x) ^ 4) *
              bernWeight n k x := by
          refine Finset.sum_le_sum fun k hk => ?_
          have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
          have htk : (k : ℝ) / n ∈ I := by
            refine ⟨by positivity, (div_le_one hn_pos).mpr ?_⟩
            exact_mod_cast hkn
          exact mul_le_mul_of_nonneg_right (hpt _ htk) (bernWeight_nonneg hx)
      _ = (ε / 2) * (∑ k ∈ Finset.range (n + 1), ((k : ℝ) / n - x) ^ 2 * bernWeight n k x) +
          (M₀ / δ ^ 4) * (∑ k ∈ Finset.range (n + 1), ((k : ℝ) / n - x) ^ 4 * bernWeight n k x) := by
          simp only [add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
      _ ≤ (ε / 2) * (x * (1 - x) / n) + (M₀ / δ ^ 4) * (4 / (n : ℝ) ^ 2) := by
          rw [bernWeight_scaled_moment2 hn0]
          have h4 := bernWeight_scaled_moment4_le hn1 hx
          gcongr
  have hx_bound : x * (1 - x) ≤ 1 := by
    rcases hx with ⟨hx0, hx1⟩
    nlinarith
  have hterm1 : (n : ℝ) * ((ε / 2) * (x * (1 - x) / n)) ≤ ε / 2 := by
    have hn' : (n : ℝ) ≠ 0 := hn_pos.ne'
    have heq : (n : ℝ) * ((ε / 2) * (x * (1 - x) / n)) = (ε / 2) * (x * (1 - x)) := by
      field_simp
    rw [heq]
    nlinarith
  have hterm2 : (n : ℝ) * ((M₀ / δ ^ 4) * (4 / (n : ℝ) ^ 2)) < ε / 2 := by
    have hn' : (n : ℝ) ≠ 0 := hn_pos.ne'
    have heq : (n : ℝ) * ((M₀ / δ ^ 4) * (4 / (n : ℝ) ^ 2)) = (4 * M₀ / δ ^ 4) / (n : ℝ) := by
      field_simp
    rw [heq, div_lt_iff₀ hn_pos]
    have hNn : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnN
    have hlt : (4 * M₀ / δ ^ 4) / (ε / 2) < (n : ℝ) := lt_of_lt_of_le hN hNn
    have hlt2 := (div_lt_iff₀ hε2).mp hlt
    linarith
  have hmul := mul_le_mul_of_nonneg_left hsum_le hn_pos.le
  rw [mul_add] at hmul
  linarith
