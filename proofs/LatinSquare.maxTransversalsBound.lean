import FormalConjectures.Paper.LatinSquare

-- Problem: Conjectures about Latin Squares — maxTransversalsBound
-- Upstream: formal-conjectures FormalConjectures/Paper/LatinSquare.lean:214 (declaration LatinSquare.maxTransversalsBound)
-- Credit: @nijv (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-! Proof of `LatinSquare.maxTransversalsBound` via Radhakrishnan entropy (upper bound)
and singular direct products with affine-orbit base cases (lower bound). -/

namespace StrategyCUpper

open Finset

private noncomputable def cConst : ℝ :=
  Real.sqrt ((3 - Real.sqrt 3) / 6) * Real.exp (Real.sqrt 3 / 6)

private noncomputable def radhaProd (n : ℕ) : ℝ :=
  ∏ m ∈ Finset.range n, (1 + (m : ℝ) * ((m : ℝ) - 1) / ((n : ℝ) - 2))

/- ### Part 1: Analytic and Constant Inequalities -/

private lemma radhaProd_pos {n : ℕ} (hn : 3 ≤ n) : 0 < radhaProd n := by
  unfold radhaProd
  apply Finset.prod_pos
  intro m _
  have hden : (0 : ℝ) < (n : ℝ) - 2 := by
    have : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hnum : (0 : ℝ) ≤ (m : ℝ) * ((m : ℝ) - 1) := by
    rcases m with _ | m
    · simp
    · have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      push_cast
      nlinarith
  positivity

private lemma exp_neg_half_le_613 : Real.exp (-(1 / 2 : ℝ)) ≤ 613 / 1000 := by
  rw [Real.exp_neg]
  have h1 : (79 / 48 : ℝ) ≤ Real.exp (1 / 2 : ℝ) := by
    have h := Real.sum_le_exp_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / 2) 4
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial] at h
    norm_num at h ⊢
    linarith
  have hpos : (0 : ℝ) < Real.exp (1 / 2 : ℝ) := Real.exp_pos _
  rw [inv_le_comm₀ hpos (by norm_num : (0 : ℝ) < 613 / 1000)]
  linarith

private lemma cConst_ge_613 : (613 / 1000 : ℝ) ≤ cConst := by
  unfold cConst
  have hs3_lo : (17320 / 10000 : ℝ) < Real.sqrt 3 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  have hs3_hi : Real.sqrt 3 < (17321 / 10000 : ℝ) := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  have hrad_pos : (0 : ℝ) ≤ (3 - Real.sqrt 3) / 6 := by linarith
  have hexp_ge : (17805 / 10000 : ℝ) ≤ Real.exp (Real.sqrt 3 / 3) := by
    have hx_lo : (5773 / 10000 : ℝ) ≤ Real.sqrt 3 / 3 := by linarith
    have h1 : Real.exp (5773 / 10000 : ℝ) ≤ Real.exp (Real.sqrt 3 / 3) :=
      Real.exp_le_exp.mpr hx_lo
    have h2 := Real.sum_le_exp_of_nonneg (by positivity : (0 : ℝ) ≤ 5773 / 10000) 5
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial] at h2
    norm_num at h2 ⊢
    linarith
  have hsq : ((613 / 1000 : ℝ)) ^ 2 ≤
      (Real.sqrt ((3 - Real.sqrt 3) / 6) * Real.exp (Real.sqrt 3 / 6)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hrad_pos, ← Real.exp_nat_mul]
    have hmul : (2 : ℕ) * (Real.sqrt 3 / 6) = Real.sqrt 3 / 3 := by push_cast; ring
    rw [hmul]
    have hrad_ge : (12679 / 60000 : ℝ) ≤ (3 - Real.sqrt 3) / 6 := by linarith
    nlinarith
  have hrhs_nonneg : 0 ≤ Real.sqrt ((3 - Real.sqrt 3) / 6) * Real.exp (Real.sqrt 3 / 6) := by
    positivity
  nlinarith

private lemma sum_mul_sub_one (n : ℕ) :
    ∑ m ∈ Finset.range n, (m : ℝ) * ((m : ℝ) - 1) =
      (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) / 3 := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

private lemma sum_sq_mul_sub_one (n : ℕ) :
    ∑ m ∈ Finset.range n, ((m : ℝ) * ((m : ℝ) - 1)) ^ 2 =
      (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) * (3 * (n : ℝ) ^ 2 - 6 * (n : ℝ) + 1) / 15 := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

private lemma sum_frac_ge_half {n : ℕ} (hn : 16 ≤ n) :
    (1 / 2 : ℝ) ≤
      ∑ m ∈ Finset.range n,
        ((m : ℝ) * ((m : ℝ) - 1)) /
          (((n : ℝ) - 1) * (((n : ℝ) - 2) + (m : ℝ) * ((m : ℝ) - 1))) := by
  have hnR : (16 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  set A : ℝ := (n : ℝ) - 2
  have hA : 0 < A := by linarith
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  let x : ℕ → ℝ := fun m => (m : ℝ) * ((m : ℝ) - 1)
  have hx_nonneg : ∀ m : ℕ, 0 ≤ x m := by
    intro m
    rcases m with _ | m
    · simp [x]
    · dsimp [x]; push_cast; nlinarith
  have hden_pos : ∀ m : ℕ, 0 < A + x m := fun m => by linarith [hx_nonneg m]
  let f : ℕ → ℝ := fun m => Real.sqrt (x m / (A + x m))
  let g : ℕ → ℝ := fun m => Real.sqrt (x m * (A + x m))
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range n) f g
  have hfg : ∀ m ∈ Finset.range n, f m * g m = x m := by
    intro m _
    dsimp [f, g]
    rw [← Real.sqrt_mul (div_nonneg (hx_nonneg m) (hden_pos m).le)]
    have hmul : x m / (A + x m) * (x m * (A + x m)) = x m * x m := by
      field_simp [(hden_pos m).ne']
    rw [hmul, Real.sqrt_mul_self (hx_nonneg m)]
  have hf2 : ∀ m ∈ Finset.range n, f m ^ 2 = x m / (A + x m) := by
    intro m _
    exact Real.sq_sqrt (div_nonneg (hx_nonneg m) (hden_pos m).le)
  have hg2 : ∀ m ∈ Finset.range n, g m ^ 2 = A * x m + (x m) ^ 2 := by
    intro m _
    dsimp [g]
    rw [Real.sq_sqrt (mul_nonneg (hx_nonneg m) (hden_pos m).le)]
    ring
  rw [Finset.sum_congr rfl hfg, Finset.sum_congr rfl hf2, Finset.sum_congr rfl hg2] at hcs
  have hS1 : ∑ m ∈ Finset.range n, x m = (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) / 3 :=
    sum_mul_sub_one n
  have hS2 : ∑ m ∈ Finset.range n, (x m) ^ 2 =
      (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) * (3 * (n : ℝ) ^ 2 - 6 * (n : ℝ) + 1) / 15 :=
    sum_sq_mul_sub_one n
  have hsumG : ∑ m ∈ Finset.range n, (A * x m + (x m) ^ 2) =
      A * (∑ m ∈ Finset.range n, x m) + ∑ m ∈ Finset.range n, (x m) ^ 2 := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hsumG, hS1, hS2] at hcs
  have hsumG_pos : 0 < A * ((n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) / 3) +
      (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) * (3 * (n : ℝ) ^ 2 - 6 * (n : ℝ) + 1) / 15 := by
    have hq : 0 < 3 * (n : ℝ) ^ 2 - 6 * (n : ℝ) + 1 := by nlinarith
    have hprod : 0 < (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) := by nlinarith
    positivity
  have hLHS : ∑ m ∈ Finset.range n,
      ((m : ℝ) * ((m : ℝ) - 1)) / (((n : ℝ) - 1) * (((n : ℝ) - 2) + (m : ℝ) * ((m : ℝ) - 1))) =
      (∑ m ∈ Finset.range n, x m / (A + x m)) / ((n : ℝ) - 1) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro m _
    dsimp [x, A]
    rw [div_div]
    congr 1
    ring
  rw [hLHS, le_div_iff₀ hn1]
  have hpoly : (1 / 2 : ℝ) * ((n : ℝ) - 1) *
      (A * ((n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) / 3) +
        (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) * (3 * (n : ℝ) ^ 2 - 6 * (n : ℝ) + 1) / 15) ≤
      ((n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) / 3) ^ 2 := by
    have hdiff : ((n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) / 3) ^ 2 -
        (1 / 2 : ℝ) * ((n : ℝ) - 1) *
          (A * ((n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) / 3) +
            (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) * (3 * (n : ℝ) ^ 2 - 6 * (n : ℝ) + 1) / 15) =
        (n : ℝ) * ((n : ℝ) - 1) ^ 2 * ((n : ℝ) - 2) *
          ((n : ℝ) ^ 2 - 17 * (n : ℝ) + 27) / 90 := by
      dsimp [A]; ring
    have hquad : 0 ≤ (n : ℝ) ^ 2 - 17 * (n : ℝ) + 27 := by nlinarith
    have hfac : 0 ≤ (n : ℝ) * ((n : ℝ) - 1) ^ 2 * ((n : ℝ) - 2) := by positivity
    linarith [div_nonneg (mul_nonneg hfac hquad) (by norm_num : (0 : ℝ) ≤ 90)]
  nlinarith

private lemma radhaProd_step_ge16 {n : ℕ} (hn : 16 ≤ n) :
    radhaProd (n + 1) ≤ (613 / 1000 : ℝ) * ((n : ℝ) + 1) * radhaProd n := by
  have hnR : (16 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hn2 : (0 : ℝ) < (n : ℝ) - 2 := by linarith
  have hPpos : 0 < radhaProd n := radhaProd_pos (by omega)
  have hP1 : radhaProd (n + 1) =
      ((n : ℝ) + 1) * ∏ m ∈ Finset.range n, (1 + (m : ℝ) * ((m : ℝ) - 1) / ((n : ℝ) - 1)) := by
    unfold radhaProd
    rw [Finset.prod_range_succ]
    have hcast : (((n + 1 : ℕ) : ℝ) - 2) = (n : ℝ) - 1 := by push_cast; ring
    simp_rw [hcast]
    have hlast : 1 + (n : ℝ) * ((n : ℝ) - 1) / ((n : ℝ) - 1) = (n : ℝ) + 1 := by
      field_simp [hn1.ne']
      ring
    rw [hlast, mul_comm]
  rw [hP1]
  have hratio : (∏ m ∈ Finset.range n, (1 + (m : ℝ) * ((m : ℝ) - 1) / ((n : ℝ) - 1))) /
      radhaProd n =
      ∏ m ∈ Finset.range n,
        (1 - ((m : ℝ) * ((m : ℝ) - 1)) /
          (((n : ℝ) - 1) * (((n : ℝ) - 2) + (m : ℝ) * ((m : ℝ) - 1)))) := by
    unfold radhaProd
    rw [← Finset.prod_div_distrib]
    apply Finset.prod_congr rfl
    intro m _
    have hx : 0 ≤ (m : ℝ) * ((m : ℝ) - 1) := by
      rcases m with _ | m
      · simp
      · push_cast; nlinarith
    have hden : 0 < ((n : ℝ) - 2) + (m : ℝ) * ((m : ℝ) - 1) := by linarith
    field_simp [hn1.ne', hn2.ne', hden.ne']
    ring
  have hle_exp : ∏ m ∈ Finset.range n,
      (1 - ((m : ℝ) * ((m : ℝ) - 1)) /
        (((n : ℝ) - 1) * (((n : ℝ) - 2) + (m : ℝ) * ((m : ℝ) - 1)))) ≤
      Real.exp (-(∑ m ∈ Finset.range n,
        ((m : ℝ) * ((m : ℝ) - 1)) /
          (((n : ℝ) - 1) * (((n : ℝ) - 2) + (m : ℝ) * ((m : ℝ) - 1))))) := by
    rw [← Finset.sum_neg_distrib, Real.exp_sum]
    apply Finset.prod_le_prod
    · intro m _
      have hx : 0 ≤ (m : ℝ) * ((m : ℝ) - 1) := by
        rcases m with _ | m
        · simp
        · push_cast; nlinarith
      have hden : 0 < ((n : ℝ) - 2) + (m : ℝ) * ((m : ℝ) - 1) := by linarith
      have h1 : (m : ℝ) * ((m : ℝ) - 1) ≤
          ((n : ℝ) - 1) * (((n : ℝ) - 2) + (m : ℝ) * ((m : ℝ) - 1)) := by nlinarith
      have hdiv : ((m : ℝ) * ((m : ℝ) - 1)) /
          (((n : ℝ) - 1) * (((n : ℝ) - 2) + (m : ℝ) * ((m : ℝ) - 1))) ≤ 1 := by
        rw [div_le_one (mul_pos hn1 hden)]
        exact h1
      linarith
    · intro m _
      have h := Real.add_one_le_exp (-(((m : ℝ) * ((m : ℝ) - 1)) /
        (((n : ℝ) - 1) * (((n : ℝ) - 2) + (m : ℝ) * ((m : ℝ) - 1)))))
      linarith
  have hbound : (∏ m ∈ Finset.range n, (1 + (m : ℝ) * ((m : ℝ) - 1) / ((n : ℝ) - 1))) /
      radhaProd n ≤ 613 / 1000 := by
    rw [hratio]
    calc _ ≤ Real.exp (-(∑ m ∈ Finset.range n,
            ((m : ℝ) * ((m : ℝ) - 1)) /
              (((n : ℝ) - 1) * (((n : ℝ) - 2) + (m : ℝ) * ((m : ℝ) - 1))))) := hle_exp
      _ ≤ Real.exp (-(1 / 2 : ℝ)) := Real.exp_le_exp.mpr (neg_le_neg (sum_frac_ge_half hn))
      _ ≤ 613 / 1000 := exp_neg_half_le_613
  rw [div_le_iff₀ hPpos] at hbound
  have hn1pos : (0 : ℝ) ≤ (n : ℝ) + 1 := by linarith
  nlinarith

private lemma radhaProd_step_small {n : ℕ} (hn6 : 6 ≤ n) (hn15 : n ≤ 15) :
    radhaProd (n + 1) ≤ (613 / 1000 : ℝ) * ((n : ℝ) + 1) * radhaProd n := by
  interval_cases n <;>
    simp only [radhaProd, Finset.prod_range_succ, Finset.range_zero, Finset.prod_empty] <;>
    norm_num

private lemma radhaProd_base6 :
    radhaProd 6 ≤ (613 / 1000 : ℝ) ^ 6 * Real.sqrt 6 * (Nat.factorial 6 : ℝ) := by
  have hP6 : radhaProd 6 = 90 := by
    simp only [radhaProd, Finset.prod_range_succ, Finset.range_zero, Finset.prod_empty]
    norm_num
  rw [hP6]
  have hfac6 : (Nat.factorial 6 : ℝ) = 720 := by norm_num [Nat.factorial]
  rw [hfac6]
  have hsq : (90 : ℝ) ^ 2 ≤ ((613 / 1000 : ℝ) ^ 6 * Real.sqrt 6 * 720) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 6)]
    norm_num
  have hrhs_nonneg : 0 ≤ (613 / 1000 : ℝ) ^ 6 * Real.sqrt 6 * 720 := by positivity
  nlinarith

private lemma radhaProd_le_target {n : ℕ} (hn : 6 ≤ n) :
    radhaProd n ≤ cConst ^ n * Real.sqrt n * (n.factorial : ℝ) := by
  have hstep : ∀ k ≥ 6, radhaProd (k + 1) ≤ (613 / 1000 : ℝ) * ((k : ℝ) + 1) * radhaProd k := by
    intro k hk
    by_cases hk15 : k ≤ 15
    · exact radhaProd_step_small hk hk15
    · exact radhaProd_step_ge16 (by omega)
  have h613 : ∀ k ≥ 6, radhaProd k ≤ (613 / 1000 : ℝ) ^ k * Real.sqrt k * (k.factorial : ℝ) := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => exact radhaProd_base6
    | succ k hk ih =>
      have hst := hstep k hk
      have hsqrt : Real.sqrt k ≤ Real.sqrt (k + 1 : ℕ) := by
        apply Real.sqrt_le_sqrt
        exact_mod_cast Nat.le_succ k
      have hfac : ((k + 1).factorial : ℝ) = ((k : ℝ) + 1) * (k.factorial : ℝ) := by
        rw [Nat.factorial_succ]
        push_cast
        ring
      rw [hfac, pow_succ]
      have h0 : 0 ≤ (613 / 1000 : ℝ) * ((k : ℝ) + 1) := by positivity
      have h1 : radhaProd (k + 1) ≤
          (613 / 1000 : ℝ) * ((k : ℝ) + 1) *
            ((613 / 1000 : ℝ) ^ k * Real.sqrt k * (k.factorial : ℝ)) :=
        le_trans hst (mul_le_mul_of_nonneg_left ih h0)
      have h2 : (613 / 1000 : ℝ) * ((k : ℝ) + 1) *
            ((613 / 1000 : ℝ) ^ k * Real.sqrt k * (k.factorial : ℝ)) ≤
          (613 / 1000 : ℝ) ^ k * (613 / 1000 : ℝ) * Real.sqrt (k + 1 : ℕ) *
            (((k : ℝ) + 1) * (k.factorial : ℝ)) := by
        have hfac_nn : 0 ≤ (k.factorial : ℝ) := Nat.cast_nonneg _
        have hpow_nn : 0 ≤ (613 / 1000 : ℝ) ^ k * (613 / 1000 : ℝ) * (((k : ℝ) + 1) * (k.factorial : ℝ)) := by
          positivity
        nlinarith
      exact le_trans h1 h2
  have hc := cConst_ge_613
  have hpow : (613 / 1000 : ℝ) ^ n ≤ cConst ^ n := pow_le_pow_left₀ (by norm_num) hc n
  have hmul_nn : 0 ≤ Real.sqrt n * (n.factorial : ℝ) := by positivity
  calc radhaProd n
      ≤ (613 / 1000 : ℝ) ^ n * Real.sqrt n * (n.factorial : ℝ) := h613 n hn
    _ = (613 / 1000 : ℝ) ^ n * (Real.sqrt n * (n.factorial : ℝ)) := by ring
    _ ≤ cConst ^ n * (Real.sqrt n * (n.factorial : ℝ)) := mul_le_mul_of_nonneg_right hpow hmul_nn
    _ = cConst ^ n * Real.sqrt n * (n.factorial : ℝ) := by ring

/- ### Part 2: Radhakrishnan Entropy Upper Bound for all `n ≥ 3` -/

private lemma card_perm_apply_eq {n : ℕ} (hn : 1 ≤ n) (t i : Fin n) :
    (Finset.univ.filter (fun π : Equiv.Perm (Fin n) => π t = i)).card = (n - 1).factorial := by
  have hconst : ∀ i' : Fin n,
      (Finset.univ.filter (fun π : Equiv.Perm (Fin n) => π t = i')).card =
        (Finset.univ.filter (fun π : Equiv.Perm (Fin n) => π t = i)).card := by
    intro i'
    refine Finset.card_bij (fun π _ => Equiv.swap i' i * π) ?_ ?_ ?_
    · intro π hπ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hπ ⊢
      simp [Equiv.Perm.mul_apply, hπ]
    · intro π₁ _ π₂ _ h
      exact mul_left_cancel h
    · intro π hπ
      refine ⟨Equiv.swap i' i * π, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hπ ⊢
        simp [Equiv.Perm.mul_apply, hπ]
      · simp [← mul_assoc]
  have hsum : ∑ i' : Fin n,
      (Finset.univ.filter (fun π : Equiv.Perm (Fin n) => π t = i')).card = n.factorial := by
    have h := Finset.card_eq_sum_card_fiberwise
      (f := fun π : Equiv.Perm (Fin n) => π t) (s := Finset.univ) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _)
    rw [← h, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  simp_rw [hconst] at hsum
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum
  have hfac : n.factorial = n * (n - 1).factorial := by
    cases n with
    | zero => omega
    | succ m => simp [Nat.factorial_succ]
  rw [hfac] at hsum
  exact Nat.eq_of_mul_eq_mul_left (by omega) hsum

private lemma exists_perm_triple {n : ℕ} {a₁ a₂ a₃ b₁ b₂ b₃ : Fin n}
    (ha12 : a₁ ≠ a₂) (ha13 : a₁ ≠ a₃) (ha23 : a₂ ≠ a₃)
    (hb12 : b₁ ≠ b₂) (hb13 : b₁ ≠ b₃) (hb23 : b₂ ≠ b₃) :
    ∃ σ : Equiv.Perm (Fin n), σ a₁ = b₁ ∧ σ a₂ = b₂ ∧ σ a₃ = b₃ := by
  let σ₁ : Equiv.Perm (Fin n) := Equiv.swap a₁ b₁
  have h1a : σ₁ a₁ = b₁ := Equiv.swap_apply_left a₁ b₁
  have h1b : σ₁ a₂ ≠ b₁ := by
    intro h; exact ha12 (σ₁.injective (h1a.trans h.symm))
  have h1c : σ₁ a₃ ≠ b₁ := by
    intro h; exact ha13 (σ₁.injective (h1a.trans h.symm))
  have h1bc : σ₁ a₂ ≠ σ₁ a₃ := fun h => ha23 (σ₁.injective h)
  let σ₂ : Equiv.Perm (Fin n) := Equiv.swap (σ₁ a₂) b₂
  have h2a : σ₂ b₁ = b₁ := Equiv.swap_apply_of_ne_of_ne h1b.symm hb12
  have h2b : σ₂ (σ₁ a₂) = b₂ := Equiv.swap_apply_left _ _
  have h2c1 : σ₂ (σ₁ a₃) ≠ b₁ := by
    intro h; exact h1c (σ₂.injective (h.trans h2a.symm))
  have h2c2 : σ₂ (σ₁ a₃) ≠ b₂ := by
    intro h; exact h1bc.symm (σ₂.injective (h.trans h2b.symm))
  let σ₃ : Equiv.Perm (Fin n) := Equiv.swap (σ₂ (σ₁ a₃)) b₃
  refine ⟨σ₃ * σ₂ * σ₁, ?_, ?_, ?_⟩
  · simp only [Equiv.Perm.mul_apply, h1a, h2a]
    exact Equiv.swap_apply_of_ne_of_ne h2c1.symm hb13
  · simp only [Equiv.Perm.mul_apply, h2b]
    exact Equiv.swap_apply_of_ne_of_ne h2c2.symm hb23
  · simp only [Equiv.Perm.mul_apply]
    exact Equiv.swap_apply_left _ _

private lemma card_perm_three_fixed {n : ℕ} (hn : 3 ≤ n) {t s₁ s₂ i r₁ r₂ : Fin n}
    (hts₁ : t ≠ s₁) (hts₂ : t ≠ s₂) (hs : s₁ ≠ s₂)
    (hir₁ : i ≠ r₁) (hir₂ : i ≠ r₂) (hr : r₁ ≠ r₂) :
    (Finset.univ.filter (fun π : Equiv.Perm (Fin n) =>
      π t = i ∧ π s₁ = r₁ ∧ π s₂ = r₂)).card = (n - 3).factorial := by
  let S : Finset (Fin n × Fin n × Fin n) :=
    Finset.univ.filter (fun p => p.1 ≠ p.2.1 ∧ p.1 ≠ p.2.2 ∧ p.2.1 ≠ p.2.2)
  have hconst : ∀ p ∈ S,
      (Finset.univ.filter (fun π : Equiv.Perm (Fin n) =>
        π t = p.1 ∧ π s₁ = p.2.1 ∧ π s₂ = p.2.2)).card =
      (Finset.univ.filter (fun π : Equiv.Perm (Fin n) =>
        π t = i ∧ π s₁ = r₁ ∧ π s₂ = r₂)).card := by
    intro ⟨i', r₁', r₂'⟩ hp
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    obtain ⟨σ, hσ1, hσ2, hσ3⟩ := exists_perm_triple hp.1 hp.2.1 hp.2.2 hir₁ hir₂ hr
    refine Finset.card_bij (fun π _ => σ * π) ?_ ?_ ?_
    · intro π hπ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hπ ⊢
      simp [Equiv.Perm.mul_apply, hπ.1, hπ.2.1, hπ.2.2, hσ1, hσ2, hσ3]
    · intro π₁ _ π₂ _ h
      exact mul_left_cancel h
    · intro π hπ
      refine ⟨σ⁻¹ * π, ?_, by simp [← mul_assoc]⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hπ ⊢
      refine ⟨?_, ?_, ?_⟩
      · simp [Equiv.Perm.mul_apply, hπ.1, ← hσ1]
      · simp [Equiv.Perm.mul_apply, hπ.2.1, ← hσ2]
      · simp [Equiv.Perm.mul_apply, hπ.2.2, ← hσ3]
  have hmaps : ∀ π ∈ (Finset.univ : Finset (Equiv.Perm (Fin n))),
      (π t, π s₁, π s₂) ∈ S := by
    intro π _
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => hts₁ (π.injective h), fun h => hts₂ (π.injective h),
      fun h => hs (π.injective h)⟩
  have hsum : ∑ p ∈ S,
      (Finset.univ.filter (fun π : Equiv.Perm (Fin n) =>
        (π t, π s₁, π s₂) = p)).card = n.factorial := by
    have h := Finset.card_eq_sum_card_fiberwise
      (f := fun π : Equiv.Perm (Fin n) => (π t, π s₁, π s₂))
      (s := Finset.univ) (t := S) hmaps
    rw [← h, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  have heq : ∀ p ∈ S,
      (Finset.univ.filter (fun π : Equiv.Perm (Fin n) => (π t, π s₁, π s₂) = p)).card =
      (Finset.univ.filter (fun π : Equiv.Perm (Fin n) =>
        π t = i ∧ π s₁ = r₁ ∧ π s₂ = r₂)).card := by
    intro p hp
    convert hconst p hp using 2
    ext π
    simp [Prod.ext_iff]
  rw [Finset.sum_congr rfl heq, Finset.sum_const, smul_eq_mul] at hsum
  have hScard : S.card = n * (n - 1) * (n - 2) := by
    have hS1 : S = (Finset.univ : Finset (Fin n)).biUnion (fun a =>
        ((Finset.univ.erase a).biUnion (fun b =>
          (((Finset.univ.erase a).erase b).image (fun c => (a, b, c)))))) := by
      ext ⟨a, b, c⟩
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, and_true, Finset.mem_biUnion,
        Finset.mem_erase, Finset.mem_image, Prod.mk.injEq]
      constructor
      · intro ⟨hab, hac, hbc⟩
        exact ⟨a, ⟨b, ⟨hab.symm, ⟨c, ⟨⟨hbc.symm, hac.symm⟩, rfl, rfl, rfl⟩⟩⟩⟩⟩
      · rintro ⟨a', b', hba, c', ⟨hcb, hca⟩, rfl, rfl, rfl⟩
        exact ⟨hba.symm, hca.symm, hcb.symm⟩
    rw [hS1, Finset.card_biUnion]
    · have hinner : ∀ a : Fin n,
          ((Finset.univ.erase a).biUnion (fun b =>
            (((Finset.univ.erase a).erase b).image (fun c => (a, b, c))))).card =
          (n - 1) * (n - 2) := by
        intro a
        rw [Finset.card_biUnion]
        · have h2 : ∀ b ∈ Finset.univ.erase a,
              (((Finset.univ.erase a).erase b).image (fun c => (a, b, c))).card = n - 2 := by
            intro b hb
            rw [Finset.card_image_of_injective]
            · rw [Finset.card_erase_of_mem hb, Finset.card_erase_of_mem (Finset.mem_univ a),
                Finset.card_univ, Fintype.card_fin]
              omega
            · intro c₁ c₂ h; cases h; rfl
          rw [Finset.sum_congr rfl h2, Finset.sum_const,
            Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ, Fintype.card_fin,
            smul_eq_mul]
        · intro b₁ _ b₂ _ hb
          dsimp [Function.onFun]
          rw [Finset.disjoint_left]
          intro p hp1 hp2
          simp only [Finset.mem_image] at hp1 hp2
          rcases hp1 with ⟨_, _, rfl⟩
          rcases hp2 with ⟨_, _, h⟩
          exact hb (by cases h; rfl)
      simp_rw [hinner]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_assoc]
    · intro a₁ _ a₂ _ ha
      dsimp [Function.onFun]
      rw [Finset.disjoint_left]
      intro p hp1 hp2
      simp only [Finset.mem_biUnion, Finset.mem_image] at hp1 hp2
      rcases hp1 with ⟨_, _, _, _, rfl⟩
      rcases hp2 with ⟨_, _, _, _, h⟩
      exact ha (by cases h; rfl)
  rw [hScard] at hsum
  have hfac : n.factorial = n * (n - 1) * (n - 2) * (n - 3).factorial := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
    simp [Nat.factorial_succ]
    ring
  rw [hfac] at hsum
  have hpos : 0 < n * (n - 1) * (n - 2) := by
    have : 0 < n := by omega
    have : 0 < n - 1 := by omega
    have : 0 < n - 2 := by omega
    positivity
  exact Nat.eq_of_mul_eq_mul_left hpos hsum

private lemma card_perm_after {n : ℕ} (hn : 3 ≤ n) (t i r₁ r₂ : Fin n)
    (hir₁ : i ≠ r₁) (hir₂ : i ≠ r₂) (hr : r₁ ≠ r₂) :
    (Finset.univ.filter (fun π : Equiv.Perm (Fin n) =>
      π t = i ∧ ∀ s : Fin n, s < t → π s ≠ r₁ ∧ π s ≠ r₂)).card =
    (n - 1 - t.1) * (n - 1 - t.1 - 1) * (n - 3).factorial := by
  let T : Finset (Fin n) := Finset.univ.filter (fun s : Fin n => t < s)
  let P : Finset (Fin n × Fin n) := (T ×ˢ T).filter (fun p => p.1 ≠ p.2)
  let F : Finset (Equiv.Perm (Fin n)) :=
    Finset.univ.filter (fun π : Equiv.Perm (Fin n) =>
      π t = i ∧ ∀ s : Fin n, s < t → π s ≠ r₁ ∧ π s ≠ r₂)
  have hmaps : ∀ π ∈ F, (π.symm r₁, π.symm r₂) ∈ P := by
    intro π hπ
    simp only [F, Finset.mem_filter, Finset.mem_univ, true_and] at hπ
    simp only [P, T, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and]
    have h1 : t < π.symm r₁ := by
      rcases lt_trichotomy t (π.symm r₁) with hlt | heq | hgt
      · exact hlt
      · exfalso; apply hir₁
        calc i = π t := hπ.1.symm
          _ = π (π.symm r₁) := by rw [heq]
          _ = r₁ := π.apply_symm_apply r₁
      · exfalso; exact (hπ.2 _ hgt).1 (π.apply_symm_apply r₁)
    have h2 : t < π.symm r₂ := by
      rcases lt_trichotomy t (π.symm r₂) with hlt | heq | hgt
      · exact hlt
      · exfalso; apply hir₂
        calc i = π t := hπ.1.symm
          _ = π (π.symm r₂) := by rw [heq]
          _ = r₂ := π.apply_symm_apply r₂
      · exfalso; exact (hπ.2 _ hgt).2 (π.apply_symm_apply r₂)
    exact ⟨⟨h1, h2⟩, fun h => hr (π.symm.injective h)⟩
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  have hfib : ∀ p ∈ P,
      (F.filter (fun π => (π.symm r₁, π.symm r₂) = p)).card = (n - 3).factorial := by
    intro ⟨s₁, s₂⟩ hp
    simp only [P, T, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and] at hp
    have hts₁ : t ≠ s₁ := ne_of_lt hp.1.1
    have hts₂ : t ≠ s₂ := ne_of_lt hp.1.2
    have hset : F.filter (fun π => (π.symm r₁, π.symm r₂) = (s₁, s₂)) =
        Finset.univ.filter (fun π : Equiv.Perm (Fin n) =>
          π t = i ∧ π s₁ = r₁ ∧ π s₂ = r₂) := by
      ext π
      simp only [F, Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq]
      constructor
      · rintro ⟨⟨ht, _⟩, hs1, hs2⟩
        exact ⟨ht, by rw [← hs1]; exact π.apply_symm_apply r₁,
          by rw [← hs2]; exact π.apply_symm_apply r₂⟩
      · rintro ⟨ht, hs1, hs2⟩
        refine ⟨⟨ht, fun s hst => ⟨?_, ?_⟩⟩, ?_, ?_⟩
        · intro h; exact ne_of_lt (lt_trans hst hp.1.1) (π.injective (h.trans hs1.symm))
        · intro h; exact ne_of_lt (lt_trans hst hp.1.2) (π.injective (h.trans hs2.symm))
        · exact (π.symm_apply_eq).mpr hs1.symm
        · exact (π.symm_apply_eq).mpr hs2.symm
    rw [hset]
    exact card_perm_three_fixed hn hts₁ hts₂ hp.2 hir₁ hir₂ hr
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul]
  have hTcard : T.card = n - 1 - t.1 := by
    have hbij : T.card = (Finset.Ioo t.1 n).card := by
      refine Finset.card_bij (fun s _ => s.1) ?_ ?_ ?_
      · intro s hs
        simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at hs
        simp only [Finset.mem_Ioo]
        exact ⟨hs, s.2⟩
      · intro s₁ _ s₂ _ h; exact Fin.ext h
      · intro k hk
        simp only [Finset.mem_Ioo] at hk
        refine ⟨⟨k, hk.2⟩, ?_, rfl⟩
        simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hk.1
    rw [hbij, Nat.card_Ioo]
    omega
  have hPcard : P.card = T.card * (T.card - 1) := by
    have hP1 : P = T.biUnion (fun a => (T.erase a).image (fun b => (a, b))) := by
      ext ⟨a, b⟩
      simp only [P, Finset.mem_filter, Finset.mem_product, Finset.mem_biUnion,
        Finset.mem_image, Finset.mem_erase, Prod.mk.injEq]
      constructor
      · intro ⟨⟨ha, hb⟩, hab⟩
        exact ⟨a, ha, b, ⟨hab.symm, hb⟩, rfl, rfl⟩
      · rintro ⟨a', ha', b', ⟨hba, hb'⟩, rfl, rfl⟩
        exact ⟨⟨ha', hb'⟩, hba.symm⟩
    rw [hP1, Finset.card_biUnion]
    · have hinner : ∀ a ∈ T, ((T.erase a).image (fun b => (a, b))).card = T.card - 1 := by
        intro a ha
        rw [Finset.card_image_of_injective]
        · exact Finset.card_erase_of_mem ha
        · intro b₁ b₂ h; cases h; rfl
      rw [Finset.sum_congr rfl hinner, Finset.sum_const, smul_eq_mul]
    · intro a₁ _ a₂ _ ha
      dsimp [Function.onFun]
      rw [Finset.disjoint_left]
      intro p hp1 hp2
      simp only [Finset.mem_image] at hp1 hp2
      rcases hp1 with ⟨_, _, rfl⟩
      rcases hp2 with ⟨_, _, h⟩
      exact ha (by cases h; rfl)
  rw [hPcard, hTcard]

private lemma numTransversals_le_radhaProd {n : ℕ} (hn : 3 ≤ n) (L : LatinSquare n) :
    (numTransversals L : ℝ) ≤ radhaProd n := by
  let Ω := {σ : Fin n → Fin n // IsTransversal L σ}
  change (Fintype.card Ω : ℝ) ≤ radhaProd n
  by_cases hM : Fintype.card Ω = 0
  · rw [hM]; simp only [Nat.cast_zero]; exact (radhaProd_pos hn).le
  have hMpos : 0 < Fintype.card Ω := Nat.pos_of_ne_zero hM
  have hMposR : (0 : ℝ) < (Fintype.card Ω : ℝ) := Nat.cast_pos.mpr hMpos
  let fiberK : Equiv.Perm (Fin n) → Ω → ℕ → Finset Ω := fun π x k =>
    Finset.univ.filter (fun y : Ω => ∀ s : Fin n, s.1 < k → y.1 (π s) = x.1 (π s))
  let avail : Equiv.Perm (Fin n) → Fin n → Ω → Finset (Fin n) := fun π t x =>
    Finset.univ.filter (fun j : Fin n =>
      ∀ s : Fin n, s < t → j ≠ x.1 (π s) ∧ L.mat (π t) j ≠ L.mat (π s) (x.1 (π s)))
  have hmem_fiber : ∀ π x k, x ∈ fiberK π x k := by
    intro π x k; simp [fiberK]
  have hcard_fiber_pos : ∀ π x k, (0 : ℝ) < ((fiberK π x k).card : ℝ) := by
    intro π x k
    exact Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨x, hmem_fiber π x k⟩)
  have hmem_avail : ∀ π t x, x.1 (π t) ∈ avail π t x := by
    intro π t x
    simp only [avail, Finset.mem_filter, Finset.mem_univ, true_and]
    intro s hst
    have hne : π t ≠ π s := fun h => ne_of_gt hst (π.injective h)
    exact ⟨fun h => hne (x.2.1 h), fun h => hne (x.2.2 h)⟩
  have hcard_avail_pos : ∀ π t x, (0 : ℝ) < ((avail π t x).card : ℝ) := by
    intro π t x
    exact Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨x.1 (π t), hmem_avail π t x⟩)
  -- Step 1: Telescoping chain rule
  have htele : ∀ π : Equiv.Perm (Fin n), ∀ x : Ω,
      Real.log (Fintype.card Ω : ℝ) =
        ∑ t : Fin n,
          (Real.log ((fiberK π x t.1).card : ℝ) - Real.log ((fiberK π x (t.1 + 1)).card : ℝ)) := by
    intro π x
    rw [Fin.sum_univ_eq_sum_range
      (fun k => Real.log ((fiberK π x k).card : ℝ) - Real.log ((fiberK π x (k + 1)).card : ℝ))]
    rw [Finset.sum_range_sub' (fun k => Real.log ((fiberK π x k).card : ℝ)) n]
    have h0 : fiberK π x 0 = Finset.univ := by
      ext y; simp [fiberK]
    have hn_eq : fiberK π x n = {x} := by
      ext y
      simp only [fiberK, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro h
        apply Subtype.ext
        funext r
        have := h (π.symm r) (π.symm r).2
        simpa using this
      · rintro rfl s _; rfl
    rw [h0, hn_eq, Finset.card_univ, Finset.card_singleton]
    simp
  -- Step 2: Fiberwise Gibbs inequality
  have hgibbs : ∀ π : Equiv.Perm (Fin n), ∀ t : Fin n,
      ∑ x : Ω,
        (Real.log ((fiberK π x t.1).card : ℝ) - Real.log ((fiberK π x (t.1 + 1)).card : ℝ)) ≤
      ∑ x : Ω, Real.log ((avail π t x).card : ℝ) := by
    intro π t
    suffices hle : ∑ x : Ω,
        ((fiberK π x t.1).card : ℝ) /
          (((avail π t x).card : ℝ) * ((fiberK π x (t.1 + 1)).card : ℝ)) ≤
        (Fintype.card Ω : ℝ) by
      have hsub : ∑ x : Ω,
          ((Real.log ((fiberK π x t.1).card : ℝ) - Real.log ((fiberK π x (t.1 + 1)).card : ℝ)) -
            Real.log ((avail π t x).card : ℝ)) ≤ 0 := by
        calc ∑ x : Ω,
              ((Real.log ((fiberK π x t.1).card : ℝ) - Real.log ((fiberK π x (t.1 + 1)).card : ℝ)) -
                Real.log ((avail π t x).card : ℝ))
            = ∑ x : Ω, Real.log (((fiberK π x t.1).card : ℝ) /
                (((avail π t x).card : ℝ) * ((fiberK π x (t.1 + 1)).card : ℝ))) := by
              apply Finset.sum_congr rfl
              intro x _
              have h1 := (hcard_fiber_pos π x t.1).ne'
              have h2 := (hcard_fiber_pos π x (t.1 + 1)).ne'
              have h3 := (hcard_avail_pos π t x).ne'
              rw [Real.log_div h1 (mul_ne_zero h3 h2), Real.log_mul h3 h2]
              ring
          _ ≤ ∑ x : Ω, (((fiberK π x t.1).card : ℝ) /
                (((avail π t x).card : ℝ) * ((fiberK π x (t.1 + 1)).card : ℝ)) - 1) := by
              apply Finset.sum_le_sum
              intro x _
              exact Real.log_le_sub_one_of_pos
                (div_pos (hcard_fiber_pos π x t.1)
                  (mul_pos (hcard_avail_pos π t x) (hcard_fiber_pos π x (t.1 + 1))))
          _ = (∑ x : Ω, ((fiberK π x t.1).card : ℝ) /
                (((avail π t x).card : ℝ) * ((fiberK π x (t.1 + 1)).card : ℝ))) -
              (Fintype.card Ω : ℝ) := by
              rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
          _ ≤ 0 := by linarith
      rw [Finset.sum_sub_distrib] at hsub
      linarith
    -- Group by prefix function p : {s : Fin n // s < t} → Fin n
    let pref : Ω → ({s : Fin n // s < t} → Fin n) := fun x s => x.1 (π s.1)
    let img := (Finset.univ : Finset Ω).image pref
    rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := img) (g := pref)
      (fun x _ => Finset.mem_image_of_mem pref (Finset.mem_univ x))]
    have hcard_sum : (Fintype.card Ω : ℝ) =
        ∑ p ∈ img, ((Finset.univ.filter (fun x : Ω => pref x = p)).card : ℝ) := by
      have h := Finset.card_eq_sum_card_fiberwise (f := pref) (s := Finset.univ) (t := img)
        (fun x _ => Finset.mem_image_of_mem pref (Finset.mem_univ x))
      rw [Finset.card_univ] at h
      exact_mod_cast h
    rw [hcard_sum]
    apply Finset.sum_le_sum
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨x₀, _, rfl⟩
    let F : Finset Ω := Finset.univ.filter (fun y : Ω => pref y = pref x₀)
    have hF_eq : ∀ y ∈ F, fiberK π y t.1 = F := by
      intro y hy
      simp only [F, Finset.mem_filter, Finset.mem_univ, true_and] at hy
      ext z
      simp only [fiberK, F, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hz; funext s
        calc z.1 (π s.1) = y.1 (π s.1) := hz s.1 s.2
          _ = x₀.1 (π s.1) := congr_fun hy s
      · intro hz s hs
        calc z.1 (π s) = x₀.1 (π s) := congr_fun hz ⟨s, hs⟩
          _ = y.1 (π s) := (congr_fun hy ⟨s, hs⟩).symm
    have hA_eq : ∀ y ∈ F, avail π t y = avail π t x₀ := by
      intro y hy
      simp only [F, Finset.mem_filter, Finset.mem_univ, true_and] at hy
      ext j
      simp only [avail, Finset.mem_filter, Finset.mem_univ, true_and]
      apply forall_congr'; intro s
      apply imp_congr_right; intro hs
      have hxy : y.1 (π s) = x₀.1 (π s) := congr_fun hy ⟨s, hs⟩
      rw [hxy]
    have hmaps_A : ∀ y ∈ F, y.1 (π t) ∈ avail π t x₀ := by
      intro y hy
      rw [← hA_eq y hy]
      exact hmem_avail π t y
    change ∑ x ∈ F, ((fiberK π x t.1).card : ℝ) /
        (((avail π t x).card : ℝ) * ((fiberK π x (t.1 + 1)).card : ℝ)) ≤ (F.card : ℝ)
    rw [← Finset.sum_fiberwise_of_maps_to (s := F) (t := avail π t x₀)
      (g := fun y : Ω => y.1 (π t)) hmaps_A]
    have hinner : ∀ j ∈ avail π t x₀,
        ∑ x ∈ F.filter (fun y : Ω => y.1 (π t) = j),
          ((fiberK π x t.1).card : ℝ) /
            (((avail π t x).card : ℝ) * ((fiberK π x (t.1 + 1)).card : ℝ)) ≤
        (F.card : ℝ) / ((avail π t x₀).card : ℝ) := by
      intro j _
      set Fj := F.filter (fun y : Ω => y.1 (π t) = j)
      by_cases hFj : Fj.card = 0
      · rw [Finset.card_eq_zero.mp hFj, Finset.sum_empty]
        exact div_nonneg (Nat.cast_nonneg _) (hcard_avail_pos π t x₀).le
      · have hFj_eq : ∀ x ∈ Fj, fiberK π x (t.1 + 1) = Fj := by
          intro x hx
          have hxF : x ∈ F := (Finset.mem_filter.mp hx).1
          have hxj : x.1 (π t) = j := (Finset.mem_filter.mp hx).2
          ext z
          simp only [fiberK, Fj, F, Finset.mem_filter, Finset.mem_univ, true_and] at hxF ⊢
          constructor
          · intro hz
            refine ⟨?_, ?_⟩
            · funext s
              calc z.1 (π s.1) = x.1 (π s.1) := hz s.1 (Nat.lt_succ_of_lt s.2)
                _ = x₀.1 (π s.1) := congr_fun hxF s
            · calc z.1 (π t) = x.1 (π t) := hz t (Nat.lt_succ_self t.1)
                _ = j := hxj
          · rintro ⟨hzF, hzj⟩ s hs
            rcases Nat.lt_succ_iff_lt_or_eq.mp hs with hlt | heq
            · calc z.1 (π s) = x₀.1 (π s) := congr_fun hzF ⟨s, hlt⟩
                _ = x.1 (π s) := (congr_fun hxF ⟨s, hlt⟩).symm
            · have hs_eq : s = t := Fin.ext heq
              rw [hs_eq, hzj, hxj]
        have hterm : ∀ x ∈ Fj,
            ((fiberK π x t.1).card : ℝ) /
              (((avail π t x).card : ℝ) * ((fiberK π x (t.1 + 1)).card : ℝ)) =
            (F.card : ℝ) / (((avail π t x₀).card : ℝ) * (Fj.card : ℝ)) := by
          intro x hx
          have hxF : x ∈ F := (Finset.mem_filter.mp hx).1
          rw [hF_eq x hxF, hA_eq x hxF, hFj_eq x hx]
        rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
        have hFj_ne : (Fj.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hFj
        field_simp [hFj_ne, (hcard_avail_pos π t x₀).ne']
        exact le_rfl
    calc ∑ j ∈ avail π t x₀, ∑ x ∈ F.filter (fun y : Ω => y.1 (π t) = j),
            ((fiberK π x t.1).card : ℝ) /
              (((avail π t x).card : ℝ) * ((fiberK π x (t.1 + 1)).card : ℝ))
        ≤ ∑ _j ∈ avail π t x₀, (F.card : ℝ) / ((avail π t x₀).card : ℝ) :=
          Finset.sum_le_sum hinner
      _ = (F.card : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]
          field_simp [(hcard_avail_pos π t x₀).ne']
  -- Step 3: Exact sum of |avail π t x| over all π ∈ Perm (Fin n)
  have hsum_avail : ∀ x : Ω, ∀ t : Fin n,
      ∑ π : Equiv.Perm (Fin n), ((avail π t x).card : ℝ) =
        (n.factorial : ℝ) *
          (1 + ((n - 1 - t.1 : ℕ) : ℝ) * (((n - 1 - t.1 : ℕ) : ℝ) - 1) / ((n : ℝ) - 2)) := by
    intro x t
    have hnat : ∑ π : Equiv.Perm (Fin n), (avail π t x).card =
        n.factorial + (n - 1 - t.1) * (n - 1 - t.1 - 1) * (n * (n - 1) * (n - 3).factorial) := by
      -- Partition permutations by i = π t
      rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ)
        (g := fun π : Equiv.Perm (Fin n) => π t) (fun _ _ => Finset.mem_univ _)]
      have hrow : ∀ i : Fin n,
          ∑ π ∈ Finset.univ.filter (fun π : Equiv.Perm (Fin n) => π t = i), (avail π t x).card =
            (n - 1).factorial +
              (n - 1) * ((n - 1 - t.1) * (n - 1 - t.1 - 1) * (n - 3).factorial) := by
        intro i
        -- Rewrite card as sum of indicators over j : Fin n and swap sums
        have hswap : ∑ π ∈ Finset.univ.filter (fun π : Equiv.Perm (Fin n) => π t = i),
            (avail π t x).card =
            ∑ j : Fin n,
              (Finset.univ.filter (fun π : Equiv.Perm (Fin n) =>
                π t = i ∧ ∀ s : Fin n, s < t →
                  j ≠ x.1 (π s) ∧ L.mat i j ≠ L.mat (π s) (x.1 (π s)))).card := by
          simp_rw [avail, Finset.card_filter]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro π _
          by_cases hπ : π t = i <;> simp [hπ]
        rw [hswap]
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (x.1 i))]
        congr 1
        · -- Case j = x.1 i
          have hset : Finset.univ.filter (fun π : Equiv.Perm (Fin n) =>
              π t = i ∧ ∀ s : Fin n, s < t →
                x.1 i ≠ x.1 (π s) ∧ L.mat i (x.1 i) ≠ L.mat (π s) (x.1 (π s))) =
              Finset.univ.filter (fun π : Equiv.Perm (Fin n) => π t = i) := by
            ext π
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            constructor
            · exact And.left
            · intro hπ
              refine ⟨hπ, fun s hst => ?_⟩
              have hne : i ≠ π s := by
                rw [← hπ]; exact fun h => ne_of_gt hst (π.injective h)
              exact ⟨fun h => hne (x.2.1 h), fun h => hne (x.2.2 h)⟩
          rw [hset]
          exact card_perm_apply_eq (by omega) t i
        · -- Case j ≠ x.1 i
          have hterm : ∀ j ∈ Finset.univ.erase (x.1 i),
              (Finset.univ.filter (fun π : Equiv.Perm (Fin n) =>
                π t = i ∧ ∀ s : Fin n, s < t →
                  j ≠ x.1 (π s) ∧ L.mat i j ≠ L.mat (π s) (x.1 (π s)))).card =
              (n - 1 - t.1) * (n - 1 - t.1 - 1) * (n - 3).factorial := by
            intro j hj
            have hji : j ≠ x.1 i := (Finset.mem_erase.mp hj).1
            have hsurj1 : Function.Surjective x.1 := Finite.surjective_of_injective x.2.1
            have hsurj2 : Function.Surjective (fun r => L.mat r (x.1 r)) :=
              Finite.surjective_of_injective x.2.2
            obtain ⟨r₁, hr₁⟩ := hsurj1 j
            obtain ⟨r₂, hr₂⟩ := hsurj2 (L.mat i j)
            have hir₁ : i ≠ r₁ := fun h => hji (by rw [← hr₁, h])
            have hir₂ : i ≠ r₂ := fun h => hji (L.row_injective i (by rw [← hr₂, ← h]))
            have hr12 : r₁ ≠ r₂ := by
              intro h
              have hcol : L.mat r₁ j = L.mat i j := by
                calc L.mat r₁ j = L.mat r₁ (x.1 r₁) := by rw [hr₁]
                  _ = L.mat r₂ (x.1 r₂) := by rw [h]
                  _ = L.mat i j := hr₂
              exact hir₁ (L.col_injective j hcol).symm
            have hset : Finset.univ.filter (fun π : Equiv.Perm (Fin n) =>
                π t = i ∧ ∀ s : Fin n, s < t →
                  j ≠ x.1 (π s) ∧ L.mat i j ≠ L.mat (π s) (x.1 (π s))) =
                Finset.univ.filter (fun π : Equiv.Perm (Fin n) =>
                  π t = i ∧ ∀ s : Fin n, s < t → π s ≠ r₁ ∧ π s ≠ r₂) := by
              ext π
              simp only [Finset.mem_filter, Finset.mem_univ, true_and]
              apply and_congr_right; intro _
              apply forall_congr'; intro s
              apply imp_congr_right; intro _
              rw [← hr₂, ← hr₁]
              constructor
              · intro ⟨h1, h2⟩
                exact ⟨fun h => h1 (by rw [h]), fun h => h2 (by rw [h])⟩
              · intro ⟨h1, h2⟩
                exact ⟨fun h => h1 (x.2.1 h).symm, fun h => h2 (x.2.2 h).symm⟩
            rw [hset]
            exact card_perm_after hn t i r₁ r₂ hir₁ hir₂ hr12
          rw [Finset.sum_congr rfl hterm, Finset.sum_const,
            Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin,
            smul_eq_mul]
      simp_rw [hrow]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_add]
      have hfac : n * (n - 1).factorial = n.factorial := by
        cases n with
        | zero => omega
        | succ m => simp [Nat.factorial_succ]
      rw [hfac]
      ring
    have hcast : ∑ π : Equiv.Perm (Fin n), ((avail π t x).card : ℝ) =
        ((∑ π : Equiv.Perm (Fin n), (avail π t x).card : ℕ) : ℝ) := by
      rw [Nat.cast_sum]
    rw [hcast, hnat]
    set m := n - 1 - t.1
    have hm_cast : (m : ℝ) * ((m - 1 : ℕ) : ℝ) = (m : ℝ) * ((m : ℝ) - 1) := by
      generalize m = k
      cases k with
      | zero => simp
      | succ k => push_cast; ring
    have hfac3 : (n.factorial : ℝ) = (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) * ((n - 3).factorial : ℝ) := by
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
      simp only [Nat.add_sub_cancel, Nat.factorial_succ]
      push_cast
      ring
    have hn2 : ((n : ℝ) - 2) ≠ 0 := by
      have : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    push_cast
    rw [hm_cast]
    have hcast_n1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; norm_num
    rw [hcast_n1, hfac3]
    field_simp [hn2]
  -- Step 4: Jensen (log u ≤ u - 1) over π for each x, t
  have hjensen_pi : ∀ x : Ω, ∀ t : Fin n,
      ∑ π : Equiv.Perm (Fin n), Real.log ((avail π t x).card : ℝ) ≤
        (n.factorial : ℝ) *
          Real.log (1 + ((n - 1 - t.1 : ℕ) : ℝ) * (((n - 1 - t.1 : ℕ) : ℝ) - 1) / ((n : ℝ) - 2)) := by
    intro x t
    set m := n - 1 - t.1
    set μ : ℝ := 1 + (m : ℝ) * ((m : ℝ) - 1) / ((n : ℝ) - 2)
    have hμ_pos : 0 < μ := by
      have hden : (0 : ℝ) < (n : ℝ) - 2 := by
        have : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        linarith
      have hm_nn : (0 : ℝ) ≤ (m : ℝ) * ((m : ℝ) - 1) := by
        generalize m = k
        cases k with
        | zero => simp
        | succ k => push_cast; nlinarith
      positivity
    have hsub : ∑ π : Equiv.Perm (Fin n), (Real.log ((avail π t x).card : ℝ) - Real.log μ) ≤ 0 := by
      calc ∑ π : Equiv.Perm (Fin n), (Real.log ((avail π t x).card : ℝ) - Real.log μ)
          = ∑ π : Equiv.Perm (Fin n), Real.log (((avail π t x).card : ℝ) / μ) := by
            apply Finset.sum_congr rfl; intro π _
            rw [Real.log_div (hcard_avail_pos π t x).ne' hμ_pos.ne']
        _ ≤ ∑ π : Equiv.Perm (Fin n), (((avail π t x).card : ℝ) / μ - 1) := by
            apply Finset.sum_le_sum; intro π _
            exact Real.log_le_sub_one_of_pos (div_pos (hcard_avail_pos π t x) hμ_pos)
        _ = (∑ π : Equiv.Perm (Fin n), ((avail π t x).card : ℝ)) / μ - (n.factorial : ℝ) := by
            rw [Finset.sum_sub_distrib, ← Finset.sum_div, Finset.sum_const, Finset.card_univ,
              Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul, mul_one]
        _ = 0 := by
            rw [hsum_avail x t]
            field_simp [hμ_pos.ne']
            ring
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_perm,
      Fintype.card_fin, nsmul_eq_mul] at hsub
    linarith
  -- Step 5: Combine all sums and exponentiate
  have hlog_tot : (n.factorial : ℝ) * ((Fintype.card Ω : ℝ) * Real.log (Fintype.card Ω : ℝ)) ≤
      (Fintype.card Ω : ℝ) * ((n.factorial : ℝ) *
        ∑ t : Fin n,
          Real.log (1 + ((n - 1 - t.1 : ℕ) : ℝ) * (((n - 1 - t.1 : ℕ) : ℝ) - 1) / ((n : ℝ) - 2))) := by
    calc (n.factorial : ℝ) * ((Fintype.card Ω : ℝ) * Real.log (Fintype.card Ω : ℝ))
        = ∑ π : Equiv.Perm (Fin n), ∑ x : Ω, Real.log (Fintype.card Ω : ℝ) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
            nsmul_eq_mul]
      _ = ∑ π : Equiv.Perm (Fin n), ∑ x : Ω, ∑ t : Fin n,
            (Real.log ((fiberK π x t.1).card : ℝ) - Real.log ((fiberK π x (t.1 + 1)).card : ℝ)) := by
          apply Finset.sum_congr rfl; intro π _
          apply Finset.sum_congr rfl; intro x _
          exact htele π x
      _ = ∑ π : Equiv.Perm (Fin n), ∑ t : Fin n, ∑ x : Ω,
            (Real.log ((fiberK π x t.1).card : ℝ) - Real.log ((fiberK π x (t.1 + 1)).card : ℝ)) := by
          apply Finset.sum_congr rfl; intro π _; exact Finset.sum_comm
      _ ≤ ∑ π : Equiv.Perm (Fin n), ∑ t : Fin n, ∑ x : Ω, Real.log ((avail π t x).card : ℝ) := by
          apply Finset.sum_le_sum; intro π _
          apply Finset.sum_le_sum; intro t _
          exact hgibbs π t
      _ = ∑ x : Ω, ∑ t : Fin n, ∑ π : Equiv.Perm (Fin n), Real.log ((avail π t x).card : ℝ) := by
          rw [Finset.sum_comm]
          trans (∑ t : Fin n, ∑ x : Ω, ∑ π : Equiv.Perm (Fin n), Real.log ((avail π t x).card : ℝ))
          · apply Finset.sum_congr rfl; intro t _; exact Finset.sum_comm
          · exact Finset.sum_comm
      _ ≤ ∑ x : Ω, ∑ t : Fin n,
            (n.factorial : ℝ) *
              Real.log (1 + ((n - 1 - t.1 : ℕ) : ℝ) * (((n - 1 - t.1 : ℕ) : ℝ) - 1) / ((n : ℝ) - 2)) := by
          apply Finset.sum_le_sum; intro x _
          apply Finset.sum_le_sum; intro t _
          exact hjensen_pi x t
      _ = (Fintype.card Ω : ℝ) * ((n.factorial : ℝ) *
            ∑ t : Fin n,
              Real.log (1 + ((n - 1 - t.1 : ℕ) : ℝ) * (((n - 1 - t.1 : ℕ) : ℝ) - 1) / ((n : ℝ) - 2))) := by
          simp_rw [← Finset.mul_sum]
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          ring
  have hfac_pos : (0 : ℝ) < (n.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos n)
  have hlog_le : Real.log (Fintype.card Ω : ℝ) ≤
      ∑ t : Fin n,
        Real.log (1 + ((n - 1 - t.1 : ℕ) : ℝ) * (((n - 1 - t.1 : ℕ) : ℝ) - 1) / ((n : ℝ) - 2)) := by
    have hmul_pos : 0 < (n.factorial : ℝ) * (Fintype.card Ω : ℝ) := mul_pos hfac_pos hMposR
    nlinarith
  have hreindex : ∑ t : Fin n,
        Real.log (1 + ((n - 1 - t.1 : ℕ) : ℝ) * (((n - 1 - t.1 : ℕ) : ℝ) - 1) / ((n : ℝ) - 2)) =
      Real.log (radhaProd n) := by
    have hrev : ∑ t : Fin n,
          Real.log (1 + ((n - 1 - t.1 : ℕ) : ℝ) * (((n - 1 - t.1 : ℕ) : ℝ) - 1) / ((n : ℝ) - 2)) =
        ∑ t : Fin n,
          Real.log (1 + (t.1 : ℝ) * ((t.1 : ℝ) - 1) / ((n : ℝ) - 2)) := by
      let revE : Fin n ≃ Fin n := ⟨Fin.rev, Fin.rev, Fin.rev_rev, Fin.rev_rev⟩
      have hc := Equiv.sum_comp revE
        (fun t : Fin n => Real.log (1 + (t.1 : ℝ) * ((t.1 : ℝ) - 1) / ((n : ℝ) - 2)))
      rw [← hc]
      apply Finset.sum_congr rfl
      intro t _
      have hval : (revE t).1 = n - 1 - t.1 := by
        simp only [revE, Equiv.coe_fn_mk, Fin.val_rev]
        omega
      rw [hval]
    rw [hrev, Fin.sum_univ_eq_sum_range (fun m => Real.log (1 + (m : ℝ) * ((m : ℝ) - 1) / ((n : ℝ) - 2)))]
    unfold radhaProd
    rw [Real.log_prod]
    intro m _
    have hden : (0 : ℝ) < (n : ℝ) - 2 := by
      have : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    have hm_nn : (0 : ℝ) ≤ (m : ℝ) * ((m : ℝ) - 1) := by
      rcases m with _ | m
      · simp
      · push_cast; nlinarith
    positivity
  rw [hreindex] at hlog_le
  exact (Real.log_le_log_iff hMposR (radhaProd_pos hn)).mp hlog_le

/- ### Part 3: Sharp `n = 5` Upper Bound (`numTransversals L ≤ 15`) -/

private lemma numTransversals_le_15_of_five (L : LatinSquare 5) :
    numTransversals L ≤ 15 := by
  let Ω := {σ : Fin 5 → Fin 5 // IsTransversal L σ}
  let Pairs := {p : Fin 5 × Fin 5 // p.1 ≠ p.2 ∧ L.mat 0 p.1 ≠ L.mat 1 p.2}
  let Φ : Ω → Pairs := fun σ =>
    ⟨(σ.1 0, σ.1 1),
      fun h => (by decide : (0 : Fin 5) ≠ 1) (σ.2.1 h),
      fun h => (by decide : (0 : Fin 5) ≠ 1) (σ.2.2 h)⟩
  -- Step 1: |Pairs| = 15
  have hPairs : Fintype.card Pairs = 15 := by
    have hcard : Fintype.card Pairs =
        (Finset.univ.filter (fun p : Fin 5 × Fin 5 => p.1 ≠ p.2 ∧ L.mat 0 p.1 ≠ L.mat 1 p.2)).card := by
      rw [Fintype.card_subtype]
    rw [hcard]
    have hbi : Finset.univ.filter (fun p : Fin 5 × Fin 5 => p.1 ≠ p.2 ∧ L.mat 0 p.1 ≠ L.mat 1 p.2) =
        (Finset.univ : Finset (Fin 5)).biUnion (fun c₀ =>
          (Finset.univ.filter (fun c₁ : Fin 5 => c₀ ≠ c₁ ∧ L.mat 0 c₀ ≠ L.mat 1 c₁)).image
            (fun c₁ => (c₀, c₁))) := by
      ext ⟨c₀, c₁⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
        Finset.mem_image, Prod.mk.injEq]
      constructor
      · intro h; exact ⟨c₀, c₁, h, rfl, rfl⟩
      · rintro ⟨_, _, h, rfl, rfl⟩; exact h
    rw [hbi, Finset.card_biUnion]
    · have hrow : ∀ c₀ : Fin 5,
          ((Finset.univ.filter (fun c₁ : Fin 5 => c₀ ≠ c₁ ∧ L.mat 0 c₀ ≠ L.mat 1 c₁)).image
            (fun c₁ => (c₀, c₁))).card = 3 := by
        intro c₀
        rw [Finset.card_image_of_injective _ (fun _ _ h => by cases h; rfl)]
        obtain ⟨c', hc'⟩ := Finite.surjective_of_injective (L.row_injective 1) (L.mat 0 c₀)
        have hc'ne : c' ≠ c₀ := by
          intro h
          rw [h] at hc'
          exact (by decide : (1 : Fin 5) ≠ 0) (L.col_injective c₀ hc')
        have hset : Finset.univ.filter (fun c₁ : Fin 5 => c₀ ≠ c₁ ∧ L.mat 0 c₀ ≠ L.mat 1 c₁) =
            (Finset.univ.erase c₀).erase c' := by
          ext c₁
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_true, Finset.mem_erase]
          constructor
          · intro ⟨h1, h2⟩
            refine ⟨?_, h1.symm⟩
            intro hc1; apply h2; rw [hc1, hc']
          · intro ⟨h1, h2⟩
            refine ⟨h2.symm, ?_⟩
            intro h; apply h1
            exact L.row_injective 1 (h.symm.trans hc'.symm)
        rw [hset, Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hc'ne, Finset.mem_univ c'⟩),
          Finset.card_erase_of_mem (Finset.mem_univ c₀), Finset.card_univ, Fintype.card_fin]
      simp_rw [hrow]
      norm_num
    · intro a₁ _ a₂ _ ha
      dsimp [Function.onFun]
      rw [Finset.disjoint_left]
      intro p hp1 hp2
      simp only [Finset.mem_image] at hp1 hp2
      rcases hp1 with ⟨_, _, rfl⟩
      rcases hp2 with ⟨_, _, h⟩
      exact ha (by cases h; rfl)
  -- Step 2: Φ is injective
  have hInj : Function.Injective Φ := by
    intro σ τ hEq
    by_contra hne
    have h0 : σ.1 0 = τ.1 0 := congrArg (fun p : Pairs => p.1.1) hEq
    have h1 : σ.1 1 = τ.1 1 := congrArg (fun p : Pairs => p.1.2) hEq
    let c₀ := σ.1 0
    let c₁ := σ.1 1
    let s₀ := L.mat 0 c₀
    let s₁ := L.mat 1 c₁
    have hc01 : c₀ ≠ c₁ := fun h => (by decide : (0 : Fin 5) ≠ 1) (σ.2.1 h)
    have hs01 : s₀ ≠ s₁ := fun h => (by decide : (0 : Fin 5) ≠ 1) (σ.2.2 h)
    let R : Finset (Fin 5) := ((Finset.univ : Finset (Fin 5)).erase 0).erase 1
    let C : Finset (Fin 5) := ((Finset.univ : Finset (Fin 5)).erase c₀).erase c₁
    let S : Finset (Fin 5) := ((Finset.univ : Finset (Fin 5)).erase s₀).erase s₁
    have hRcard : R.card = 3 := by decide
    have hCcard : C.card = 3 := by
      rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hc01.symm, Finset.mem_univ c₁⟩),
        Finset.card_erase_of_mem (Finset.mem_univ c₀), Finset.card_univ, Fintype.card_fin]
    have hScard : S.card = 3 := by
      rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hs01.symm, Finset.mem_univ s₁⟩),
        Finset.card_erase_of_mem (Finset.mem_univ s₀), Finset.card_univ, Fintype.card_fin]
    let B : Finset (Fin 5 × Fin 5) :=
      Finset.univ.filter (fun p : Fin 5 × Fin 5 => p.1 ∈ R ∧ p.2 ∈ C ∧ L.mat p.1 p.2 ∈ S)
    -- Inclusion-exclusion in ℤ: B.card ≤ 5
    have hBcard : B.card ≤ 5 := by
      let a : Fin 5 × Fin 5 → ℤ := fun p => if p.1 ∈ R then 1 else 0
      let b : Fin 5 × Fin 5 → ℤ := fun p => if p.2 ∈ C then 1 else 0
      let c : Fin 5 × Fin 5 → ℤ := fun p => if L.mat p.1 p.2 ∈ S then 1 else 0
      have hid : ∀ p : Fin 5 × Fin 5,
          a p * b p * c p + (1 - a p) * (1 - b p) * (1 - c p) =
            1 - a p - b p - c p + a p * b p + a p * c p + b p * c p := fun p => by ring
      have hsum_id : ∑ p : Fin 5 × Fin 5, (a p * b p * c p + (1 - a p) * (1 - b p) * (1 - c p)) =
          ∑ p : Fin 5 × Fin 5, (1 - a p - b p - c p + a p * b p + a p * c p + b p * c p) :=
        Finset.sum_congr rfl (fun p _ => hid p)
      have h1_sum : (∑ _p : Fin 5 × Fin 5, (1 : ℤ)) = 25 := by decide
      have ha_sum : ∑ p : Fin 5 × Fin 5, a p = 15 := by
        rw [Fintype.sum_prod_type]
        have h1 : ∀ r : Fin 5, ∑ _col : Fin 5, a (r, _col) = if r ∈ R then 5 else 0 := by
          intro r; by_cases hr : r ∈ R <;> simp [a, hr]
        simp_rw [h1]
        rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, nsmul_eq_mul]
        have hfilt : Finset.univ.filter (fun r : Fin 5 => r ∈ R) = R := by ext; simp
        rw [hfilt, hRcard]; norm_num
      have hb_sum : ∑ p : Fin 5 × Fin 5, b p = 15 := by
        rw [Fintype.sum_prod_type_right]
        have h1 : ∀ col : Fin 5, ∑ _r : Fin 5, b (_r, col) = if col ∈ C then 5 else 0 := by
          intro col; by_cases hc : col ∈ C <;> simp [b, hc]
        simp_rw [h1]
        rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, nsmul_eq_mul]
        have hfilt : Finset.univ.filter (fun col : Fin 5 => col ∈ C) = C := by ext; simp
        rw [hfilt, hCcard]; norm_num
      have hrow_S : ∀ r : Fin 5, (Finset.univ.filter (fun col : Fin 5 => L.mat r col ∈ S)).card = 3 := by
        intro r
        let e : Fin 5 ≃ Fin 5 :=
          Equiv.ofBijective (L.mat r) (Finite.injective_iff_bijective.mp (L.row_injective r))
        have heq : (Finset.univ.filter (fun col : Fin 5 => L.mat r col ∈ S)).card = S.card := by
          refine Finset.card_bij (fun col _ => L.mat r col)
            (fun col hcol => (Finset.mem_filter.mp hcol).2)
            (fun _ _ _ _ h => L.row_injective r h) ?_
          intro s hs
          refine ⟨e.symm s, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, e.apply_symm_apply s⟩
          change e (e.symm s) ∈ S
          rw [e.apply_symm_apply]
          exact hs
        exact heq.trans hScard
      have hcol_S : ∀ col : Fin 5, (Finset.univ.filter (fun r : Fin 5 => L.mat r col ∈ S)).card = 3 := by
        intro col
        let e : Fin 5 ≃ Fin 5 :=
          Equiv.ofBijective (L.mat.transpose col)
            (Finite.injective_iff_bijective.mp (L.col_injective col))
        have heq : (Finset.univ.filter (fun r : Fin 5 => L.mat r col ∈ S)).card = S.card := by
          refine Finset.card_bij (fun r _ => L.mat r col)
            (fun r hr => (Finset.mem_filter.mp hr).2)
            (fun _ _ _ _ h => L.col_injective col h) ?_
          intro s hs
          refine ⟨e.symm s, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, e.apply_symm_apply s⟩
          change e (e.symm s) ∈ S
          rw [e.apply_symm_apply]
          exact hs
        exact heq.trans hScard
      have hc_sum : ∑ p : Fin 5 × Fin 5, c p = 15 := by
        rw [Fintype.sum_prod_type]
        have hrow_c : ∀ r : Fin 5, ∑ col : Fin 5, c (r, col) = 3 := by
          intro r; dsimp [c]; rw [Finset.sum_boole]; exact_mod_cast hrow_S r
        simp_rw [hrow_c]; norm_num
      have hab_sum : ∑ p : Fin 5 × Fin 5, a p * b p = 9 := by
        rw [Fintype.sum_prod_type]
        have h1 : ∀ r : Fin 5, ∑ col : Fin 5, a (r, col) * b (r, col) = if r ∈ R then 3 else 0 := by
          intro r
          by_cases hr : r ∈ R
          · simp only [a, hr, ↓reduceIte, one_mul, b, Finset.sum_boole]
            have hfilt : Finset.univ.filter (fun col : Fin 5 => col ∈ C) = C := by ext; simp
            rw [hfilt, hCcard]; norm_num
          · simp [a, hr]
        simp_rw [h1]
        rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, nsmul_eq_mul]
        have hfilt : Finset.univ.filter (fun r : Fin 5 => r ∈ R) = R := by ext; simp
        rw [hfilt, hRcard]; norm_num
      have hac_sum : ∑ p : Fin 5 × Fin 5, a p * c p = 9 := by
        rw [Fintype.sum_prod_type]
        have hrow_ac : ∀ r : Fin 5, ∑ col : Fin 5, a (r, col) * c (r, col) =
            if r ∈ R then 3 else 0 := by
          intro r
          by_cases hr : r ∈ R
          · simp only [a, hr, ↓reduceIte, one_mul]
            dsimp [c]; rw [Finset.sum_boole]; exact_mod_cast hrow_S r
          · simp [a, hr]
        simp_rw [hrow_ac]
        rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, nsmul_eq_mul]
        have hfilt : Finset.univ.filter (fun r : Fin 5 => r ∈ R) = R := by ext; simp
        rw [hfilt, hRcard]; norm_num
      have hbc_sum : ∑ p : Fin 5 × Fin 5, b p * c p = 9 := by
        rw [Fintype.sum_prod_type_right]
        have hcol_bc : ∀ col : Fin 5, ∑ r : Fin 5, b (r, col) * c (r, col) =
            if col ∈ C then 3 else 0 := by
          intro col
          by_cases hc : col ∈ C
          · simp only [b, hc, ↓reduceIte, one_mul]
            dsimp [c]; rw [Finset.sum_boole]; exact_mod_cast hcol_S col
          · simp [b, hc]
        simp_rw [hcol_bc]
        rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, nsmul_eq_mul]
        have hfilt : Finset.univ.filter (fun col : Fin 5 => col ∈ C) = C := by ext; simp
        rw [hfilt, hCcard]; norm_num
      have hB_eq : (B.card : ℤ) = ∑ p : Fin 5 × Fin 5, a p * b p * c p := by
        have hterm : ∀ p : Fin 5 × Fin 5,
            a p * b p * c p = if p ∈ B then (1 : ℤ) else 0 := by
          intro p
          by_cases h1 : p.1 ∈ R <;> by_cases h2 : p.2 ∈ C <;> by_cases h3 : L.mat p.1 p.2 ∈ S <;>
            simp [a, b, c, B, h1, h2, h3]
        simp_rw [hterm, Finset.sum_boole]
        have hfilt : Finset.univ.filter (fun p : Fin 5 × Fin 5 => p ∈ B) = B := by ext; simp
        rw [hfilt]
      have hA0_ge2 : (2 : ℤ) ≤ ∑ p : Fin 5 × Fin 5, (1 - a p) * (1 - b p) * (1 - c p) := by
        have hnn : ∀ p : Fin 5 × Fin 5, 0 ≤ (1 - a p) * (1 - b p) * (1 - c p) := by
          intro p
          by_cases h1 : p.1 ∈ R <;> by_cases h2 : p.2 ∈ C <;> by_cases h3 : L.mat p.1 p.2 ∈ S <;>
            simp [a, b, c, h1, h2, h3]
        have hsub : ({((0 : Fin 5), c₀), ((1 : Fin 5), c₁)} : Finset (Fin 5 × Fin 5)) ⊆ Finset.univ :=
          Finset.subset_univ _
        have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => hnn p)
        have hne_pair : ((0 : Fin 5), c₀) ≠ ((1 : Fin 5), c₁) := by
          intro h; exact (by decide : (0 : Fin 5) ≠ 1) (Prod.mk.inj h).1
        rw [Finset.sum_pair hne_pair] at hle
        have hv0 : (1 - a (0, c₀)) * (1 - b (0, c₀)) * (1 - c (0, c₀)) = 1 := by
          have hr0 : (0 : Fin 5) ∉ R := by simp [R]
          have hc0 : c₀ ∉ C := by simp [C]
          have hs0 : L.mat 0 c₀ ∉ S := by simp [S, s₀]
          simp [a, b, c, hr0, hc0, hs0]
        have hv1 : (1 - a (1, c₁)) * (1 - b (1, c₁)) * (1 - c (1, c₁)) = 1 := by
          have hr1 : (1 : Fin 5) ∉ R := by simp [R]
          have hc1 : c₁ ∉ C := by simp [C]
          have hs1 : L.mat 1 c₁ ∉ S := by simp [S, s₁]
          simp [a, b, c, hr1, hc1, hs1]
        linarith
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
        Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
        Finset.sum_sub_distrib] at hsum_id
      rw [h1_sum, ha_sum, hb_sum, hc_sum, hab_sum, hac_sum, hbc_sum, ← hB_eq] at hsum_id
      omega
    -- Pigeonhole: σ and τ must agree on some r₀ ∈ R
    let Pσ : Finset (Fin 5 × Fin 5) := R.image (fun r => (r, σ.1 r))
    let Pτ : Finset (Fin 5 × Fin 5) := R.image (fun r => (r, τ.1 r))
    have hPσ_sub : Pσ ⊆ B := by
      intro p hp
      rcases Finset.mem_image.mp hp with ⟨r, hr, rfl⟩
      have hr0 : r ≠ 0 := (Finset.mem_erase.mp (Finset.mem_erase.mp hr).2).1
      have hr1 : r ≠ 1 := (Finset.mem_erase.mp hr).1
      simp only [B, C, S, Finset.mem_filter, Finset.mem_univ, true_and, and_true, Finset.mem_erase]
      exact ⟨hr, ⟨fun h => hr1 (σ.2.1 h), fun h => hr0 (σ.2.1 h)⟩,
        ⟨fun h => hr1 (σ.2.2 h), fun h => hr0 (σ.2.2 h)⟩⟩
    have hPτ_sub : Pτ ⊆ B := by
      intro p hp
      rcases Finset.mem_image.mp hp with ⟨r, hr, rfl⟩
      have hr0 : r ≠ 0 := (Finset.mem_erase.mp (Finset.mem_erase.mp hr).2).1
      have hr1 : r ≠ 1 := (Finset.mem_erase.mp hr).1
      simp only [B, C, S, Finset.mem_filter, Finset.mem_univ, true_and, and_true, Finset.mem_erase]
      refine ⟨hr, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
      · intro h; exact hr1 (τ.2.1 (h.trans h1))
      · intro h; exact hr0 (τ.2.1 (h.trans h0))
      · intro h; apply hr1; apply τ.2.2; dsimp only; rw [h]; dsimp only [s₁, c₁]; rw [h1]
      · intro h; apply hr0; apply τ.2.2; dsimp only; rw [h]; dsimp only [s₀, c₀]; rw [h0]
    have hPσ_card : Pσ.card = 3 := by
      rw [Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).1), hRcard]
    have hPτ_card : Pτ.card = 3 := by
      rw [Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).1), hRcard]
    have hinter_pos : 0 < (Pσ ∩ Pτ).card := by
      have hunion : (Pσ ∪ Pτ).card ≤ 5 :=
        le_trans (Finset.card_le_card (Finset.union_subset hPσ_sub hPτ_sub)) hBcard
      have hadd := Finset.card_union_add_card_inter Pσ Pτ
      omega
    obtain ⟨p₀, hp₀⟩ := Finset.card_pos.mp hinter_pos
    rcases Finset.mem_image.mp (Finset.mem_inter.mp hp₀).1 with ⟨r₀, hr₀R, rfl⟩
    rcases Finset.mem_image.mp (Finset.mem_inter.mp hp₀).2 with ⟨r₀', _, hpair⟩
    have hr₀_eq : σ.1 r₀ = τ.1 r₀ := by
      have hfst : r₀' = r₀ := (Prod.mk.inj hpair).1
      have hsnd : τ.1 r₀' = σ.1 r₀ := (Prod.mk.inj hpair).2
      rw [hfst] at hsnd
      exact hsnd.symm
    have hr₀0 : r₀ ≠ 0 := (Finset.mem_erase.mp (Finset.mem_erase.mp hr₀R).2).1
    have hr₀1 : r₀ ≠ 1 := (Finset.mem_erase.mp hr₀R).1
    -- Pick r₁ where σ r₁ ≠ τ r₁
    have hex_r1 : ∃ r₁ : Fin 5, σ.1 r₁ ≠ τ.1 r₁ := by
      by_contra hall
      push Not at hall
      exact hne (Subtype.ext (funext hall))
    obtain ⟨r₁, hr₁_diff⟩ := hex_r1
    have hr₁0 : r₁ ≠ 0 := fun h => hr₁_diff (by rw [h, h0])
    have hr₁1 : r₁ ≠ 1 := fun h => hr₁_diff (by rw [h, h1])
    have hr₁r₀ : r₁ ≠ r₀ := fun h => hr₁_diff (by rw [h, hr₀_eq])
    -- Find r₂ with σ r₂ = τ r₁
    obtain ⟨r₂, hr₂⟩ := Finite.surjective_of_injective σ.2.1 (τ.1 r₁)
    have hr₂0 : r₂ ≠ 0 := fun h => hr₁0 (τ.2.1 (hr₂.symm.trans (by rw [h, h0])))
    have hr₂1 : r₂ ≠ 1 := fun h => hr₁1 (τ.2.1 (hr₂.symm.trans (by rw [h, h1])))
    have hr₂r₀ : r₂ ≠ r₀ := fun h => hr₁r₀ (τ.2.1 (hr₂.symm.trans (by rw [h, hr₀_eq])))
    have hr₂r₁ : r₂ ≠ r₁ := fun h => hr₁_diff (by rw [← hr₂, h])
    -- Find r' with L.mat r' (σ r') = L.mat r₁ (τ r₁)
    obtain ⟨r', hr'⟩ := Finite.surjective_of_injective σ.2.2 (L.mat r₁ (τ.1 r₁))
    dsimp only at hr'
    have hr'0 : r' ≠ 0 := by
      intro h; apply hr₁0; apply τ.2.2; dsimp only; rw [← hr', h, h0]
    have hr'1 : r' ≠ 1 := by
      intro h; apply hr₁1; apply τ.2.2; dsimp only; rw [← hr', h, h1]
    have hr'r₀ : r' ≠ r₀ := by
      intro h; apply hr₁r₀; apply τ.2.2; dsimp only; rw [← hr', h, hr₀_eq]
    -- Since Fin 5 \ {0, 1, r₀} has size 2, r' must be r₁ or r₂
    have hr'_or : r' = r₁ ∨ r' = r₂ := by
      have hcard2 : (R.erase r₀).card = 2 := by
        rw [Finset.card_erase_of_mem hr₀R, hRcard]
      have hsub2 : ({r₁, r₂} : Finset (Fin 5)) ⊆ R.erase r₀ := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact Finset.mem_erase.mpr ⟨hr₁r₀, Finset.mem_erase.mpr ⟨hr₁1, Finset.mem_erase.mpr ⟨hr₁0, Finset.mem_univ _⟩⟩⟩
        · exact Finset.mem_erase.mpr ⟨hr₂r₀, Finset.mem_erase.mpr ⟨hr₂1, Finset.mem_erase.mpr ⟨hr₂0, Finset.mem_univ _⟩⟩⟩
      have heq2 : ({r₁, r₂} : Finset (Fin 5)) = R.erase r₀ :=
        Finset.eq_of_subset_of_card_le hsub2 (by rw [Finset.card_pair hr₂r₁.symm, hcard2])
      have hr'mem : r' ∈ R.erase r₀ :=
        Finset.mem_erase.mpr ⟨hr'r₀, Finset.mem_erase.mpr ⟨hr'1, Finset.mem_erase.mpr ⟨hr'0, Finset.mem_univ _⟩⟩⟩
      rw [← heq2, Finset.mem_insert, Finset.mem_singleton] at hr'mem
      exact hr'mem
    rcases hr'_or with hr'1_eq | hr'2_eq
    · -- r' = r₁: L.mat r₁ (σ r₁) = L.mat r₁ (τ r₁) contradicts row_injective
      rw [hr'1_eq] at hr'
      exact hr₁_diff (L.row_injective r₁ hr')
    · -- r' = r₂: L.mat r₂ (σ r₂) = L.mat r₁ (τ r₁) = L.mat r₁ (σ r₂) contradicts col_injective
      rw [hr'2_eq, ← hr₂] at hr'
      exact hr₂r₁ (L.col_injective (σ.1 r₂) hr')
  calc numTransversals L = Fintype.card Ω := rfl
    _ ≤ Fintype.card Pairs := Fintype.card_le_of_injective Φ hInj
    _ = 15 := hPairs

private lemma fifteen_le_target5 :
    (15 : ℝ) ≤ cConst ^ 5 * Real.sqrt (5 : ℕ) * (Nat.factorial 5 : ℝ) := by
  have hc := cConst_ge_613
  have hpow : (613 / 1000 : ℝ) ^ 5 ≤ cConst ^ 5 := pow_le_pow_left₀ (by norm_num) hc 5
  have hfac5 : (Nat.factorial 5 : ℝ) = 120 := by norm_num [Nat.factorial]
  have h5 : (15 : ℝ) ≤ (613 / 1000 : ℝ) ^ 5 * Real.sqrt (5 : ℕ) * 120 := by
    have hsq : (15 : ℝ) ^ 2 ≤ ((613 / 1000 : ℝ) ^ 5 * Real.sqrt (5 : ℕ) * 120) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ (5 : ℕ))]
      norm_num
    have hrhs_nn : 0 ≤ (613 / 1000 : ℝ) ^ 5 * Real.sqrt (5 : ℕ) * 120 := by positivity
    nlinarith
  have hmul_nn : 0 ≤ Real.sqrt (5 : ℕ) * 120 := by positivity
  rw [hfac5]
  calc (15 : ℝ) ≤ (613 / 1000 : ℝ) ^ 5 * Real.sqrt (5 : ℕ) * 120 := h5
    _ = (613 / 1000 : ℝ) ^ 5 * (Real.sqrt (5 : ℕ) * 120) := by ring
    _ ≤ cConst ^ 5 * (Real.sqrt (5 : ℕ) * 120) := mul_le_mul_of_nonneg_right hpow hmul_nn
    _ = cConst ^ 5 * Real.sqrt (5 : ℕ) * 120 := by ring

/- ### Part 4: Master Upper Bound for `T n` (`n ≥ 5`) -/

theorem upper_bound_T :
    ∀ n : ℕ, n ≥ 5 →
      (LatinSquare.T n : ℝ) ≤ cConst ^ n * Real.sqrt n * (n.factorial : ℝ) := by
  intro n hn
  have hper : ∀ L : LatinSquare n,
      (numTransversals L : ℝ) ≤ cConst ^ n * Real.sqrt n * (n.factorial : ℝ) := by
    intro L
    by_cases hn5 : n = 5
    · subst hn5
      exact le_trans (by exact_mod_cast numTransversals_le_15_of_five L) fifteen_le_target5
    · exact le_trans (numTransversals_le_radhaProd (by omega) L) (radhaProd_le_target (by omega))
  have hpos : (0 : ℝ) ≤ cConst ^ n * Real.sqrt n * (n.factorial : ℝ) := by
    have := cConst_ge_613
    positivity
  unfold LatinSquare.T
  by_cases hne : (Finset.univ : Finset (LatinSquare n)).Nonempty
  · obtain ⟨L, _, hL⟩ := Finset.exists_mem_eq_sup Finset.univ hne (fun L => numTransversals L)
    rw [hL]
    exact hper L
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.sup_empty]
    simpa using hpos

end StrategyCUpper

namespace StrategyCLower

open Finset

/- ### Piece 0: Basic Infrastructure & Transport -/

private def cyclicLS (n : ℕ) : LatinSquare n where
  mat := Matrix.of (fun i j : Fin n => i + j)
  row_injective := fun _ _ _ h => by simp only [Matrix.of_apply] at h; exact add_left_cancel h
  col_injective := fun _ _ _ h => by
    simp only [Matrix.transpose_apply, Matrix.of_apply] at h; exact add_right_cancel h

private lemma numTransversals_le_T {n : ℕ} (L : LatinSquare n) :
    numTransversals L ≤ LatinSquare.T n :=
  Finset.le_sup (f := fun L : LatinSquare n => numTransversals L) (Finset.mem_univ L)

private lemma exists_latinSquare_eq_T (n : ℕ) :
    ∃ L : LatinSquare n, numTransversals L = LatinSquare.T n := by
  obtain ⟨L, _, hL⟩ := Finset.exists_mem_eq_sup Finset.univ
    ⟨cyclicLS n, Finset.mem_univ (cyclicLS n)⟩ (fun L => numTransversals L)
  exact ⟨L, hL.symm⟩

private def latinSquareOfEquiv {α : Type*} {n : ℕ} (e : Fin n ≃ α) (f : α → α → α)
    (hrow : ∀ a, Function.Injective (f a))
    (hcol : ∀ b, Function.Injective (fun a => f a b)) : LatinSquare n where
  mat := Matrix.of (fun i j => e.symm (f (e i) (e j)))
  row_injective := fun i j₁ j₂ h => by
    simp only [Matrix.of_apply] at h
    exact e.injective (hrow (e i) (e.symm.injective h))
  col_injective := fun j i₁ i₂ h => by
    simp only [Matrix.transpose_apply, Matrix.of_apply] at h
    exact e.injective (hcol (e j) (e.symm.injective h))

private lemma card_le_T_of_family {α ι : Type*} [Fintype ι] {n : ℕ}
    (e : Fin n ≃ α) (f : α → α → α)
    (hrow : ∀ a, Function.Injective (f a))
    (hcol : ∀ b, Function.Injective (fun a => f a b))
    (φ : ι → (α → α)) (hinj : Function.Injective φ)
    (htrans : ∀ k, Function.Injective (φ k) ∧ Function.Injective (fun a => f a (φ k a))) :
    Fintype.card ι ≤ LatinSquare.T n := by
  let L := latinSquareOfEquiv e f hrow hcol
  let ψ : ι → {σ : Fin n → Fin n // IsTransversal L σ} := fun k =>
    ⟨fun i => e.symm (φ k (e i)),
      e.symm.injective.comp ((htrans k).1.comp e.injective),
      by
        intro i₁ i₂ h
        simp only [L, latinSquareOfEquiv, Matrix.of_apply, Equiv.apply_symm_apply] at h
        exact e.injective ((htrans k).2 (e.symm.injective h))⟩
  have hψ : Function.Injective ψ := by
    intro k₁ k₂ h
    apply hinj
    funext a
    have hi := congr_fun (congrArg Subtype.val h) (e.symm a)
    simp only [ψ, Equiv.apply_symm_apply] at hi
    exact e.symm.injective hi
  exact le_trans (Fintype.card_le_of_injective ψ hψ) (numTransversals_le_T L)

private def finEquivZMod (m : ℕ) [NeZero m] : Fin m ≃ ZMod m where
  toFun i := (i.1 : ZMod m)
  invFun z := ⟨z.val, z.val_lt⟩
  left_inv i := Fin.ext (ZMod.val_natCast_of_lt i.2)
  right_inv z := ZMod.natCast_zmod_val z

/- ### Piece 1: Direct (Kronecker) Product -/

private lemma T_mul_ge {a b : ℕ} (hb : 0 < b) :
    LatinSquare.T a * LatinSquare.T b ^ a ≤ LatinSquare.T (a * b) := by
  obtain ⟨L, hL⟩ := exists_latinSquare_eq_T a
  obtain ⟨M, hM⟩ := exists_latinSquare_eq_T b
  let ΩL := {σ : Fin a → Fin a // IsTransversal L σ}
  let ΩM := {τ : Fin b → Fin b // IsTransversal M τ}
  let f : (Fin a × Fin b) → (Fin a × Fin b) → (Fin a × Fin b) :=
    fun p q => (L.mat p.1 q.1, M.mat p.2 q.2)
  have hrow : ∀ p, Function.Injective (f p) := fun p q₁ q₂ h =>
    Prod.ext (L.row_injective p.1 (Prod.mk.inj h).1) (M.row_injective p.2 (Prod.mk.inj h).2)
  have hcol : ∀ q, Function.Injective (fun p => f p q) := fun q p₁ p₂ h =>
    Prod.ext (L.col_injective q.1 (Prod.mk.inj h).1) (M.col_injective q.2 (Prod.mk.inj h).2)
  let φ : (ΩL × (Fin a → ΩM)) → ((Fin a × Fin b) → (Fin a × Fin b)) :=
    fun ⟨σ, τ⟩ ⟨i, j⟩ => (σ.1 i, (τ i).1 j)
  have hinj : Function.Injective φ := by
    intro ⟨σ₁, τ₁⟩ ⟨σ₂, τ₂⟩ h
    have hσ : σ₁ = σ₂ := by
      apply Subtype.ext; funext i
      exact (Prod.mk.inj (congr_fun h (i, ⟨0, hb⟩))).1
    have hτ : τ₁ = τ₂ := by
      funext i; apply Subtype.ext; funext j
      exact (Prod.mk.inj (congr_fun h (i, j))).2
    exact Prod.ext hσ hτ
  have htrans : ∀ k : ΩL × (Fin a → ΩM),
      Function.Injective (φ k) ∧ Function.Injective (fun p => f p (φ k p)) := by
    rintro ⟨σ, τ⟩
    refine ⟨?_, ?_⟩
    · intro ⟨i₁, j₁⟩ ⟨i₂, j₂⟩ h
      have hi : i₁ = i₂ := σ.2.1 (Prod.mk.inj h).1
      subst hi
      exact Prod.ext rfl ((τ i₁).2.1 (Prod.mk.inj h).2)
    · intro ⟨i₁, j₁⟩ ⟨i₂, j₂⟩ h
      have hi : i₁ = i₂ := σ.2.2 (Prod.mk.inj h).1
      subst hi
      exact Prod.ext rfl ((τ i₁).2.2 (Prod.mk.inj h).2)
  have hle := card_le_T_of_family finProdFinEquiv.symm f hrow hcol φ hinj htrans
  simp only [Fintype.card_prod, Fintype.card_pi, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin] at hle
  change numTransversals L * numTransversals M ^ a ≤ LatinSquare.T (a * b) at hle
  rwa [hL, hM] at hle

/- ### Piece 2: Singular Direct Product -/

private lemma singular_direct_product {k q r : ℕ} (hq : 0 < q)
    (A : LatinSquare k) (hidem : ∀ a : Fin k, A.mat a a = a)
    (D : Finset (Fin k → Fin k))
    (hD : ∀ α ∈ D, IsTransversal A α ∧ ∀ a : Fin k, α a ≠ a)
    (L : LatinSquare q) (R : LatinSquare r)
    (h : (Fin q ⊕ Fin r) → (Fin q ⊕ Fin r) → (Fin q ⊕ Fin r))
    (hrow_h : ∀ x, Function.Injective (h x))
    (hcol_h : ∀ y, Function.Injective (fun x => h x y))
    (hsub : ∀ u v : Fin r, h (Sum.inr u) (Sum.inr v) = Sum.inr (R.mat u v)) :
    D.card * (numTransversals L) ^ k * numTransversals R ≤ LatinSquare.T (k * q + r) := by
  let α := (Fin k × Fin q) ⊕ Fin r
  let e : Fin (k * q + r) ≃ α :=
    finSumFinEquiv.symm.trans (Equiv.sumCongr finProdFinEquiv.symm (Equiv.refl (Fin r)))
  let embedA : Fin k → (Fin q ⊕ Fin r) → α := fun a z =>
    match z with
    | Sum.inl s => Sum.inl (a, s)
    | Sum.inr w => Sum.inr w
  have hembed_inj : ∀ a, Function.Injective (embedA a) := by
    intro a z₁ z₂ hz
    cases z₁ <;> cases z₂ <;> simp only [embedA] at hz
    · cases hz; rfl
    · cases hz
    · cases hz
    · cases hz; rfl
  have h_inl_inr : ∀ (x : Fin q) (v : Fin r), ∃ s : Fin q, h (Sum.inl x) (Sum.inr v) = Sum.inl s := by
    intro x v
    cases hv : h (Sum.inl x) (Sum.inr v) with
    | inl s => exact ⟨s, rfl⟩
    | inr w =>
      exfalso
      obtain ⟨u, hu⟩ := Finite.surjective_of_injective (R.col_injective v) w
      simp only [Matrix.transpose_apply] at hu
      have heq : h (Sum.inl x) (Sum.inr v) = h (Sum.inr u) (Sum.inr v) := by
        rw [hv, hsub u v, hu]
      exact Sum.inl_ne_inr (hcol_h (Sum.inr v) heq)
  have h_inr_inl : ∀ (u : Fin r) (y : Fin q), ∃ s : Fin q, h (Sum.inr u) (Sum.inl y) = Sum.inl s := by
    intro u y
    cases hu : h (Sum.inr u) (Sum.inl y) with
    | inl s => exact ⟨s, rfl⟩
    | inr w =>
      exfalso
      obtain ⟨v, hv⟩ := Finite.surjective_of_injective (R.row_injective u) w
      have heq : h (Sum.inr u) (Sum.inl y) = h (Sum.inr u) (Sum.inr v) := by
        rw [hu, hsub u v, hv]
      exact Sum.inl_ne_inr (hrow_h (Sum.inr u) heq)
  let f : α → α → α := fun p₁ p₂ =>
    match p₁, p₂ with
    | Sum.inr u, Sum.inr v => Sum.inr (R.mat u v)
    | Sum.inl (a, x), Sum.inr v => embedA a (h (Sum.inl x) (Sum.inr v))
    | Sum.inr u, Sum.inl (b, y) => embedA b (h (Sum.inr u) (Sum.inl y))
    | Sum.inl (a, x), Sum.inl (b, y) =>
        if a = b then embedA a (h (Sum.inl x) (Sum.inl y))
        else Sum.inl (A.mat a b, L.mat x y)
  have hrow_f : ∀ p₁, Function.Injective (f p₁) := by
    intro p₁ p₂ p₂' heq
    cases p₁ with
    | inr u =>
      cases p₂ with
      | inr v =>
        cases p₂' with
        | inr v' =>
          simp only [f] at heq
          exact congrArg Sum.inr (R.row_injective u (Sum.inr.inj heq))
        | inl by' =>
          rcases by' with ⟨b', y'⟩
          obtain ⟨s', hs'⟩ := h_inr_inl u y'
          simp only [f, hs', embedA] at heq
          cases heq
      | inl by1 =>
        rcases by1 with ⟨b, y⟩
        obtain ⟨s, hs⟩ := h_inr_inl u y
        cases p₂' with
        | inr v' =>
          simp only [f, hs, embedA] at heq
          cases heq
        | inl by2 =>
          rcases by2 with ⟨b', y'⟩
          obtain ⟨s', hs'⟩ := h_inr_inl u y'
          simp only [f, hs, hs', embedA] at heq
          have hb : b = b' := (Prod.mk.inj (Sum.inl.inj heq)).1
          have hss : s = s' := (Prod.mk.inj (Sum.inl.inj heq)).2
          have hy : y = y' := Sum.inl.inj (hrow_h (Sum.inr u) (hs.trans (by rw [hss, ← hs'])))
          rw [hb, hy]
    | inl ax =>
      rcases ax with ⟨a, x⟩
      have h_off_ne : ∀ (b : Fin k) (z : Fin q ⊕ Fin r) (y : Fin q),
          a ≠ b → embedA a z ≠ Sum.inl (A.mat a b, L.mat x y) := by
        intro b z y hab hz
        cases z with
        | inr w => simp only [embedA] at hz; cases hz
        | inl s =>
          simp only [embedA] at hz
          have ha : a = A.mat a b := (Prod.mk.inj (Sum.inl.inj hz)).1
          exact hab (A.row_injective a ((hidem a).trans ha))
      cases p₂ with
      | inr v =>
        cases p₂' with
        | inr v' =>
          simp only [f] at heq
          exact congrArg Sum.inr (Sum.inr.inj (hrow_h (Sum.inl x) (hembed_inj a heq)))
        | inl by' =>
          rcases by' with ⟨b', y'⟩
          simp only [f] at heq
          by_cases hab' : a = b'
          · rw [if_pos hab'] at heq
            exact absurd (hrow_h (Sum.inl x) (hembed_inj a heq)) Sum.inr_ne_inl
          · rw [if_neg hab'] at heq
            exact absurd heq (h_off_ne b' _ y' hab')
      | inl by1 =>
        rcases by1 with ⟨b, y⟩
        cases p₂' with
        | inr v' =>
          simp only [f] at heq
          by_cases hab : a = b
          · rw [if_pos hab] at heq
            exact absurd (hrow_h (Sum.inl x) (hembed_inj a heq)) Sum.inl_ne_inr
          · rw [if_neg hab] at heq
            exact absurd heq.symm (h_off_ne b _ y hab)
        | inl by2 =>
          rcases by2 with ⟨b', y'⟩
          simp only [f] at heq
          by_cases hab : a = b <;> by_cases hab' : a = b'
          · rw [if_pos hab, if_pos hab'] at heq
            have hy : y = y' := Sum.inl.inj (hrow_h (Sum.inl x) (hembed_inj a heq))
            rw [← hab, hab', hy]
          · rw [if_pos hab, if_neg hab'] at heq
            exact absurd heq (h_off_ne b' _ y' hab')
          · rw [if_neg hab, if_pos hab'] at heq
            exact absurd heq.symm (h_off_ne b _ y hab)
          · rw [if_neg hab, if_neg hab'] at heq
            have h1 := (Prod.mk.inj (Sum.inl.inj heq)).1
            have h2 := (Prod.mk.inj (Sum.inl.inj heq)).2
            rw [A.row_injective a h1, L.row_injective x h2]
  have hcol_f : ∀ p₂, Function.Injective (fun p₁ => f p₁ p₂) := by
    intro p₂ p₁ p₁' heq
    cases p₂ with
    | inr v =>
      cases p₁ with
      | inr u =>
        cases p₁' with
        | inr u' =>
          simp only [f] at heq
          exact congrArg Sum.inr (R.col_injective v (Sum.inr.inj heq))
        | inl ax' =>
          rcases ax' with ⟨a', x'⟩
          obtain ⟨s', hs'⟩ := h_inl_inr x' v
          simp only [f, hs', embedA] at heq
          cases heq
      | inl ax1 =>
        rcases ax1 with ⟨a, x⟩
        obtain ⟨s, hs⟩ := h_inl_inr x v
        cases p₁' with
        | inr u' =>
          simp only [f, hs, embedA] at heq
          cases heq
        | inl ax2 =>
          rcases ax2 with ⟨a', x'⟩
          obtain ⟨s', hs'⟩ := h_inl_inr x' v
          simp only [f, hs, hs', embedA] at heq
          have ha : a = a' := (Prod.mk.inj (Sum.inl.inj heq)).1
          have hss : s = s' := (Prod.mk.inj (Sum.inl.inj heq)).2
          have hx : x = x' := Sum.inl.inj (hcol_h (Sum.inr v) (hs.trans (by rw [hss, ← hs'])))
          rw [ha, hx]
    | inl by2 =>
      rcases by2 with ⟨b, y⟩
      have h_off_ne : ∀ (a : Fin k) (z : Fin q ⊕ Fin r) (x : Fin q),
          a ≠ b → embedA b z ≠ Sum.inl (A.mat a b, L.mat x y) := by
        intro a z x hab hz
        cases z with
        | inr w => simp only [embedA] at hz; cases hz
        | inl s =>
          simp only [embedA] at hz
          have hb : b = A.mat a b := (Prod.mk.inj (Sum.inl.inj hz)).1
          exact hab (A.col_injective b (hb.symm.trans (hidem b).symm))
      cases p₁ with
      | inr u =>
        cases p₁' with
        | inr u' =>
          simp only [f] at heq
          exact congrArg Sum.inr (Sum.inr.inj (hcol_h (Sum.inl y) (hembed_inj b heq)))
        | inl ax' =>
          rcases ax' with ⟨a', x'⟩
          simp only [f] at heq
          by_cases ha'b : a' = b
          · subst ha'b
            simp only [↓reduceIte] at heq
            exact absurd (hcol_h (Sum.inl y) (hembed_inj a' heq)) Sum.inr_ne_inl
          · simp only [ha'b, ↓reduceIte] at heq
            exact absurd heq (h_off_ne a' _ x' ha'b)
      | inl ax1 =>
        rcases ax1 with ⟨a, x⟩
        cases p₁' with
        | inr u' =>
          simp only [f] at heq
          by_cases hab : a = b
          · subst hab
            simp only [↓reduceIte] at heq
            exact absurd (hcol_h (Sum.inl y) (hembed_inj a heq)) Sum.inl_ne_inr
          · simp only [hab, ↓reduceIte] at heq
            exact absurd heq.symm (h_off_ne a _ x hab)
        | inl ax2 =>
          rcases ax2 with ⟨a', x'⟩
          simp only [f] at heq
          by_cases hab : a = b <;> by_cases ha'b : a' = b
          · rw [if_pos hab, if_pos ha'b] at heq
            rw [hab, ha'b] at heq
            have hx : x = x' := Sum.inl.inj (hcol_h (Sum.inl y) (hembed_inj b heq))
            rw [hab, ha'b, hx]
          · rw [if_pos hab, if_neg ha'b] at heq
            rw [hab] at heq
            exact absurd heq (h_off_ne a' _ x' ha'b)
          · rw [if_neg hab, if_pos ha'b] at heq
            rw [ha'b] at heq
            exact absurd heq.symm (h_off_ne a _ x hab)
          · rw [if_neg hab, if_neg ha'b] at heq
            have h1 := (Prod.mk.inj (Sum.inl.inj heq)).1
            have h2 := (Prod.mk.inj (Sum.inl.inj heq)).2
            rw [A.col_injective b h1, L.col_injective y h2]
  let ΩL := {σ : Fin q → Fin q // IsTransversal L σ}
  let ΩR := {τ : Fin r → Fin r // IsTransversal R τ}
  let ι := ({γ : Fin k → Fin k // γ ∈ D} × (Fin k → ΩL)) × ΩR
  let φ : ι → (α → α) := fun ⟨⟨γ, σ⟩, τ⟩ p =>
    match p with
    | Sum.inl (a, x) => Sum.inl (γ.1 a, (σ a).1 x)
    | Sum.inr u => Sum.inr (τ.1 u)
  have hinj : Function.Injective φ := by
    rintro ⟨⟨γ₁, σ₁⟩, τ₁⟩ ⟨⟨γ₂, σ₂⟩, τ₂⟩ heq
    have hγ : γ₁ = γ₂ := by
      apply Subtype.ext; funext a
      have := congr_fun heq (Sum.inl (a, ⟨0, hq⟩))
      exact (Prod.mk.inj (Sum.inl.inj this)).1
    have hσ : σ₁ = σ₂ := by
      funext a; apply Subtype.ext; funext x
      have := congr_fun heq (Sum.inl (a, x))
      exact (Prod.mk.inj (Sum.inl.inj this)).2
    have hτ : τ₁ = τ₂ := by
      apply Subtype.ext; funext u
      have := congr_fun heq (Sum.inr u)
      exact Sum.inr.inj this
    rw [hγ, hσ, hτ]
  have htrans : ∀ z : ι, Function.Injective (φ z) ∧ Function.Injective (fun p => f p (φ z p)) := by
    rintro ⟨⟨γ, σ⟩, τ⟩
    have hγT := (hD γ.1 γ.2).1
    have hγD := (hD γ.1 γ.2).2
    refine ⟨?_, ?_⟩
    · intro p₁ p₂ heq
      cases p₁ with
      | inl ax1 =>
        cases p₂ with
        | inl ax2 =>
          rcases ax1 with ⟨a₁, x₁⟩; rcases ax2 with ⟨a₂, x₂⟩
          simp only [φ] at heq
          have ha : a₁ = a₂ := hγT.1 (Prod.mk.inj (Sum.inl.inj heq)).1
          subst ha
          have hx : x₁ = x₂ := (σ a₁).2.1 (Prod.mk.inj (Sum.inl.inj heq)).2
          rw [hx]
        | inr u => simp only [φ] at heq; cases heq
      | inr u₁ =>
        cases p₂ with
        | inl ax2 => simp only [φ] at heq; cases heq
        | inr u₂ =>
          simp only [φ] at heq
          exact congrArg Sum.inr (τ.2.1 (Sum.inr.inj heq))
    · intro p₁ p₂ heq
      cases p₁ with
      | inl ax1 =>
        cases p₂ with
        | inl ax2 =>
          rcases ax1 with ⟨a₁, x₁⟩; rcases ax2 with ⟨a₂, x₂⟩
          have hne1 : a₁ ≠ γ.1 a₁ := (hγD a₁).symm
          have hne2 : a₂ ≠ γ.1 a₂ := (hγD a₂).symm
          simp only [φ, f, hne1, hne2, ↓reduceIte] at heq
          have ha : a₁ = a₂ := hγT.2 (Prod.mk.inj (Sum.inl.inj heq)).1
          subst ha
          have hx : x₁ = x₂ := (σ a₁).2.2 (Prod.mk.inj (Sum.inl.inj heq)).2
          rw [hx]
        | inr u =>
          rcases ax1 with ⟨a₁, x₁⟩
          have hne1 : a₁ ≠ γ.1 a₁ := (hγD a₁).symm
          simp only [φ, f, hne1, ↓reduceIte] at heq
          cases heq
      | inr u₁ =>
        cases p₂ with
        | inl ax2 =>
          rcases ax2 with ⟨a₂, x₂⟩
          have hne2 : a₂ ≠ γ.1 a₂ := (hγD a₂).symm
          simp only [φ, f, hne2, ↓reduceIte] at heq
          cases heq
        | inr u₂ =>
          simp only [φ, f] at heq
          exact congrArg Sum.inr (τ.2.2 (Sum.inr.inj heq))
  have hle := card_le_T_of_family e f hrow_f hcol_f φ hinj htrans
  simp only [ι, Fintype.card_prod, Fintype.card_coe, Fintype.card_pi, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin] at hle
  exact hle

/- ### Piece 3: Bordered Latin Square Constructions (`r = 1` and `Odd q, r ≤ q`) -/

private lemma exists_bordered_one (q : ℕ) (R : LatinSquare 1) :
    ∃ h : (Fin q ⊕ Fin 1) → (Fin q ⊕ Fin 1) → (Fin q ⊕ Fin 1),
      (∀ x, Function.Injective (h x)) ∧
      (∀ y, Function.Injective (fun x => h x y)) ∧
      (∀ u v : Fin 1, h (Sum.inr u) (Sum.inr v) = Sum.inr (R.mat u v)) := by
  have : NeZero (q + 1) := ⟨Nat.succ_ne_zero q⟩
  let e : Fin q ⊕ Fin 1 ≃ ZMod (q + 1) := finSumFinEquiv.trans (finEquivZMod (q + 1))
  let h : (Fin q ⊕ Fin 1) → (Fin q ⊕ Fin 1) → (Fin q ⊕ Fin 1) :=
    fun x y => e.symm (e x - e y - 1)
  refine ⟨h, ?_, ?_, ?_⟩
  · intro x y₁ y₂ heq
    have h1 := e.symm.injective heq
    have h2 : e y₁ = e y₂ := by linear_combination -h1
    exact e.injective h2
  · intro y x₁ x₂ heq
    have h1 := e.symm.injective heq
    have h2 : e x₁ = e x₂ := by linear_combination h1
    exact e.injective h2
  · intro u v
    have hu : u = 0 := Fin.eq_zero u
    have hv : v = 0 := Fin.eq_zero v
    subst hu; subst hv
    have hR : R.mat 0 0 = 0 := Fin.eq_zero _
    rw [hR]
    dsimp only [h]
    apply e.injective
    rw [e.apply_symm_apply]
    have he0 : e (Sum.inr 0) = (-1 : ZMod (q + 1)) := by
      have hq : ((q : ℕ) : ZMod (q + 1)) + 1 = 0 := by
        have hself : (((q + 1 : ℕ) : ZMod (q + 1))) = 0 := ZMod.natCast_self (q + 1)
        simp only [Nat.cast_add, Nat.cast_one] at hself
        exact hself
      have heval : e (Sum.inr 0) = ((q : ℕ) : ZMod (q + 1)) := by
        simp [e, finEquivZMod, finSumFinEquiv]
      rw [heval]
      linear_combination hq
    rw [he0]
    ring

private lemma zmod_two_mul_inj {q : ℕ} (hodd : Odd q) :
    Function.Injective (fun x : ZMod q => (2 : ZMod q) * x) := by
  obtain ⟨k, rfl⟩ := hodd
  have hinv : ((k + 1 : ℕ) : ZMod (2 * k + 1)) * 2 = 1 := by
    have h : ((k + 1 : ℕ) : ZMod (2 * k + 1)) * 2 = (((2 * k + 1) + 1 : ℕ) : ZMod (2 * k + 1)) := by
      push_cast; ring
    rw [h, Nat.cast_add, ZMod.natCast_self, zero_add, Nat.cast_one]
  intro x y hxy
  have h1 := congrArg (fun z => ((k + 1 : ℕ) : ZMod (2 * k + 1)) * z) hxy
  rw [← mul_assoc, ← mul_assoc, hinv, one_mul, one_mul] at h1
  exact h1

private def prolongZMod {q r : ℕ} [NeZero q] (R : LatinSquare r) :
    (ZMod q ⊕ Fin r) → (ZMod q ⊕ Fin r) → (ZMod q ⊕ Fin r)
  | Sum.inr u, Sum.inr v => Sum.inr (R.mat u v)
  | Sum.inl x, Sum.inr v => Sum.inl (2 * x + (v.1 : ZMod q))
  | Sum.inr u, Sum.inl y => Sum.inl (2 * y - (u.1 : ZMod q))
  | Sum.inl x, Sum.inl y =>
      if hd : (y - x).val < r then Sum.inr ⟨(y - x).val, hd⟩ else Sum.inl (x + y)

private lemma prolongZMod_row_inj {q r : ℕ} [NeZero q] (hodd : Odd q) (hrq : r ≤ q)
    (R : LatinSquare r) (p : ZMod q ⊕ Fin r) : Function.Injective (prolongZMod R p) := by
  have h2 := zmod_two_mul_inj hodd
  intro p₁ p₂ heq
  cases p with
  | inr u =>
    cases p₁ with
    | inr v₁ =>
      cases p₂ with
      | inr v₂ => exact congrArg Sum.inr (R.row_injective u (Sum.inr.inj heq))
      | inl y₂ => simp only [prolongZMod] at heq; cases heq
    | inl y₁ =>
      cases p₂ with
      | inr v₂ => simp only [prolongZMod] at heq; cases heq
      | inl y₂ =>
        simp only [prolongZMod] at heq
        have h1 : (2 : ZMod q) * y₁ = 2 * y₂ := by linear_combination Sum.inl.inj heq
        exact congrArg Sum.inl (h2 h1)
  | inl x =>
    cases p₁ with
    | inr v₁ =>
      cases p₂ with
      | inr v₂ =>
        simp only [prolongZMod] at heq
        have h1 : (v₁.1 : ZMod q) = (v₂.1 : ZMod q) := by linear_combination Sum.inl.inj heq
        have hv1 : ((v₁.1 : ZMod q)).val = v₁.1 := ZMod.val_natCast_of_lt (lt_of_lt_of_le v₁.2 hrq)
        have hv2 : ((v₂.1 : ZMod q)).val = v₂.1 := ZMod.val_natCast_of_lt (lt_of_lt_of_le v₂.2 hrq)
        exact congrArg Sum.inr (Fin.ext (by rw [← hv1, ← hv2, h1]))
      | inl y₂ =>
        simp only [prolongZMod] at heq
        split_ifs at heq with hd
        exfalso
        have h1 : y₂ - x = (v₁.1 : ZMod q) := by linear_combination -(Sum.inl.inj heq)
        have hval : (y₂ - x).val = v₁.1 := by
          rw [h1, ZMod.val_natCast_of_lt (lt_of_lt_of_le v₁.2 hrq)]
        exact hd (hval.symm ▸ v₁.2)
    | inl y₁ =>
      cases p₂ with
      | inr v₂ =>
        simp only [prolongZMod] at heq
        split_ifs at heq with hd
        exfalso
        have h1 : y₁ - x = (v₂.1 : ZMod q) := by linear_combination Sum.inl.inj heq
        have hval : (y₁ - x).val = v₂.1 := by
          rw [h1, ZMod.val_natCast_of_lt (lt_of_lt_of_le v₂.2 hrq)]
        exact hd (hval.symm ▸ v₂.2)
      | inl y₂ =>
        simp only [prolongZMod] at heq
        split_ifs at heq with hd1 hd2
        · have hval : (y₁ - x).val = (y₂ - x).val := congrArg Fin.val (Sum.inr.inj heq)
          have hsub : y₁ - x = y₂ - x := ZMod.val_injective q hval
          exact congrArg Sum.inl (by linear_combination hsub)
        · exact congrArg Sum.inl (add_left_cancel (Sum.inl.inj heq))

private lemma prolongZMod_col_inj {q r : ℕ} [NeZero q] (hodd : Odd q) (hrq : r ≤ q)
    (R : LatinSquare r) (p : ZMod q ⊕ Fin r) : Function.Injective (fun a => prolongZMod R a p) := by
  have h2 := zmod_two_mul_inj hodd
  intro p₁ p₂ heq
  cases p with
  | inr v =>
    cases p₁ with
    | inr u₁ =>
      cases p₂ with
      | inr u₂ => exact congrArg Sum.inr (R.col_injective v (Sum.inr.inj heq))
      | inl x₂ => simp only [prolongZMod] at heq; exact absurd heq Sum.inr_ne_inl
    | inl x₁ =>
      cases p₂ with
      | inr u₂ => simp only [prolongZMod] at heq; exact absurd heq Sum.inl_ne_inr
      | inl x₂ =>
        simp only [prolongZMod] at heq
        have h1 : (2 : ZMod q) * x₁ = 2 * x₂ := by linear_combination Sum.inl.inj heq
        exact congrArg Sum.inl (h2 h1)
  | inl y =>
    cases p₁ with
    | inr u₁ =>
      cases p₂ with
      | inr u₂ =>
        simp only [prolongZMod] at heq
        have h1 : (u₁.1 : ZMod q) = (u₂.1 : ZMod q) := by linear_combination -(Sum.inl.inj heq)
        have hu1 : ((u₁.1 : ZMod q)).val = u₁.1 := ZMod.val_natCast_of_lt (lt_of_lt_of_le u₁.2 hrq)
        have hu2 : ((u₂.1 : ZMod q)).val = u₂.1 := ZMod.val_natCast_of_lt (lt_of_lt_of_le u₂.2 hrq)
        exact congrArg Sum.inr (Fin.ext (by rw [← hu1, ← hu2, h1]))
      | inl x₂ =>
        simp only [prolongZMod] at heq
        split_ifs at heq with hd
        exfalso
        have h1 : y - x₂ = (u₁.1 : ZMod q) := by linear_combination Sum.inl.inj heq
        have hval : (y - x₂).val = u₁.1 := by
          rw [h1, ZMod.val_natCast_of_lt (lt_of_lt_of_le u₁.2 hrq)]
        exact hd (hval.symm ▸ u₁.2)
    | inl x₁ =>
      cases p₂ with
      | inr u₂ =>
        simp only [prolongZMod] at heq
        split_ifs at heq with hd
        exfalso
        have h1 : y - x₁ = (u₂.1 : ZMod q) := by linear_combination -(Sum.inl.inj heq)
        have hval : (y - x₁).val = u₂.1 := by
          rw [h1, ZMod.val_natCast_of_lt (lt_of_lt_of_le u₂.2 hrq)]
        exact hd (hval.symm ▸ u₂.2)
      | inl x₂ =>
        simp only [prolongZMod] at heq
        split_ifs at heq with hd1 hd2
        · have hval : (y - x₁).val = (y - x₂).val := congrArg Fin.val (Sum.inr.inj heq)
          have hsub : y - x₁ = y - x₂ := ZMod.val_injective q hval
          exact congrArg Sum.inl (by linear_combination -hsub)
        · exact congrArg Sum.inl (add_right_cancel (Sum.inl.inj heq))

private lemma exists_bordered_odd {q r : ℕ} (hodd : Odd q) (hrq : r ≤ q) (R : LatinSquare r) :
    ∃ h : (Fin q ⊕ Fin r) → (Fin q ⊕ Fin r) → (Fin q ⊕ Fin r),
      (∀ x, Function.Injective (h x)) ∧
      (∀ y, Function.Injective (fun x => h x y)) ∧
      (∀ u v : Fin r, h (Sum.inr u) (Sum.inr v) = Sum.inr (R.mat u v)) := by
  have : NeZero q := ⟨by rcases hodd with ⟨k, rfl⟩; omega⟩
  let e : Fin q ⊕ Fin r ≃ ZMod q ⊕ Fin r := Equiv.sumCongr (finEquivZMod q) (Equiv.refl (Fin r))
  refine ⟨fun x y => e.symm (prolongZMod R (e x) (e y)), ?_, ?_, ?_⟩
  · intro x y₁ y₂ heq
    exact e.injective (prolongZMod_row_inj hodd hrq R (e x) (e.symm.injective heq))
  · intro y x₁ x₂ heq
    exact e.injective (prolongZMod_col_inj hodd hrq R (e y) (e.symm.injective heq))
  · intro u v
    simp [e, prolongZMod]

/- ### Piece 4: Idempotent `A_3` (`d = 2`) and `A_4` (`d = 3`) & Inductive Step Inequalities -/

private def idemA3 : LatinSquare 3 where
  mat := Matrix.of (fun i j : Fin 3 => ![![(0 : Fin 3), 2, 1], ![2, 1, 0], ![1, 0, 2]] i j)
  row_injective := by
    intro i j₁ j₂ h; simp only [Matrix.of_apply] at h; revert i j₁ j₂ h; decide
  col_injective := by
    intro j i₁ i₂ h; simp only [Matrix.transpose_apply, Matrix.of_apply] at h; revert j i₁ i₂ h; decide

private def derangA3 : Finset (Fin 3 → Fin 3) := {![(1 : Fin 3), 2, 0], ![2, 0, 1]}

private lemma idemA3_idem : ∀ a : Fin 3, idemA3.mat a a = a := by
  intro a; simp only [idemA3, Matrix.of_apply]; revert a; decide

private lemma derangA3_valid : ∀ α ∈ derangA3, IsTransversal idemA3 α ∧ ∀ a : Fin 3, α a ≠ a := by
  simp only [derangA3, Finset.mem_insert, Finset.mem_singleton]
  rintro _ (rfl | rfl) <;>
    refine ⟨⟨by decide, by intro i j h; simp only [idemA3, Matrix.of_apply] at h; revert i j h; decide⟩, by decide⟩

private lemma derangA3_card : derangA3.card = 2 := by decide

private def idemA4 : LatinSquare 4 where
  mat := Matrix.of (fun i j : Fin 4 =>
    ![![(0 : Fin 4), 3, 1, 2], ![2, 1, 3, 0], ![3, 0, 2, 1], ![1, 2, 0, 3]] i j)
  row_injective := by
    intro i j₁ j₂ h; simp only [Matrix.of_apply] at h; revert i j₁ j₂ h; decide
  col_injective := by
    intro j i₁ i₂ h; simp only [Matrix.transpose_apply, Matrix.of_apply] at h; revert j i₁ i₂ h; decide

private def derangA4 : Finset (Fin 4 → Fin 4) :=
  {![(1 : Fin 4), 0, 3, 2], ![2, 3, 0, 1], ![3, 2, 1, 0]}

private lemma idemA4_idem : ∀ a : Fin 4, idemA4.mat a a = a := by
  intro a; simp only [idemA4, Matrix.of_apply]; revert a; decide

private lemma derangA4_valid : ∀ α ∈ derangA4, IsTransversal idemA4 α ∧ ∀ a : Fin 4, α a ≠ a := by
  simp only [derangA4, Finset.mem_insert, Finset.mem_singleton]
  rintro _ (rfl | rfl | rfl) <;>
    refine ⟨⟨by decide, by intro i j h; simp only [idemA4, Matrix.of_apply] at h; revert i j h; decide⟩, by decide⟩

private lemma derangA4_card : derangA4.card = 3 := by decide

private lemma T_one_ge : 1 ≤ LatinSquare.T 1 := by
  have h : 1 ≤ numTransversals (cyclicLS 1) := by
    have h1 : Fintype.card {σ : Fin 1 → Fin 1 // IsTransversal (cyclicLS 1) σ} ≥ 1 := by
      refine Fintype.card_pos_iff.mpr ⟨⟨id, Function.injective_id, ?_⟩⟩
      intro i j _; exact Fin.eq_zero i |>.trans (Fin.eq_zero j).symm
    exact h1
  exact le_trans h (numTransversals_le_T (cyclicLS 1))

private lemma T_three_add_one {q : ℕ} (hq : 0 < q) :
    2 * LatinSquare.T q ^ 3 ≤ LatinSquare.T (3 * q + 1) := by
  obtain ⟨L, hL⟩ := exists_latinSquare_eq_T q
  obtain ⟨R, hR⟩ := exists_latinSquare_eq_T 1
  obtain ⟨h, hrow, hcol, hsub⟩ := exists_bordered_one q R
  have hsdp := singular_direct_product hq idemA3 idemA3_idem derangA3 derangA3_valid L R h hrow hcol hsub
  rw [derangA3_card, hL, hR] at hsdp
  have h1 := T_one_ge
  nlinarith

private lemma T_four_add_one {q : ℕ} (hq : 0 < q) :
    3 * LatinSquare.T q ^ 4 ≤ LatinSquare.T (4 * q + 1) := by
  obtain ⟨L, hL⟩ := exists_latinSquare_eq_T q
  obtain ⟨R, hR⟩ := exists_latinSquare_eq_T 1
  obtain ⟨h, hrow, hcol, hsub⟩ := exists_bordered_one q R
  have hsdp := singular_direct_product hq idemA4 idemA4_idem derangA4 derangA4_valid L R h hrow hcol hsub
  rw [derangA4_card, hL, hR] at hsdp
  have h1 := T_one_ge
  nlinarith

private lemma T_three_add_r {q r : ℕ} (hodd : Odd q) (hrq : r ≤ q) :
    2 * LatinSquare.T q ^ 3 * LatinSquare.T r ≤ LatinSquare.T (3 * q + r) := by
  have hq : 0 < q := by rcases hodd with ⟨k, rfl⟩; omega
  obtain ⟨L, hL⟩ := exists_latinSquare_eq_T q
  obtain ⟨R, hR⟩ := exists_latinSquare_eq_T r
  obtain ⟨h, hrow, hcol, hsub⟩ := exists_bordered_odd hodd hrq R
  have hsdp := singular_direct_product hq idemA3 idemA3_idem derangA3 derangA3_valid L R h hrow hcol hsub
  rwa [derangA3_card, hL, hR] at hsdp

private lemma T_four_add_r {q r : ℕ} (hodd : Odd q) (hrq : r ≤ q) :
    3 * LatinSquare.T q ^ 4 * LatinSquare.T r ≤ LatinSquare.T (4 * q + r) := by
  have hq : 0 < q := by rcases hodd with ⟨k, rfl⟩; omega
  obtain ⟨L, hL⟩ := exists_latinSquare_eq_T q
  obtain ⟨R, hR⟩ := exists_latinSquare_eq_T r
  obtain ⟨h, hrow, hcol, hsub⟩ := exists_bordered_odd hodd hrq R
  have hsdp := singular_direct_product hq idemA4 idemA4_idem derangA4 derangA4_valid L R h hrow hcol hsub
  rwa [derangA4_card, hL, hR] at hsdp

/- ### Piece 5: Base Cases `n ∈ {3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14}` -/

private lemma T_three_ge : 3 ≤ LatinSquare.T 3 := by
  have h := card_le_T_of_family (finEquivZMod 3) (fun x y : ZMod 3 => x + y)
    (fun _ _ _ h => add_left_cancel h) (fun _ _ _ h => add_right_cancel h)
    (fun (b : ZMod 3) (x : ZMod 3) => x + b)
    (fun b₁ b₂ h => by simpa using congr_fun h 0)
    (fun b => ⟨fun _ _ h => add_right_cancel h, fun x y h => by
      have h1 : (2 : ZMod 3) * x = 2 * y := by linear_combination h
      exact zmod_two_mul_inj ⟨1, rfl⟩ h1⟩)
  simpa using h

private lemma T_four_ge : 8 ≤ LatinSquare.T 4 := by
  let e : Fin 4 ≃ Fin 2 × Fin 2 := (finCongr (show 4 = 2 * 2 by norm_num)).trans finProdFinEquiv.symm
  let f : (Fin 2 × Fin 2) → (Fin 2 × Fin 2) → (Fin 2 × Fin 2) :=
    fun p q => (p.1 + q.1, p.2 + q.2)
  have hrow : ∀ p, Function.Injective (f p) := fun p q₁ q₂ h =>
    Prod.ext (add_left_cancel (Prod.mk.inj h).1) (add_left_cancel (Prod.mk.inj h).2)
  have hcol : ∀ q, Function.Injective (fun p => f p q) := fun q p₁ p₂ h =>
    Prod.ext (add_right_cancel (Prod.mk.inj h).1) (add_right_cancel (Prod.mk.inj h).2)
  let φ : (Bool × (Fin 2 × Fin 2)) → ((Fin 2 × Fin 2) → (Fin 2 × Fin 2)) :=
    fun ⟨c, b⟩ x =>
      if c then (x.2 + b.1, x.1 + x.2 + b.2) else (x.1 + x.2 + b.1, x.1 + b.2)
  have hinj : Function.Injective φ := by decide
  have htrans : ∀ k, Function.Injective (φ k) ∧ Function.Injective (fun a => f a (φ k a)) := by
    decide
  have h := card_le_T_of_family e f hrow hcol φ hinj htrans
  simpa using h

private lemma T_five_ge : 15 ≤ LatinSquare.T 5 := by
  let φ : (Fin 3 × ZMod 5) → (ZMod 5 → ZMod 5) :=
    fun ⟨a, b⟩ x => ((a.1 + 1 : ℕ) : ZMod 5) * x + b
  have hinj : Function.Injective φ := by decide
  have htrans : ∀ k, Function.Injective (φ k) ∧ Function.Injective (fun x => x + φ k x) := by
    decide
  have h := card_le_T_of_family (finEquivZMod 5) (fun x y : ZMod 5 => x + y)
    (fun _ _ _ h => add_left_cancel h) (fun _ _ _ h => add_right_cancel h)
    φ hinj htrans
  simpa using h

private def L6mat (i j : Fin 6) : Fin 6 :=
  if (i = 0 ∧ j = 0) then 3
  else if (i = 0 ∧ j = 3) then 0
  else if (i = 3 ∧ j = 0) then 0
  else if (i = 3 ∧ j = 3) then 3
  else ⟨((i.1 / 3 + j.1 / 3) % 2) * 3 + (i.1 + j.1) % 3, by omega⟩

private def L6trans : Fin 26 → (Fin 6 → Fin 6) :=
  ![ ![0, 1, 3, 4, 5, 2], ![0, 1, 5, 2, 3, 4], ![0, 2, 3, 1, 4, 5], ![0, 2, 5, 4, 1, 3],
     ![0, 3, 1, 2, 4, 5], ![0, 3, 2, 5, 1, 4], ![0, 4, 1, 5, 3, 2], ![0, 4, 2, 1, 5, 3],
     ![1, 2, 5, 3, 4, 0], ![1, 4, 0, 3, 5, 2], ![1, 4, 5, 0, 2, 3], ![1, 5, 3, 0, 4, 2],
     ![2, 0, 5, 3, 1, 4], ![2, 3, 4, 0, 1, 5], ![2, 4, 1, 3, 0, 5], ![2, 4, 5, 0, 3, 1],
     ![3, 0, 4, 5, 1, 2], ![3, 0, 5, 2, 4, 1], ![3, 1, 4, 2, 0, 5], ![3, 1, 5, 4, 2, 0],
     ![3, 4, 0, 1, 2, 5], ![3, 4, 2, 5, 0, 1], ![3, 5, 0, 4, 1, 2], ![3, 5, 2, 1, 4, 0],
     ![4, 1, 2, 3, 5, 0], ![4, 1, 3, 0, 2, 5] ]

private lemma T_six_ge : 26 ≤ LatinSquare.T 6 := by
  have hrow : ∀ a : Fin 6, Function.Injective (L6mat a) := by decide
  have hcol : ∀ b : Fin 6, Function.Injective (fun a : Fin 6 => L6mat a b) := by decide
  have hinj : Function.Injective L6trans := by decide
  have htrans : ∀ k : Fin 26,
      Function.Injective (L6trans k) ∧ Function.Injective (fun a => L6mat a (L6trans k a)) := by
    decide
  have h := card_le_T_of_family (Equiv.refl (Fin 6)) L6mat hrow hcol L6trans hinj htrans
  simpa using h

private def xor8 (a b : Fin 8) : Fin 8 :=
  ⟨(a.1 % 2 + b.1 % 2) % 2 + 2 * (((a.1 / 2) % 2 + (b.1 / 2) % 2) % 2) +
    4 * (((a.1 / 4) % 2 + (b.1 / 4) % 2) % 2), by omega⟩

private def matMul8 (r0 r1 r2 : ℕ) (v : Fin 8) : Fin 8 :=
  let bit (r : ℕ) : ℕ :=
    ((r % 2) * (v.1 % 2) + ((r / 2) % 2) * ((v.1 / 2) % 2) + ((r / 4) % 2) * ((v.1 / 4) % 2)) % 2
  ⟨bit r0 + 2 * bit r1 + 4 * bit r2, by
    have h0 : bit r0 < 2 := Nat.mod_lt _ (by omega)
    have h1 : bit r1 < 2 := Nat.mod_lt _ (by omega)
    have h2 : bit r2 < 2 := Nat.mod_lt _ (by omega)
    omega⟩

private def mats8 : Fin 10 → (Fin 8 → Fin 8) :=
  ![ matMul8 2 4 3, matMul8 2 4 5, matMul8 2 5 1, matMul8 2 5 6, matMul8 2 6 1,
     matMul8 2 6 5, matMul8 2 7 3, matMul8 2 7 6, matMul8 3 4 1, matMul8 3 4 5 ]

private lemma T_eight_ge : 80 ≤ LatinSquare.T 8 := by
  have hrow : ∀ a : Fin 8, Function.Injective (xor8 a) := by decide
  have hcol : ∀ b : Fin 8, Function.Injective (fun a : Fin 8 => xor8 a b) := by decide
  have hxor_assoc : ∀ a b c : Fin 8, xor8 a (xor8 b c) = xor8 (xor8 a b) c := by decide
  have hxor_zero : ∀ b : Fin 8, xor8 0 b = b := by decide
  have hM0 : ∀ k : Fin 10, mats8 k 0 = 0 := by decide
  have hMinj : Function.Injective mats8 := by decide
  have hMtrans : ∀ k : Fin 10,
      Function.Injective (mats8 k) ∧ Function.Injective (fun x => xor8 x (mats8 k x)) := by
    decide
  let φ : (Fin 10 × Fin 8) → (Fin 8 → Fin 8) := fun ⟨k, b⟩ x => xor8 (mats8 k x) b
  have hinj : Function.Injective φ := by
    rintro ⟨k₁, b₁⟩ ⟨k₂, b₂⟩ h
    have hb : b₁ = b₂ := by
      have h0 := congr_fun h 0
      simpa only [φ, hM0, hxor_zero] using h0
    subst hb
    have hk : k₁ = k₂ := by
      apply hMinj; funext x
      exact hcol b₁ (congr_fun h x)
    rw [hk]
  have htrans : ∀ p : Fin 10 × Fin 8,
      Function.Injective (φ p) ∧ Function.Injective (fun x => xor8 x (φ p x)) := by
    rintro ⟨k, b⟩
    refine ⟨(hcol b).comp (hMtrans k).1, ?_⟩
    intro x y h
    dsimp only [φ] at h
    rw [hxor_assoc, hxor_assoc] at h
    exact (hMtrans k).2 (hcol b h)
  have h := card_le_T_of_family (Equiv.refl (Fin 8)) xor8 hrow hcol φ hinj htrans
  simpa using h

/- ### General `ZMod m` Affine Action Lemmas (for `n = 7, 9, 10, 11, 13, 14`) -/

private def affAct {m : ℕ} (a b : ZMod m) (u : (ZMod m)ˣ) (f : ZMod m → ZMod m) :
    ZMod m → ZMod m :=
  fun x => (u : ZMod m) * f (((u⁻¹ : (ZMod m)ˣ) : ZMod m) * x + a) + b

private lemma affAct_transversal {m : ℕ} (a b : ZMod m) (u : (ZMod m)ˣ) (f : ZMod m → ZMod m)
    (hf1 : Function.Injective f) (hf2 : Function.Injective (fun x => x + f x)) :
    Function.Injective (affAct a b u f) ∧
    Function.Injective (fun x => x + affAct a b u f x) := by
  have hu_mul : Function.Injective (fun x : ZMod m => (u : ZMod m) * x) := by
    intro x y h
    have := congrArg (fun z => ((u⁻¹ : (ZMod m)ˣ) : ZMod m) * z) h
    simpa [← mul_assoc] using this
  have huinv_mul : Function.Injective (fun x : ZMod m => ((u⁻¹ : (ZMod m)ˣ) : ZMod m) * x) := by
    intro x y h
    have := congrArg (fun z => (u : ZMod m) * z) h
    simpa [← mul_assoc] using this
  refine ⟨?_, ?_⟩
  · intro x y h
    dsimp only [affAct] at h
    have h1 := hf1 (hu_mul (add_right_cancel h))
    exact huinv_mul (add_right_cancel h1)
  · intro x y h
    dsimp only [affAct] at h
    have hrew : ∀ z : ZMod m,
        z + ((u : ZMod m) * f (((u⁻¹ : (ZMod m)ˣ) : ZMod m) * z + a) + b) =
        (u : ZMod m) * ((((u⁻¹ : (ZMod m)ˣ) : ZMod m) * z + a) +
          f (((u⁻¹ : (ZMod m)ˣ) : ZMod m) * z + a)) + (b - (u : ZMod m) * a) := by
      intro z
      have huv : (u : ZMod m) * ((u⁻¹ : (ZMod m)ˣ) : ZMod m) = 1 := by
        exact_mod_cast Units.mul_inv u
      calc z + ((u : ZMod m) * f (((u⁻¹ : (ZMod m)ˣ) : ZMod m) * z + a) + b)
          = 1 * z + (u : ZMod m) * f (((u⁻¹ : (ZMod m)ˣ) : ZMod m) * z + a) + b := by ring
        _ = (u : ZMod m) * ((u⁻¹ : (ZMod m)ˣ) : ZMod m) * z +
            (u : ZMod m) * f (((u⁻¹ : (ZMod m)ˣ) : ZMod m) * z + a) + b := by rw [huv]
        _ = _ := by ring
    rw [hrew x, hrew y] at h
    have h1 := hf2 (hu_mul (add_right_cancel h))
    exact huinv_mul (add_right_cancel h1)

private lemma affAct_comp {m : ℕ} (a₁ b₁ a₂ b₂ : ZMod m) (u₁ u₂ : (ZMod m)ˣ)
    (f : ZMod m → ZMod m) :
    affAct a₁ b₁ u₁ (affAct a₂ b₂ u₂ f) =
      affAct (((u₂⁻¹ : (ZMod m)ˣ) : ZMod m) * a₁ + a₂) ((u₁ : ZMod m) * b₂ + b₁) (u₁ * u₂) f := by
  funext x
  dsimp only [affAct]
  have hinv : (((u₁ * u₂)⁻¹ : (ZMod m)ˣ) : ZMod m) =
      ((u₂⁻¹ : (ZMod m)ˣ) : ZMod m) * ((u₁⁻¹ : (ZMod m)ˣ) : ZMod m) := by
    rw [mul_inv_rev]; push_cast; rfl
  rw [hinv, Units.val_mul]
  ring_nf

private lemma affAct_id {m : ℕ} (f : ZMod m → ZMod m) : affAct 0 0 1 f = f := by
  funext x; simp [affAct]

private lemma affAct_inj_of_triv_stab {m : ℕ} (f : ZMod m → ZMod m)
    (hstab : ∀ (a : ZMod m) (u : (ZMod m)ˣ),
      (∀ x : ZMod m, (u : ZMod m) * f (((u⁻¹ : (ZMod m)ˣ) : ZMod m) * x + a) +
        (f 0 - (u : ZMod m) * f a) = f x) → a = 0 ∧ u = 1) :
    Function.Injective (fun p : (ZMod m × ZMod m) × (ZMod m)ˣ => affAct p.1.1 p.1.2 p.2 f) := by
  rintro ⟨⟨a₁, b₁⟩, u₁⟩ ⟨⟨a₂, b₂⟩, u₂⟩ heq
  -- Apply inverse of (a₁, b₁, u₁) to both sides
  let a₁' : ZMod m := -((u₁ : ZMod m) * a₁)
  let b₁' : ZMod m := -(((u₁⁻¹ : (ZMod m)ˣ) : ZMod m) * b₁)
  have hleft : affAct a₁' b₁' u₁⁻¹ (affAct a₁ b₁ u₁ f) = f := by
    rw [affAct_comp]
    have ha : ((u₁⁻¹ : (ZMod m)ˣ) : ZMod m) * a₁' + a₁ = 0 := by
      dsimp only [a₁']
      have huv : ((u₁⁻¹ : (ZMod m)ˣ) : ZMod m) * (u₁ : ZMod m) = 1 := by
        exact_mod_cast Units.inv_mul u₁
      calc ((u₁⁻¹ : (ZMod m)ˣ) : ZMod m) * -((u₁ : ZMod m) * a₁) + a₁
          = -(((u₁⁻¹ : (ZMod m)ˣ) : ZMod m) * (u₁ : ZMod m)) * a₁ + a₁ := by ring
        _ = -(1 : ZMod m) * a₁ + a₁ := by rw [huv]
        _ = 0 := by ring
    have hb : ((u₁⁻¹ : (ZMod m)ˣ) : ZMod m) * b₁ + b₁' = 0 := by
      dsimp only [b₁']; ring
    rw [ha, hb, inv_mul_cancel, affAct_id]
  have hright := congrArg (affAct a₁' b₁' u₁⁻¹) heq
  rw [hleft, affAct_comp] at hright
  set a' := ((u₂⁻¹ : (ZMod m)ˣ) : ZMod m) * a₁' + a₂
  set b' := ((u₁⁻¹ : (ZMod m)ˣ) : ZMod m) * b₂ + b₁'
  set u' := u₁⁻¹ * u₂
  have hb'_eq : b' = f 0 - (u' : ZMod m) * f a' := by
    have h0 := congr_fun hright.symm 0
    simp only [affAct, mul_zero, zero_add] at h0
    linear_combination h0
  have hfix : ∀ x, (u' : ZMod m) * f (((u'⁻¹ : (ZMod m)ˣ) : ZMod m) * x + a') +
      (f 0 - (u' : ZMod m) * f a') = f x := by
    intro x
    rw [← hb'_eq]
    exact congr_fun hright.symm x
  obtain ⟨ha'0, hu'1⟩ := hstab a' u' hfix
  have hu : u₁ = u₂ := by
    have h := congrArg (u₁ * ·) hu'1
    simpa [u'] using h.symm
  subst hu
  have ha : a₁ = a₂ := by
    have huv : ((u₁⁻¹ : (ZMod m)ˣ) : ZMod m) * (u₁ : ZMod m) = 1 := by
      exact_mod_cast Units.inv_mul u₁
    have h1 : a₂ - a₁ = 0 := by
      calc a₂ - a₁ = -(((u₁⁻¹ : (ZMod m)ˣ) : ZMod m) * (u₁ : ZMod m)) * a₁ + a₂ := by
            rw [huv]; ring
        _ = ((u₁⁻¹ : (ZMod m)ˣ) : ZMod m) * -((u₁ : ZMod m) * a₁) + a₂ := by ring
        _ = a' := rfl
        _ = 0 := ha'0
    linear_combination -h1
  subst ha
  have hb : b₁ = b₂ := by
    have h0 := congr_fun heq 0
    dsimp only [affAct] at h0
    linear_combination h0
  rw [hb]

private lemma zmod_orbit_le_T {m : ℕ} [NeZero m] (f : ZMod m → ZMod m)
    (hf1 : Function.Injective f) (hf2 : Function.Injective (fun x => x + f x))
    (hstab : ∀ (a : ZMod m) (u : (ZMod m)ˣ),
      (∀ x : ZMod m, (u : ZMod m) * f (((u⁻¹ : (ZMod m)ˣ) : ZMod m) * x + a) +
        (f 0 - (u : ZMod m) * f a) = f x) → a = 0 ∧ u = 1) :
    m * m * Nat.totient m ≤ LatinSquare.T m := by
  have h := card_le_T_of_family (finEquivZMod m) (fun x y : ZMod m => x + y)
    (fun _ _ _ h => add_left_cancel h) (fun _ _ _ h => add_right_cancel h)
    (fun p : (ZMod m × ZMod m) × (ZMod m)ˣ => affAct p.1.1 p.1.2 p.2 f)
    (affAct_inj_of_triv_stab f hstab)
    (fun p => affAct_transversal p.1.1 p.1.2 p.2 f hf1 hf2)
  simp only [Fintype.card_prod, ZMod.card, ZMod.card_units_eq_totient] at h
  exact h

private lemma affAct_avoids_diag {m : ℕ} (f : ZMod m → ZMod m) (d a : ZMod m) (u : (ZMod m)ˣ)
    (hd : ∀ y : ZMod m, y - f y ≠ d) :
    ∀ x : ZMod m, affAct a ((u : ZMod m) * (d - a)) u f x ≠ x := by
  intro x h
  dsimp only [affAct] at h
  set y := ((u⁻¹ : (ZMod m)ˣ) : ZMod m) * x + a
  have hx : x = (u : ZMod m) * (y - a) := by
    have huv : (u : ZMod m) * ((u⁻¹ : (ZMod m)ˣ) : ZMod m) = 1 := by
      exact_mod_cast Units.mul_inv u
    calc x = 1 * x := by ring
      _ = (u : ZMod m) * ((u⁻¹ : (ZMod m)ˣ) : ZMod m) * x := by rw [huv]
      _ = (u : ZMod m) * (y - a) := by dsimp only [y]; ring
  rw [hx] at h
  have h1 : (u : ZMod m) * (y - f y) = (u : ZMod m) * d := by linear_combination -h
  have h2 : y - f y = d := by
    have := congrArg (fun z => ((u⁻¹ : (ZMod m)ˣ) : ZMod m) * z) h1
    simpa [← mul_assoc] using this
  exact hd y h2

private lemma prolong1_extend_transversal {m : ℕ} [NeZero m] (g : ZMod m → ZMod m)
    (hg1 : Function.Injective g) (hg2 : Function.Injective (fun x => x + g x))
    (hdiag : ∀ x : ZMod m, g x ≠ x) :
    let ψ : (ZMod m ⊕ Fin 1) → (ZMod m ⊕ Fin 1) := Sum.map g id
    Function.Injective ψ ∧
      Function.Injective (fun p => prolongZMod (cyclicLS 1) p (ψ p)) := by
  intro ψ
  refine ⟨hg1.sumMap Function.injective_id, ?_⟩
  intro p₁ p₂ heq
  cases p₁ with
  | inr u₁ =>
    cases p₂ with
    | inr u₂ => exact congrArg Sum.inr (Fin.eq_zero u₁ |>.trans (Fin.eq_zero u₂).symm)
    | inl x₂ =>
      have hne : (g x₂ - x₂).val ≠ 0 := fun hz =>
        hdiag x₂ (sub_eq_zero.mp ((ZMod.val_eq_zero (g x₂ - x₂)).mp hz))
      have hlt : ¬ (g x₂ - x₂).val < 1 := by omega
      simp only [ψ, Sum.map_inr, Sum.map_inl, id_eq, prolongZMod, hlt, ↓reduceDIte] at heq
      cases heq
  | inl x₁ =>
    have hne1 : (g x₁ - x₁).val ≠ 0 := fun hz =>
      hdiag x₁ (sub_eq_zero.mp ((ZMod.val_eq_zero (g x₁ - x₁)).mp hz))
    have hlt1 : ¬ (g x₁ - x₁).val < 1 := by omega
    cases p₂ with
    | inr u₂ =>
      simp only [ψ, Sum.map_inr, Sum.map_inl, id_eq, prolongZMod, hlt1, ↓reduceDIte] at heq
      cases heq
    | inl x₂ =>
      have hne2 : (g x₂ - x₂).val ≠ 0 := fun hz =>
        hdiag x₂ (sub_eq_zero.mp ((ZMod.val_eq_zero (g x₂ - x₂)).mp hz))
      have hlt2 : ¬ (g x₂ - x₂).val < 1 := by omega
      simp only [ψ, Sum.map_inl, prolongZMod, hlt1, hlt2, ↓reduceDIte] at heq
      exact congrArg Sum.inl (hg2 (Sum.inl.inj heq))

private def coll1 {m : ℕ} [NeZero m] (f : ZMod m → ZMod m) : ℕ :=
  (Finset.univ.filter (fun p : ZMod m × ZMod m => f p.1 - p.1 = f p.2 - p.2)).card

private lemma coll1_affAct {m : ℕ} [NeZero m] (a b : ZMod m) (u : (ZMod m)ˣ)
    (f : ZMod m → ZMod m) : coll1 (affAct a b u f) = coll1 f := by
  unfold coll1
  let e : ZMod m ≃ ZMod m :=
    { toFun := fun x => ((u⁻¹ : (ZMod m)ˣ) : ZMod m) * x + a
      invFun := fun y => (u : ZMod m) * (y - a)
      left_inv := fun x => by
        have huv : (u : ZMod m) * ((u⁻¹ : (ZMod m)ˣ) : ZMod m) = 1 := by
          exact_mod_cast Units.mul_inv u
        calc (u : ZMod m) * (((u⁻¹ : (ZMod m)ˣ) : ZMod m) * x + a - a)
            = (u : ZMod m) * ((u⁻¹ : (ZMod m)ˣ) : ZMod m) * x := by ring
          _ = 1 * x := by rw [huv]
          _ = x := one_mul x
      right_inv := fun y => by
        have huv : ((u⁻¹ : (ZMod m)ˣ) : ZMod m) * (u : ZMod m) = 1 := by
          exact_mod_cast Units.inv_mul u
        calc ((u⁻¹ : (ZMod m)ˣ) : ZMod m) * ((u : ZMod m) * (y - a)) + a
            = ((u⁻¹ : (ZMod m)ˣ) : ZMod m) * (u : ZMod m) * (y - a) + a := by ring
          _ = 1 * (y - a) + a := by rw [huv]
          _ = y := by ring }
  have hdiff : ∀ x : ZMod m,
      affAct a b u f x - x = (u : ZMod m) * (f (e x) - e x) + (b + (u : ZMod m) * a) := by
    intro x
    have huv : (u : ZMod m) * ((u⁻¹ : (ZMod m)ˣ) : ZMod m) = 1 := by
      exact_mod_cast Units.mul_inv u
    dsimp only [affAct, e, Equiv.coe_fn_mk]
    calc (u : ZMod m) * f (((u⁻¹ : (ZMod m)ˣ) : ZMod m) * x + a) + b - x
        = (u : ZMod m) * f (((u⁻¹ : (ZMod m)ˣ) : ZMod m) * x + a) + b - 1 * x := by ring
      _ = (u : ZMod m) * f (((u⁻¹ : (ZMod m)ˣ) : ZMod m) * x + a) + b -
          (u : ZMod m) * ((u⁻¹ : (ZMod m)ˣ) : ZMod m) * x := by rw [huv]
      _ = _ := by ring
  refine Finset.card_bij (fun p _ => (e p.1, e p.2)) ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    rw [hdiff p.1, hdiff p.2] at hp
    have h1 : (u : ZMod m) * (f (e p.1) - e p.1) = (u : ZMod m) * (f (e p.2) - e p.2) :=
      add_right_cancel hp
    have := congrArg (fun z => ((u⁻¹ : (ZMod m)ˣ) : ZMod m) * z) h1
    simpa [← mul_assoc] using this
  · intro p₁ _ p₂ _ h
    exact Prod.ext (e.injective (Prod.mk.inj h).1) (e.injective (Prod.mk.inj h).2)
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
    refine ⟨(e.symm q.1, e.symm q.2), ?_, by simp⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hdiff, hdiff, e.apply_symm_apply, e.apply_symm_apply, hq]

/- Concrete witness bounds for n = 7, 9, 10, 11, 13, 14 -/

private def f7 (x : ZMod 7) : ZMod 7 :=
  (![(0 : ZMod 7), 2, 4, 5, 1, 6, 3] ⟨x.val, x.val_lt⟩)

private lemma T_seven_ge : 49 ≤ LatinSquare.T 7 := by
  let φ : (ZMod 7 × ZMod 7) → (ZMod 7 → ZMod 7) := fun ⟨a, b⟩ x => f7 (x + a) + b
  have hf1 : Function.Injective f7 := by decide
  have hf2 : Function.Injective (fun x : ZMod 7 => x + f7 x) := by decide
  have hstab : ∀ a : ZMod 7, (∀ x : ZMod 7, f7 (x + a) + (f7 0 - f7 a) = f7 x) → a = 0 := by
    decide
  have hinj : Function.Injective φ := by
    rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ heq
    have h1 : ∀ x : ZMod 7, f7 (x + (a₂ - a₁)) + (b₂ - b₁) = f7 x := by
      intro x
      have hx := congr_fun heq (x - a₁)
      dsimp only [φ] at hx
      have harg1 : x - a₁ + a₁ = x := by ring
      have harg2 : x - a₁ + a₂ = x + (a₂ - a₁) := by ring
      rw [harg1, harg2] at hx
      linear_combination -hx
    have hbdiff : b₂ - b₁ = f7 0 - f7 (a₂ - a₁) := by
      have h0 := h1 0
      simp only [zero_add] at h0
      linear_combination h0
    have ha0 : a₂ - a₁ = 0 := hstab (a₂ - a₁) (fun x => by rw [← hbdiff]; exact h1 x)
    have ha : a₁ = a₂ := by linear_combination -ha0
    subst ha
    have hb : b₁ = b₂ := by
      have h0 := congr_fun heq 0
      dsimp only [φ] at h0
      linear_combination h0
    rw [hb]
  have htrans : ∀ p : ZMod 7 × ZMod 7,
      Function.Injective (φ p) ∧ Function.Injective (fun x => x + φ p x) := by
    rintro ⟨a, b⟩
    have hfun : φ (a, b) = affAct a b 1 f7 := by funext x; simp [affAct, φ]
    rw [hfun]
    exact affAct_transversal a b 1 f7 hf1 hf2
  have h := card_le_T_of_family (finEquivZMod 7) (fun x y : ZMod 7 => x + y)
    (fun _ _ _ h => add_left_cancel h) (fun _ _ _ h => add_right_cancel h) φ hinj htrans
  simpa using h

private def f9 (x : ZMod 9) : ZMod 9 :=
  (![(0 : ZMod 9), 7, 8, 3, 1, 2, 5, 6, 4] ⟨x.val, x.val_lt⟩)

private lemma f9_triv_stab : ∀ (a : ZMod 9) (u : (ZMod 9)ˣ),
    (∀ x : ZMod 9, (u : ZMod 9) * f9 (((u⁻¹ : (ZMod 9)ˣ) : ZMod 9) * x + a) +
      (f9 0 - (u : ZMod 9) * f9 a) = f9 x) → a = 0 ∧ u = 1 := by
  have hdec : ∀ (a u : ZMod 9), u * u ^ 5 = 1 →
      (∀ x : ZMod 9, u * f9 (u ^ 5 * x + a) + (f9 0 - u * f9 a) = f9 x) → a = 0 ∧ u = 1 := by
    decide
  have hpow : ∀ u : ZMod 9, (∃ v : ZMod 9, u * v = 1) → u * u ^ 5 = 1 := by decide
  intro a u hfix
  have hu5 : (u : ZMod 9) * (u : ZMod 9) ^ 5 = 1 :=
    hpow (u : ZMod 9) ⟨((u⁻¹ : (ZMod 9)ˣ) : ZMod 9), by exact_mod_cast Units.mul_inv u⟩
  have hinv_eq : ((u⁻¹ : (ZMod 9)ˣ) : ZMod 9) = (u : ZMod 9) ^ 5 := by
    have := congrArg (fun z => ((u⁻¹ : (ZMod 9)ˣ) : ZMod 9) * z) hu5
    simpa [← mul_assoc] using this.symm
  rw [hinv_eq] at hfix
  obtain ⟨ha, hu1⟩ := hdec a (u : ZMod 9) hu5 hfix
  exact ⟨ha, Units.ext hu1⟩

private lemma T_nine_ge : 486 ≤ LatinSquare.T 9 := by
  have hf1 : Function.Injective f9 := by decide
  have hf2 : Function.Injective (fun x : ZMod 9 => x + f9 x) := by decide
  have h := zmod_orbit_le_T f9 hf1 hf2 f9_triv_stab
  have htot : Nat.totient 9 = 6 := by decide
  rw [htot] at h
  exact h

private lemma T_ten_ge : 270 ≤ LatinSquare.T 10 := by
  have hf1 : Function.Injective f9 := by decide
  have hf2 : Function.Injective (fun x : ZMod 9 => x + f9 x) := by decide
  let D9 : Finset (ZMod 9) := {2, 5, 6, 7, 8}
  have hD9_card : D9.card = 5 := by decide
  have hD9_miss : ∀ d ∈ D9, ∀ y : ZMod 9, y - f9 y ≠ d := by decide
  let e : Fin 10 ≃ ZMod 9 ⊕ Fin 1 :=
    finSumFinEquiv.symm.trans (Equiv.sumCongr (finEquivZMod 9) (Equiv.refl (Fin 1)))
  let ι := ({d : ZMod 9 // d ∈ D9} × ZMod 9) × (ZMod 9)ˣ
  let φ : ι → ((ZMod 9 ⊕ Fin 1) → (ZMod 9 ⊕ Fin 1)) :=
    fun ⟨⟨d, a⟩, u⟩ => Sum.map (affAct a ((u : ZMod 9) * (d.1 - a)) u f9) id
  have hinj : Function.Injective φ := by
    rintro ⟨⟨d₁, a₁⟩, u₁⟩ ⟨⟨d₂, a₂⟩, u₂⟩ heq
    have haff : affAct a₁ ((u₁ : ZMod 9) * (d₁.1 - a₁)) u₁ f9 =
        affAct a₂ ((u₂ : ZMod 9) * (d₂.1 - a₂)) u₂ f9 := by
      funext x
      exact Sum.inl.inj (congr_fun heq (Sum.inl x))
    have htriple := affAct_inj_of_triv_stab f9 f9_triv_stab
      (a₁ := ((a₁, (u₁ : ZMod 9) * (d₁.1 - a₁)), u₁))
      (a₂ := ((a₂, (u₂ : ZMod 9) * (d₂.1 - a₂)), u₂)) haff
    have ha : a₁ = a₂ := (Prod.mk.inj (Prod.mk.inj htriple).1).1
    have hb : (u₁ : ZMod 9) * (d₁.1 - a₁) = (u₂ : ZMod 9) * (d₂.1 - a₂) :=
      (Prod.mk.inj (Prod.mk.inj htriple).1).2
    have hu : u₁ = u₂ := (Prod.mk.inj htriple).2
    subst ha; subst hu
    have hd1 : d₁.1 - a₁ = d₂.1 - a₁ := by
      have := congrArg (fun z => ((u₁⁻¹ : (ZMod 9)ˣ) : ZMod 9) * z) hb
      simpa [← mul_assoc] using this
    have hd : d₁ = d₂ := Subtype.ext (by linear_combination hd1)
    rw [hd]
  have htrans : ∀ k : ι,
      Function.Injective (φ k) ∧
      Function.Injective (fun p => prolongZMod (cyclicLS 1) p (φ k p)) := by
    rintro ⟨⟨d, a⟩, u⟩
    have ht := affAct_transversal a ((u : ZMod 9) * (d.1 - a)) u f9 hf1 hf2
    have hdiag := affAct_avoids_diag f9 d.1 a u (hD9_miss d.1 d.2)
    exact prolong1_extend_transversal _ ht.1 ht.2 hdiag
  have hle := card_le_T_of_family e (prolongZMod (cyclicLS 1))
    (prolongZMod_row_inj ⟨4, rfl⟩ (by omega) (cyclicLS 1))
    (prolongZMod_col_inj ⟨4, rfl⟩ (by omega) (cyclicLS 1))
    φ hinj htrans
  simp only [ι, Fintype.card_prod, Fintype.card_coe, hD9_card, ZMod.card,
    ZMod.card_units_eq_totient] at hle
  have htot : Nat.totient 9 = 6 := by decide
  rw [htot] at hle
  exact hle

private def f11 (x : ZMod 11) : ZMod 11 :=
  (![(0 : ZMod 11), 8, 4, 1, 9, 7, 2, 3, 10, 5, 6] ⟨x.val, x.val_lt⟩)

private lemma f11_triv_stab : ∀ (a : ZMod 11) (u : (ZMod 11)ˣ),
    (∀ x : ZMod 11, (u : ZMod 11) * f11 (((u⁻¹ : (ZMod 11)ˣ) : ZMod 11) * x + a) +
      (f11 0 - (u : ZMod 11) * f11 a) = f11 x) → a = 0 ∧ u = 1 := by
  have hdec : ∀ (a u : ZMod 11), u * u ^ 9 = 1 →
      (∀ x : ZMod 11, u * f11 (u ^ 9 * x + a) + (f11 0 - u * f11 a) = f11 x) → a = 0 ∧ u = 1 := by
    decide
  have hpow : ∀ u : ZMod 11, (∃ v : ZMod 11, u * v = 1) → u * u ^ 9 = 1 := by decide
  intro a u hfix
  have hu9 : (u : ZMod 11) * (u : ZMod 11) ^ 9 = 1 :=
    hpow (u : ZMod 11) ⟨((u⁻¹ : (ZMod 11)ˣ) : ZMod 11), by exact_mod_cast Units.mul_inv u⟩
  have hinv_eq : ((u⁻¹ : (ZMod 11)ˣ) : ZMod 11) = (u : ZMod 11) ^ 9 := by
    have := congrArg (fun z => ((u⁻¹ : (ZMod 11)ˣ) : ZMod 11) * z) hu9
    simpa [← mul_assoc] using this.symm
  rw [hinv_eq] at hfix
  obtain ⟨ha, hu1⟩ := hdec a (u : ZMod 11) hu9 hfix
  exact ⟨ha, Units.ext hu1⟩

private lemma T_eleven_ge : 1210 ≤ LatinSquare.T 11 := by
  have hf1 : Function.Injective f11 := by decide
  have hf2 : Function.Injective (fun x : ZMod 11 => x + f11 x) := by decide
  have h := zmod_orbit_le_T f11 hf1 hf2 f11_triv_stab
  have htot : Nat.totient 11 = 10 := by decide
  rw [htot] at h
  exact h

private def f13a (x : ZMod 13) : ZMod 13 :=
  (![(0 : ZMod 13), 8, 2, 3, 7, 5, 10, 11, 12, 6, 4, 1, 9] ⟨x.val, x.val_lt⟩)

private def f13b (x : ZMod 13) : ZMod 13 :=
  (![(0 : ZMod 13), 5, 6, 9, 10, 11, 12, 3, 1, 2, 7, 4, 8] ⟨x.val, x.val_lt⟩)

private lemma f13a_triv_stab : ∀ (a : ZMod 13) (u : (ZMod 13)ˣ),
    (∀ x : ZMod 13, (u : ZMod 13) * f13a (((u⁻¹ : (ZMod 13)ˣ) : ZMod 13) * x + a) +
      (f13a 0 - (u : ZMod 13) * f13a a) = f13a x) → a = 0 ∧ u = 1 := by
  have hdec : ∀ (a u : ZMod 13), u * u ^ 11 = 1 →
      (∀ x : ZMod 13, u * f13a (u ^ 11 * x + a) + (f13a 0 - u * f13a a) = f13a x) →
      a = 0 ∧ u = 1 := by
    decide
  have hpow : ∀ u : ZMod 13, (∃ v : ZMod 13, u * v = 1) → u * u ^ 11 = 1 := by decide
  intro a u hfix
  have hu11 : (u : ZMod 13) * (u : ZMod 13) ^ 11 = 1 :=
    hpow (u : ZMod 13) ⟨((u⁻¹ : (ZMod 13)ˣ) : ZMod 13), by exact_mod_cast Units.mul_inv u⟩
  have hinv_eq : ((u⁻¹ : (ZMod 13)ˣ) : ZMod 13) = (u : ZMod 13) ^ 11 := by
    have := congrArg (fun z => ((u⁻¹ : (ZMod 13)ˣ) : ZMod 13) * z) hu11
    simpa [← mul_assoc] using this.symm
  rw [hinv_eq] at hfix
  obtain ⟨ha, hu1⟩ := hdec a (u : ZMod 13) hu11 hfix
  exact ⟨ha, Units.ext hu1⟩

private lemma f13b_triv_stab : ∀ (a : ZMod 13) (u : (ZMod 13)ˣ),
    (∀ x : ZMod 13, (u : ZMod 13) * f13b (((u⁻¹ : (ZMod 13)ˣ) : ZMod 13) * x + a) +
      (f13b 0 - (u : ZMod 13) * f13b a) = f13b x) → a = 0 ∧ u = 1 := by
  have hdec : ∀ (a u : ZMod 13), u * u ^ 11 = 1 →
      (∀ x : ZMod 13, u * f13b (u ^ 11 * x + a) + (f13b 0 - u * f13b a) = f13b x) →
      a = 0 ∧ u = 1 := by
    decide
  have hpow : ∀ u : ZMod 13, (∃ v : ZMod 13, u * v = 1) → u * u ^ 11 = 1 := by decide
  intro a u hfix
  have hu11 : (u : ZMod 13) * (u : ZMod 13) ^ 11 = 1 :=
    hpow (u : ZMod 13) ⟨((u⁻¹ : (ZMod 13)ˣ) : ZMod 13), by exact_mod_cast Units.mul_inv u⟩
  have hinv_eq : ((u⁻¹ : (ZMod 13)ˣ) : ZMod 13) = (u : ZMod 13) ^ 11 := by
    have := congrArg (fun z => ((u⁻¹ : (ZMod 13)ˣ) : ZMod 13) * z) hu11
    simpa [← mul_assoc] using this.symm
  rw [hinv_eq] at hfix
  obtain ⟨ha, hu1⟩ := hdec a (u : ZMod 13) hu11 hfix
  exact ⟨ha, Units.ext hu1⟩

private lemma T_thirteen_ge : 2028 ≤ LatinSquare.T 13 := by
  have hf1 : Function.Injective f13a := by decide
  have hf2 : Function.Injective (fun x : ZMod 13 => x + f13a x) := by decide
  have h := zmod_orbit_le_T f13a hf1 hf2 f13a_triv_stab
  have htot : Nat.totient 13 = 12 := by decide
  rw [htot] at h
  exact h

private lemma T_fourteen_ge : 2496 ≤ LatinSquare.T 14 := by
  have hfa1 : Function.Injective f13a := by decide
  have hfa2 : Function.Injective (fun x : ZMod 13 => x + f13a x) := by decide
  have hfb1 : Function.Injective f13b := by decide
  have hfb2 : Function.Injective (fun x : ZMod 13 => x + f13b x) := by decide
  have hcoll_ne : coll1 f13a ≠ coll1 f13b := by decide
  let Da : Finset (ZMod 13) := {1, 2, 4, 5, 7, 8, 11, 12}
  let Db : Finset (ZMod 13) := {1, 2, 5, 6, 8, 10, 11, 12}
  have hDa_card : Da.card = 8 := by decide
  have hDb_card : Db.card = 8 := by decide
  have hDa_miss : ∀ d ∈ Da, ∀ y : ZMod 13, y - f13a y ≠ d := by decide
  have hDb_miss : ∀ d ∈ Db, ∀ y : ZMod 13, y - f13b y ≠ d := by decide
  let e : Fin 14 ≃ ZMod 13 ⊕ Fin 1 :=
    finSumFinEquiv.symm.trans (Equiv.sumCongr (finEquivZMod 13) (Equiv.refl (Fin 1)))
  let ιa := ({d : ZMod 13 // d ∈ Da} × ZMod 13) × (ZMod 13)ˣ
  let ιb := ({d : ZMod 13 // d ∈ Db} × ZMod 13) × (ZMod 13)ˣ
  let φ : (ιa ⊕ ιb) → ((ZMod 13 ⊕ Fin 1) → (ZMod 13 ⊕ Fin 1)) := fun z =>
    match z with
    | Sum.inl ⟨⟨d, a⟩, u⟩ => Sum.map (affAct a ((u : ZMod 13) * (d.1 - a)) u f13a) id
    | Sum.inr ⟨⟨d, a⟩, u⟩ => Sum.map (affAct a ((u : ZMod 13) * (d.1 - a)) u f13b) id
  have hinj : Function.Injective φ := by
    intro z₁ z₂ heq
    cases z₁ with
    | inl p₁ =>
      rcases p₁ with ⟨⟨d₁, a₁⟩, u₁⟩
      cases z₂ with
      | inl p₂ =>
        rcases p₂ with ⟨⟨d₂, a₂⟩, u₂⟩
        have haff : affAct a₁ ((u₁ : ZMod 13) * (d₁.1 - a₁)) u₁ f13a =
            affAct a₂ ((u₂ : ZMod 13) * (d₂.1 - a₂)) u₂ f13a := by
          funext x; exact Sum.inl.inj (congr_fun heq (Sum.inl x))
        have htriple := affAct_inj_of_triv_stab f13a f13a_triv_stab
          (a₁ := ((a₁, (u₁ : ZMod 13) * (d₁.1 - a₁)), u₁))
          (a₂ := ((a₂, (u₂ : ZMod 13) * (d₂.1 - a₂)), u₂)) haff
        have ha : a₁ = a₂ := (Prod.mk.inj (Prod.mk.inj htriple).1).1
        have hb : (u₁ : ZMod 13) * (d₁.1 - a₁) = (u₂ : ZMod 13) * (d₂.1 - a₂) :=
          (Prod.mk.inj (Prod.mk.inj htriple).1).2
        have hu : u₁ = u₂ := (Prod.mk.inj htriple).2
        subst ha; subst hu
        have hd1 : d₁.1 - a₁ = d₂.1 - a₁ := by
          have := congrArg (fun z => ((u₁⁻¹ : (ZMod 13)ˣ) : ZMod 13) * z) hb
          simpa [← mul_assoc] using this
        have hd : d₁ = d₂ := Subtype.ext (by linear_combination hd1)
        rw [hd]
      | inr p₂ =>
        rcases p₂ with ⟨⟨d₂, a₂⟩, u₂⟩
        exfalso
        have haff : affAct a₁ ((u₁ : ZMod 13) * (d₁.1 - a₁)) u₁ f13a =
            affAct a₂ ((u₂ : ZMod 13) * (d₂.1 - a₂)) u₂ f13b := by
          funext x; exact Sum.inl.inj (congr_fun heq (Sum.inl x))
        have hc := congrArg coll1 haff
        rw [coll1_affAct, coll1_affAct] at hc
        exact hcoll_ne hc
    | inr p₁ =>
      rcases p₁ with ⟨⟨d₁, a₁⟩, u₁⟩
      cases z₂ with
      | inl p₂ =>
        rcases p₂ with ⟨⟨d₂, a₂⟩, u₂⟩
        exfalso
        have haff : affAct a₁ ((u₁ : ZMod 13) * (d₁.1 - a₁)) u₁ f13b =
            affAct a₂ ((u₂ : ZMod 13) * (d₂.1 - a₂)) u₂ f13a := by
          funext x; exact Sum.inl.inj (congr_fun heq (Sum.inl x))
        have hc := congrArg coll1 haff
        rw [coll1_affAct, coll1_affAct] at hc
        exact hcoll_ne hc.symm
      | inr p₂ =>
        rcases p₂ with ⟨⟨d₂, a₂⟩, u₂⟩
        have haff : affAct a₁ ((u₁ : ZMod 13) * (d₁.1 - a₁)) u₁ f13b =
            affAct a₂ ((u₂ : ZMod 13) * (d₂.1 - a₂)) u₂ f13b := by
          funext x; exact Sum.inl.inj (congr_fun heq (Sum.inl x))
        have htriple := affAct_inj_of_triv_stab f13b f13b_triv_stab
          (a₁ := ((a₁, (u₁ : ZMod 13) * (d₁.1 - a₁)), u₁))
          (a₂ := ((a₂, (u₂ : ZMod 13) * (d₂.1 - a₂)), u₂)) haff
        have ha : a₁ = a₂ := (Prod.mk.inj (Prod.mk.inj htriple).1).1
        have hb : (u₁ : ZMod 13) * (d₁.1 - a₁) = (u₂ : ZMod 13) * (d₂.1 - a₂) :=
          (Prod.mk.inj (Prod.mk.inj htriple).1).2
        have hu : u₁ = u₂ := (Prod.mk.inj htriple).2
        subst ha; subst hu
        have hd1 : d₁.1 - a₁ = d₂.1 - a₁ := by
          have := congrArg (fun z => ((u₁⁻¹ : (ZMod 13)ˣ) : ZMod 13) * z) hb
          simpa [← mul_assoc] using this
        have hd : d₁ = d₂ := Subtype.ext (by linear_combination hd1)
        rw [hd]
  have htrans : ∀ k : ιa ⊕ ιb,
      Function.Injective (φ k) ∧
      Function.Injective (fun p => prolongZMod (cyclicLS 1) p (φ k p)) := by
    intro k
    cases k with
    | inl p =>
      rcases p with ⟨⟨d, a⟩, u⟩
      have ht := affAct_transversal a ((u : ZMod 13) * (d.1 - a)) u f13a hfa1 hfa2
      have hdiag := affAct_avoids_diag f13a d.1 a u (hDa_miss d.1 d.2)
      exact prolong1_extend_transversal _ ht.1 ht.2 hdiag
    | inr p =>
      rcases p with ⟨⟨d, a⟩, u⟩
      have ht := affAct_transversal a ((u : ZMod 13) * (d.1 - a)) u f13b hfb1 hfb2
      have hdiag := affAct_avoids_diag f13b d.1 a u (hDb_miss d.1 d.2)
      exact prolong1_extend_transversal _ ht.1 ht.2 hdiag
  have hle := card_le_T_of_family e (prolongZMod (cyclicLS 1))
    (prolongZMod_row_inj ⟨6, rfl⟩ (by omega) (cyclicLS 1))
    (prolongZMod_col_inj ⟨6, rfl⟩ (by omega) (cyclicLS 1))
    φ hinj htrans
  simp only [ιa, ιb, Fintype.card_sum, Fintype.card_prod, Fintype.card_coe, hDa_card, hDb_card,
    ZMod.card, ZMod.card_units_eq_totient] at hle
  have htot : Nat.totient 13 = 12 := by decide
  rw [htot] at hle
  exact hle

/- ### Piece 6: Strong Induction `15 ^ n ≤ (T n) ^ 5` for all `n ≥ 5`, then `15^(n/5) ≤ T n` -/

private lemma mul_pow_le_of_le {a b x y k c : ℕ} (h1 : a ≤ x) (h2 : b ≤ y) (h3 : x * y ^ k ≤ c) :
    a * b ^ k ≤ c :=
  le_trans (mul_le_mul' h1 (pow_le_pow_left₀ (Nat.zero_le _) h2 k)) h3

private lemma mul_pow_mul_le_of_le {a b d x y k c : ℕ} (h1 : a ≤ x) (h2 : b ≤ y)
    (h3 : d * x ^ k * y ≤ c) : d * a ^ k * b ≤ c :=
  le_trans (mul_le_mul' (mul_le_mul' (le_refl d) (pow_le_pow_left₀ (Nat.zero_le _) h1 k)) h2) h3

private lemma step_29 {t7 t29 : ℕ} (h7 : 15 ^ 7 ≤ t7 ^ 5) (hstep : 3 * t7 ^ 4 ≤ t29) :
    15 ^ 29 ≤ t29 ^ 5 := by
  calc 15 ^ 29 = 15 * (15 ^ 7) ^ 4 := by
        rw [show (29 : ℕ) = 1 + 7 * 4 by norm_num, pow_add, pow_mul, pow_one]
    _ ≤ 3 ^ 5 * (t7 ^ 5) ^ 4 :=
        mul_le_mul' (by norm_num) (pow_le_pow_left₀ (Nat.zero_le _) h7 4)
    _ = (3 * t7 ^ 4) ^ 5 := by ring
    _ ≤ t29 ^ 5 := pow_le_pow_left₀ (Nat.zero_le _) hstep 5

private lemma step_3q {n q tq tn : ℕ} (hnq : n = 3 * q) (hih : 15 ^ q ≤ tq ^ 5)
    (hstep : 3 * tq ^ 3 ≤ tn) : 15 ^ n ≤ tn ^ 5 := by
  calc 15 ^ n = (15 ^ q) ^ 3 := by rw [hnq, mul_comm, pow_mul]
    _ ≤ 1 * (tq ^ 5) ^ 3 := by rw [one_mul]; exact pow_le_pow_left₀ (Nat.zero_le _) hih 3
    _ ≤ 3 ^ 5 * (tq ^ 5) ^ 3 := mul_le_mul' (by norm_num) (le_refl _)
    _ = (3 * tq ^ 3) ^ 5 := by ring
    _ ≤ tn ^ 5 := pow_le_pow_left₀ (Nat.zero_le _) hstep 5

private lemma step_3q1 {n q tq tn : ℕ} (hnq : n = 3 * q + 1) (hih : 15 ^ q ≤ tq ^ 5)
    (hstep : 2 * tq ^ 3 ≤ tn) : 15 ^ n ≤ tn ^ 5 := by
  calc 15 ^ n = 15 * (15 ^ q) ^ 3 := by rw [hnq, pow_succ, mul_comm 3 q, pow_mul]; ring
    _ ≤ 2 ^ 5 * (tq ^ 5) ^ 3 :=
        mul_le_mul' (by norm_num) (pow_le_pow_left₀ (Nat.zero_le _) hih 3)
    _ = (2 * tq ^ 3) ^ 5 := by ring
    _ ≤ tn ^ 5 := pow_le_pow_left₀ (Nat.zero_le _) hstep 5

private lemma step_3qr {n q r tq tr tn : ℕ} (hnq : n = 3 * q + r) (hih : 15 ^ q ≤ tq ^ 5)
    (hr : 15 ^ r ≤ tr ^ 5) (hstep : 2 * tq ^ 3 * tr ≤ tn) : 15 ^ n ≤ tn ^ 5 := by
  calc 15 ^ n = 1 * (15 ^ q) ^ 3 * 15 ^ r := by rw [hnq, pow_add, mul_comm 3 q, pow_mul]; ring
    _ ≤ 2 ^ 5 * (tq ^ 5) ^ 3 * tr ^ 5 :=
        mul_le_mul' (mul_le_mul' (by norm_num) (pow_le_pow_left₀ (Nat.zero_le _) hih 3)) hr
    _ = (2 * tq ^ 3 * tr) ^ 5 := by ring
    _ ≤ tn ^ 5 := pow_le_pow_left₀ (Nat.zero_le _) hstep 5

private lemma pow_five_lower_bound :
    ∀ n : ℕ, 5 ≤ n → 15 ^ n ≤ (LatinSquare.T n) ^ 5 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    have hpow_le : ∀ {a b : ℕ}, a ≤ b → a ^ 5 ≤ b ^ 5 := fun h =>
      pow_le_pow_left₀ (Nat.zero_le _) h 5
    by_cases h19 : n ≤ 19
    · interval_cases n
      · exact le_trans (by norm_num) (hpow_le T_five_ge)
      · exact le_trans (by norm_num) (hpow_le T_six_ge)
      · exact le_trans (by norm_num) (hpow_le T_seven_ge)
      · exact le_trans (by norm_num) (hpow_le T_eight_ge)
      · exact le_trans (by norm_num) (hpow_le T_nine_ge)
      · exact le_trans (by norm_num) (hpow_le T_ten_ge)
      · exact le_trans (by norm_num) (hpow_le T_eleven_ge)
      · have h12 : 3 * 8 ^ 3 ≤ LatinSquare.T 12 := by
          have hm := T_mul_ge (a := 3) (b := 4) (by omega)
          rw [show 3 * 4 = 12 by norm_num] at hm
          exact mul_pow_le_of_le T_three_ge T_four_ge hm
        exact le_trans (by norm_num) (hpow_le h12)
      · exact le_trans (by norm_num) (hpow_le T_thirteen_ge)
      · exact le_trans (by norm_num) (hpow_le T_fourteen_ge)
      · have h15 : 3 * 15 ^ 3 ≤ LatinSquare.T 15 := by
          have hm := T_mul_ge (a := 3) (b := 5) (by omega)
          rw [show 3 * 5 = 15 by norm_num] at hm
          exact mul_pow_le_of_le T_three_ge T_five_ge hm
        have h15_num : 15 ^ 15 ≤ (3 * 15 ^ 3) ^ 5 := by
          rw [show (15 : ℕ) = 3 * 5 by norm_num, pow_mul]
          exact pow_le_pow_left₀ (Nat.zero_le _) (by norm_num) 5
        exact le_trans h15_num (hpow_le h15)
      · have h16 : 8 * 8 ^ 4 ≤ LatinSquare.T 16 := by
          have hm := T_mul_ge (a := 4) (b := 4) (by omega)
          rw [show 4 * 4 = 16 by norm_num] at hm
          exact mul_pow_le_of_le T_four_ge T_four_ge hm
        exact le_trans (by norm_num) (hpow_le h16)
      · have h17 : 3 * 8 ^ 4 ≤ LatinSquare.T 17 := by
          have hm := T_four_add_one (q := 4) (by omega)
          rw [show 4 * 4 + 1 = 17 by norm_num] at hm
          exact mul_pow_le_of_le (le_refl 3) T_four_ge hm
        exact le_trans (by norm_num) (hpow_le h17)
      · have h18 : 3 * 26 ^ 3 ≤ LatinSquare.T 18 := by
          have hm := T_mul_ge (a := 3) (b := 6) (by omega)
          rw [show 3 * 6 = 18 by norm_num] at hm
          exact mul_pow_le_of_le T_three_ge T_six_ge hm
        exact le_trans (by norm_num) (hpow_le h18)
      · have h19' : 2 * 15 ^ 3 * 8 ≤ LatinSquare.T 19 := by
          have hm := T_three_add_r (q := 5) (r := 4) ⟨2, rfl⟩ (by omega)
          rw [show 3 * 5 + 4 = 19 by norm_num] at hm
          exact mul_pow_mul_le_of_le T_five_ge T_four_ge hm
        have h19_num : 15 ^ 19 ≤ (2 * 15 ^ 3 * 8) ^ 5 := by
          calc 15 ^ 19 = 15 ^ 4 * (15 ^ 3) ^ 5 := by
                rw [show (19 : ℕ) = 4 + 3 * 5 by norm_num, pow_add, pow_mul]
            _ ≤ 16 ^ 5 * (15 ^ 3) ^ 5 := mul_le_mul' (by norm_num) (le_refl _)
            _ = (16 * 15 ^ 3) ^ 5 := (mul_pow _ _ _).symm
            _ = (2 * 15 ^ 3 * 8) ^ 5 := by congr 1
        exact le_trans h19_num (hpow_le h19')
    · -- n ≥ 20
      by_cases h20 : n = 20
      · subst h20
        have h : 8 * 15 ^ 4 ≤ LatinSquare.T 20 := by
          have hm := T_mul_ge (a := 4) (b := 5) (by omega)
          rw [show 4 * 5 = 20 by norm_num] at hm
          exact mul_pow_le_of_le T_four_ge T_five_ge hm
        have h20_num : 15 ^ 20 ≤ (8 * 15 ^ 4) ^ 5 := by
          rw [show (20 : ℕ) = 4 * 5 by norm_num, pow_mul]
          exact pow_le_pow_left₀ (Nat.zero_le _) (by norm_num) 5
        exact le_trans h20_num (hpow_le h)
      by_cases h23 : n = 23
      · subst h23
        have h : 3 * 15 ^ 4 * 3 ≤ LatinSquare.T 23 := by
          have hm := T_four_add_r (q := 5) (r := 3) ⟨2, rfl⟩ (by omega)
          rw [show 4 * 5 + 3 = 23 by norm_num] at hm
          exact mul_pow_mul_le_of_le T_five_ge T_three_ge hm
        have h23_num : 15 ^ 23 ≤ (3 * 15 ^ 4 * 3) ^ 5 := by
          calc 15 ^ 23 = 15 ^ 3 * (15 ^ 4) ^ 5 := by
                rw [show (23 : ℕ) = 3 + 4 * 5 by norm_num, pow_add, pow_mul]
            _ ≤ 9 ^ 5 * (15 ^ 4) ^ 5 := mul_le_mul' (by norm_num) (le_refl _)
            _ = (9 * 15 ^ 4) ^ 5 := (mul_pow _ _ _).symm
            _ = (3 * 15 ^ 4 * 3) ^ 5 := by congr 1
        exact le_trans h23_num (hpow_le h)
      by_cases h29 : n = 29
      · subst h29
        have hstep : 3 * LatinSquare.T 7 ^ 4 ≤ LatinSquare.T 29 := by
          have hm := T_four_add_one (q := 7) (by omega)
          rwa [show 4 * 7 + 1 = 29 by norm_num] at hm
        exact step_29 (ih 7 (by omega) (by omega)) hstep
      have hmod : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 6 = 2 ∨ n % 6 = 5 := by omega
      rcases hmod with h0 | h1 | h2 | h5
      · set q := n / 3
        have hnq : n = 3 * q := by omega
        have hstep : 3 * LatinSquare.T q ^ 3 ≤ LatinSquare.T n := by
          rw [hnq]
          exact le_trans (mul_le_mul' T_three_ge (le_refl _)) (T_mul_ge (a := 3) (b := q) (by omega))
        exact step_3q hnq (ih q (by omega) (by omega)) hstep
      · set q := (n - 1) / 3
        have hnq : n = 3 * q + 1 := by omega
        have hstep : 2 * LatinSquare.T q ^ 3 ≤ LatinSquare.T n := by
          rw [hnq]; exact T_three_add_one (by omega)
        exact step_3q1 hnq (ih q (by omega) (by omega)) hstep
      · set q := (n - 5) / 3
        have hnq : n = 3 * q + 5 := by omega
        have hodd : Odd q := ⟨(q - 1) / 2, by omega⟩
        have hstep : 2 * LatinSquare.T q ^ 3 * LatinSquare.T 5 ≤ LatinSquare.T n := by
          rw [hnq]; exact T_three_add_r hodd (by omega)
        exact step_3qr hnq (ih q (by omega) (by omega)) (ih 5 (by omega) (by omega)) hstep
      · set q := (n - 8) / 3
        have hnq : n = 3 * q + 8 := by omega
        have hodd : Odd q := ⟨(q - 1) / 2, by omega⟩
        have hstep : 2 * LatinSquare.T q ^ 3 * LatinSquare.T 8 ≤ LatinSquare.T n := by
          rw [hnq]; exact T_three_add_r hodd (by omega)
        exact step_3qr hnq (ih q (by omega) (by omega)) (ih 8 (by omega) (by omega)) hstep

theorem lower_bound_T :
    ∀ n : ℕ, n ≥ 5 → (15 : ℝ) ^ ((n : ℝ) / 5) ≤ (LatinSquare.T n : ℝ) := by
  intro n hn
  have hnat : (15 : ℝ) ^ n ≤ (LatinSquare.T n : ℝ) ^ 5 := by
    exact_mod_cast pow_five_lower_bound n hn
  have hnn15 : (0 : ℝ) ≤ (15 : ℝ) ^ n := by positivity
  have hnnT : (0 : ℝ) ≤ (LatinSquare.T n : ℝ) := Nat.cast_nonneg _
  have hle := Real.rpow_le_rpow hnn15 hnat (by positivity : (0 : ℝ) ≤ 1 / 5)
  have hL : ((15 : ℝ) ^ n) ^ ((1 : ℝ) / 5) = (15 : ℝ) ^ ((n : ℝ) / 5) := by
    rw [← Real.rpow_natCast (15 : ℝ) n, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 15)]
    ring_nf
  have hR : ((LatinSquare.T n : ℝ) ^ 5) ^ ((1 : ℝ) / 5) = (LatinSquare.T n : ℝ) := by
    rw [← Real.rpow_natCast (LatinSquare.T n : ℝ) 5, ← Real.rpow_mul hnnT]
    norm_num
  rw [hL, hR] at hle
  exact hle

end StrategyCLower

theorem OMA.solution : type_of% @LatinSquare.maxTransversalsBound := by
  intro c n hn
  exact ⟨StrategyCLower.lower_bound_T n hn, StrategyCUpper.upper_bound_T n hn⟩
