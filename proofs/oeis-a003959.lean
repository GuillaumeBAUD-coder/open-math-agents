import OMAStatements.S_oeis_a003959

-- Problem: A003959: If n = Product p(k)^e(k) then a(n) = Product (p(k)+1)^e(k), a(1) = 1.
-- Upstream: formal-conjectures statements/oeis-a003959.lean:0 (declaration OMA.S_oeis_a003959.main)
-- Credit: @nerotulip90 (the owner of the agent is credited as the solver)
-- Proof: a is completely multiplicative; absolute convergence for Re s > 2 via the Euler
-- product over smooth numbers, then Mathlib's Euler product for completely multiplicative
-- functions.

open OMA.S_oeis_a003959

namespace W4A3959

lemma a_mul {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) : a (m * n) = a m * a n := by
  unfold a
  rw [Nat.factorization_mul hm hn]
  exact Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)

lemma a_one : a 1 = 1 := by simp [a]

lemma a_prime {p : ℕ} (hp : p.Prime) : a p = p + 1 := by
  unfold a
  rw [hp.factorization, Finsupp.prod_single_index] <;> simp

/-- the real comparison function -/
noncomputable def G (σ : ℝ) : ℕ →*₀ ℝ where
  toFun n := if n = 0 then 0 else (a n : ℝ) * (n : ℝ) ^ (-σ)
  map_zero' := by simp
  map_one' := by simp [a_one]
  map_mul' m n := by
    by_cases hm : m = 0
    · simp [hm]
    by_cases hn : n = 0
    · simp [hn]
    simp only [mul_eq_zero, hm, hn, or_self, if_false, a_mul hm hn, Nat.cast_mul]
    rw [Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
    ring

noncomputable def F (s : ℂ) : ℕ →*₀ ℂ where
  toFun n := if n = 0 then 0 else (a n : ℂ) * (n : ℂ) ^ (-s)
  map_zero' := by simp
  map_one' := by simp [a_one]
  map_mul' m n := by
    by_cases hm : m = 0
    · simp [hm]
    by_cases hn : n = 0
    · simp [hn]
    simp only [mul_eq_zero, hm, hn, or_self, if_false, a_mul hm hn, Nat.cast_mul]
    rw [Complex.natCast_mul_natCast_cpow]
    ring

lemma G_nonneg (σ : ℝ) (n : ℕ) : 0 ≤ G σ n := by
  show 0 ≤ (if n = 0 then 0 else (a n : ℝ) * (n : ℝ) ^ (-σ))
  split_ifs
  · exact le_rfl
  · exact mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)

lemma norm_F (s : ℂ) (n : ℕ) : ‖F s n‖ = G s.re n := by
  show ‖(if n = 0 then 0 else (a n : ℂ) * (n : ℂ) ^ (-s))‖ =
    (if n = 0 then 0 else (a n : ℝ) * (n : ℝ) ^ (-s.re))
  split_ifs with h
  · simp
  · rw [norm_mul, Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero h)]
    simp

lemma G_prime {σ : ℝ} (hσ : 2 < σ) {p : ℕ} (hp : p.Prime) :
    G σ p ≤ 2 * (p : ℝ) ^ (1 - σ) ∧ G σ p ≤ 3 / 4 := by
  have hp0 : p ≠ 0 := hp.ne_zero
  have hG : G σ p = ((p : ℝ) + 1) * (p : ℝ) ^ (-σ) := by
    show (if p = 0 then 0 else (a p : ℝ) * (p : ℝ) ^ (-σ)) = _
    rw [if_neg hp0, a_prime hp]; push_cast; ring
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hpos : (0 : ℝ) < p := by linarith
  have e1 : (p : ℝ) ^ (1 - σ) = p * (p : ℝ) ^ (-σ) := by
    rw [show (1 - σ) = 1 + (-σ) by ring, Real.rpow_add hpos, Real.rpow_one]
  have hle : (p : ℝ) ^ (-σ) ≤ (p : ℝ) ^ (-2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have e2 : (p : ℝ) ^ (-2 : ℝ) = 1 / (p : ℝ) ^ 2 := by
    rw [Real.rpow_neg hpos.le, one_div]; norm_cast
  have hnn : 0 ≤ (p : ℝ) ^ (-σ) := Real.rpow_nonneg hpos.le _
  constructor
  · rw [hG, e1]; nlinarith
  · rw [hG]
    calc ((p : ℝ) + 1) * (p : ℝ) ^ (-σ) ≤ ((p : ℝ) + 1) * (1 / (p : ℝ) ^ 2) := by
          rw [← e2]; exact mul_le_mul_of_nonneg_left hle (by linarith)
      _ ≤ 3 / 4 := by
          rw [mul_one_div, div_le_iff₀ (by positivity)]; nlinarith

lemma inv_le_exp {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 3 / 4) : (1 - x)⁻¹ ≤ Real.exp (4 * x) := by
  have hpos : 0 < 1 - x := by linarith
  rw [inv_le_iff_one_le_mul₀' hpos]
  have := Real.add_one_le_exp (4 * x)
  nlinarith

lemma summable_G {σ : ℝ} (hσ : 2 < σ) : Summable (fun n => G σ n) := by
  have hS : Summable (fun n : ℕ => 2 * (n : ℝ) ^ (1 - σ)) :=
    (Real.summable_nat_rpow.mpr (by linarith)).mul_left 2
  set C := ∑' n : ℕ, 2 * (n : ℝ) ^ (1 - σ)
  have hlt : ∀ {p : ℕ}, p.Prime → ‖(G σ : ℕ →* ℝ) p‖ < 1 := by
    intro p hp
    have := (G_prime hσ hp).2
    show ‖G σ p‖ < 1
    rw [Real.norm_of_nonneg (G_nonneg σ p)]
    linarith
  refine summable_of_sum_range_le (G_nonneg σ) (c := Real.exp (4 * C)) fun N => ?_
  obtain ⟨hsm, hhas⟩ := EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric
    hlt N
  have hsm' : Summable (fun m : N.smoothNumbers => G σ m) := by
    refine hsm.congr fun m => ?_
    exact Real.norm_of_nonneg (G_nonneg σ m)
  -- step 1: finite sum ≤ sum over smooth numbers
  have step1 : ∑ i ∈ Finset.range N, G σ i ≤ ∑' m : N.smoothNumbers, G σ m := by
    have hsub : ∑ i ∈ Finset.range N, G σ i =
        ∑ i ∈ (Finset.range N).subtype (· ∈ N.smoothNumbers), G σ i := by
      rw [Finset.sum_subtype_eq_sum_filter]
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro x hx hx'
      simp only [Finset.mem_filter, not_and] at hx'
      have : x = 0 := by
        by_contra h0
        exact hx' hx (Nat.mem_smoothNumbers_of_lt (Nat.pos_of_ne_zero h0) (Finset.mem_range.mp hx))
      subst this; simp
    rw [hsub]
    exact hsm'.sum_le_tsum _ (fun i _ => G_nonneg σ i)
  -- step 2: the product bound
  have step2 : ∑' m : N.smoothNumbers, G σ m ≤ Real.exp (4 * C) := by
    have hhas' : HasSum (fun m : N.smoothNumbers => G σ m)
        (∏ p ∈ N.primesBelow, (1 - G σ p)⁻¹) := hhas
    rw [hhas'.tsum_eq]
    calc ∏ p ∈ N.primesBelow, (1 - G σ p)⁻¹
        ≤ ∏ p ∈ N.primesBelow, Real.exp (4 * G σ p) := by
          apply Finset.prod_le_prod
          · intro p hp
            have hpp := (Nat.mem_primesBelow.mp hp).2
            have := (G_prime hσ hpp).2
            exact inv_nonneg.mpr (by show 0 ≤ 1 - G σ p; linarith)
          · intro p hp
            have hpp := (Nat.mem_primesBelow.mp hp).2
            exact inv_le_exp (G_nonneg σ p) (G_prime hσ hpp).2
      _ = Real.exp (4 * ∑ p ∈ N.primesBelow, G σ p) := by
          rw [← Real.exp_sum, Finset.mul_sum]
      _ ≤ Real.exp (4 * C) := by
          apply Real.exp_le_exp.mpr
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          calc ∑ p ∈ N.primesBelow, G σ p ≤ ∑ p ∈ N.primesBelow, 2 * (p : ℝ) ^ (1 - σ) :=
                Finset.sum_le_sum fun p hp => (G_prime hσ (Nat.mem_primesBelow.mp hp).2).1
            _ ≤ C := hS.sum_le_tsum _ (fun i _ => by positivity)
  linarith

theorem main_proof : ∀ s : ℂ, 2 < s.re →
      LSeries (fun n => (a n : ℂ)) s =
        ∏' p : Nat.Primes, (1 - (p : ℂ) ^ (-s) - (p : ℂ) ^ (1 - s))⁻¹ := by
  intro s hs
  have hsum : Summable (fun n => ‖F s n‖) := by
    have := summable_G hs
    refine this.congr fun n => ?_
    rw [norm_F]
  have hE := EulerProduct.eulerProduct_completely_multiplicative_tprod hsum
  have hL : LSeries (fun n => (a n : ℂ)) s = ∑' n, F s n := by
    unfold LSeries
    congr 1
    funext n
    rw [LSeries.term_def]
    show _ = (if n = 0 then 0 else (a n : ℂ) * (n : ℂ) ^ (-s))
    split_ifs with h
    · rfl
    · rw [Complex.cpow_neg, div_eq_mul_inv]
  rw [hL, ← hE]
  congr 1
  funext p
  congr 1
  show 1 - (if (p : ℕ) = 0 then 0 else (a p : ℂ) * ((p : ℕ) : ℂ) ^ (-s)) = _
  rw [if_neg p.prop.ne_zero, a_prime p.prop]
  have hp0 : ((p : ℕ) : ℂ) ≠ 0 := by exact_mod_cast p.prop.ne_zero
  rw [show (1 - s) = 1 + (-s) by ring, Complex.cpow_add _ _ hp0, Complex.cpow_one]
  push_cast
  ring

end W4A3959

theorem OMA.solution : type_of% @OMA.S_oeis_a003959.main := W4A3959.main_proof
