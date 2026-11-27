import OMAReductions.R_Erdos360_erdos_360_R1

/-!
# Proof of Step H3 of Erdős Problem 360 (`Erdos360.erdos_360.R1.H3`)

We verify the existence of a valid scale `y` for Conlon–Fox–Pham's lower bound window using
Chebyshev bounds (`Chebyshev.eventually_primeCounting_le` and `Chebyshev.theta_ge`), a dyadic
bound on the reciprocal sum of primes, and Euler's product formula for `Nat.totient`.
-/

-- Step Erdos360.erdos_360.R1.H3: hypothesis H3 of reduction Erdos360.erdos_360.R1
-- Credit: @green-notes

open Filter Asymptotics

section Helpers

private lemma inv_one_sub_inv_le_exp {p : ℝ} (hp : 2 ≤ p) :
    (1 - 1 / p)⁻¹ ≤ Real.exp (2 / p) := by
  have hp0 : 0 < p := by linarith
  have hp1 : 0 < p - 1 := by linarith
  have hsub : 1 - 1 / p = (p - 1) / p := by field_simp
  rw [hsub, inv_div]
  have hsplit : p / (p - 1) = 1 / (p - 1) + 1 := by field_simp; ring
  rw [hsplit]
  refine (Real.add_one_le_exp (1 / (p - 1))).trans (Real.exp_le_exp.mpr ?_)
  rw [div_le_div_iff₀ hp1 hp0]
  linarith

private lemma exp_neg_le_one_sub_inv {p : ℝ} (hp : 2 ≤ p) :
    Real.exp (- (2 / p)) ≤ 1 - 1 / p := by
  have hp0 : 0 < p := by linarith
  have hpos : 0 < 1 - 1 / p := by rw [sub_pos, div_lt_one hp0]; linarith
  have h1 := inv_one_sub_inv_le_exp hp
  rw [Real.exp_neg]
  simpa using inv_anti₀ (inv_pos.mpr hpos) h1

private lemma nth_prime_lower :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 2 ≤ k → (k : ℝ) * Real.log (k : ℝ) ≤ C * (Nat.nth Nat.Prime k : ℝ) := by
  have hev := Chebyshev.eventually_primeCounting_le (ε := 1 / 2) (by norm_num)
  have htend : Tendsto (fun k : ℕ ↦ (Nat.nth Nat.Prime k : ℝ)) atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro b
    refine ⟨⌈b⌉₊, fun k hk ↦ ?_⟩
    have h1 : b ≤ (k : ℝ) := (Nat.le_ceil b).trans (by exact_mod_cast hk)
    have h2 : k ≤ Nat.nth Nat.Prime k := (Nat.add_two_le_nth_prime k).trans' (by omega)
    exact h1.trans (by exact_mod_cast h2)
  have hev_k := htend.eventually hev
  rw [eventually_atTop] at hev_k
  obtain ⟨K₀, hK₀⟩ := hev_k
  let term : ℕ → ℝ := fun j ↦ (j : ℝ) * Real.log (j : ℝ) / (Nat.nth Nat.Prime j : ℝ)
  let K := max K₀ 2
  let C := max (Real.log 4 + 1 / 2) (∑ k ∈ Finset.Ico 2 K, term k + 1)
  have hCpos : 0 < C := by
    refine lt_of_lt_of_le ?_ (le_max_left _ _)
    have : 0 < Real.log 4 := Real.log_pos (by norm_num)
    linarith
  refine ⟨C, hCpos, fun k hk ↦ ?_⟩
  by_cases hlt : k < K
  · have hmem : k ∈ Finset.Ico 2 K := Finset.mem_Ico.mpr ⟨hk, hlt⟩
    have hterm_nonneg : ∀ j ∈ Finset.Ico 2 K, 0 ≤ term j := by
      intro j hj
      have hj2 : (1 : ℝ) ≤ (j : ℝ) := by
        exact_mod_cast (show 1 ≤ j by have := (Finset.mem_Ico.mp hj).1; omega)
      have hlog : 0 ≤ Real.log (j : ℝ) := Real.log_nonneg hj2
      dsimp only [term]
      positivity
    have hterm_le : term k ≤ ∑ j ∈ Finset.Ico 2 K, term j :=
      Finset.single_le_sum hterm_nonneg hmem
    have hmax : ∑ j ∈ Finset.Ico 2 K, term j + 1 ≤ C := le_max_right _ _
    have hleC : term k ≤ C := by linarith
    have hp_pos : (0 : ℝ) < (Nat.nth Nat.Prime k : ℝ) := by
      exact_mod_cast (Nat.add_two_le_nth_prime k).trans_lt' (by omega)
    exact (div_le_iff₀ hp_pos).mp hleC
  · have hkK₀ : K₀ ≤ k := (le_max_left K₀ 2).trans (not_lt.mp hlt)
    have hpi := hK₀ k hkK₀
    have hfl : ⌊(Nat.nth Nat.Prime k : ℝ)⌋₊ = Nat.nth Nat.Prime k := Nat.floor_natCast _
    rw [hfl] at hpi
    have hk_le_pi : k ≤ Nat.primeCounting (Nat.nth Nat.Prime k) := by
      calc k = Nat.primeCounting' (Nat.nth Nat.Prime k) := (Nat.primeCounting'_nth_eq k).symm
        _ ≤ Nat.primeCounting' (Nat.nth Nat.Prime k + 1) :=
          Nat.monotone_primeCounting' (Nat.le_succ _)
        _ = Nat.primeCounting (Nat.nth Nat.Prime k) := rfl
    have hkp : k ≤ Nat.nth Nat.Prime k := by
      have := Nat.add_two_le_nth_prime k
      omega
    have hk_pos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
    have hp2 : (2 : ℝ) ≤ (Nat.nth Nat.Prime k : ℝ) := by
      exact_mod_cast (Nat.add_two_le_nth_prime k).trans' (by omega)
    have hlogp_pos : 0 < Real.log (Nat.nth Nat.Prime k : ℝ) := Real.log_pos (by linarith)
    have h1 : (k : ℝ) ≤ (Real.log 4 + 1 / 2) * (Nat.nth Nat.Prime k : ℝ) /
        Real.log (Nat.nth Nat.Prime k : ℝ) :=
      (by exact_mod_cast hk_le_pi : (k : ℝ) ≤ Nat.primeCounting (Nat.nth Nat.Prime k)).trans hpi
    have h2 : (k : ℝ) * Real.log (Nat.nth Nat.Prime k : ℝ) ≤
        (Real.log 4 + 1 / 2) * (Nat.nth Nat.Prime k : ℝ) := (le_div_iff₀ hlogp_pos).mp h1
    have hlog_le : Real.log (k : ℝ) ≤ Real.log (Nat.nth Nat.Prime k : ℝ) :=
      Real.log_le_log hk_pos (by exact_mod_cast hkp)
    have h3 : (k : ℝ) * Real.log (k : ℝ) ≤ (Real.log 4 + 1 / 2) * (Nat.nth Nat.Prime k : ℝ) :=
      (mul_le_mul_of_nonneg_left hlog_le hk_pos.le).trans h2
    exact h3.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))

private lemma exp_one_lt_three : Real.exp 1 < 3 :=
  lt_trans Real.exp_one_lt_d9 (by norm_num)

private lemma log_thirty_gt_three : 3 < Real.log 30 := by
  rw [← Real.log_exp 3]
  refine Real.log_lt_log (Real.exp_pos 3) ?_
  have hexp3 : Real.exp 3 = (Real.exp 1) ^ 3 := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [hexp3]
  have hpow : (Real.exp 1) ^ 3 < 3 ^ 3 := by
    gcongr
    exact exp_one_lt_three
  linarith

private lemma log_log_thirty_gt_one : 1 < Real.log (Real.log 30) := by
  rw [← Real.log_exp 1]
  exact Real.log_lt_log (Real.exp_pos 1) (lt_trans exp_one_lt_three log_thirty_gt_three)

private lemma log_two_lt_one : Real.log 2 < 1 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  linarith [Real.add_one_lt_exp (one_ne_zero : (1 : ℝ) ≠ 0)]

private lemma sum_inv_nth_prime_le :
    ∃ D : ℝ, 0 < D ∧ ∀ r : ℕ, 30 ≤ r →
      ∑ i ∈ Finset.range r, (Nat.nth Nat.Prime i : ℝ)⁻¹ ≤ D * Real.log (Real.log r) := by
  obtain ⟨C, hCpos, hC⟩ := nth_prime_lower
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let D : ℝ := 4 + (C / Real.log 2) * (1 + Real.log (2 / Real.log 2)) + C / Real.log 2
  have hDpos : 0 < D := by
    have h2 : 1 < 2 / Real.log 2 := (one_lt_div hlog2_pos).mpr (by linarith [log_two_lt_one])
    have hlog_pos : 0 < Real.log (2 / Real.log 2) := Real.log_pos h2
    positivity
  refine ⟨D, hDpos, fun r hr30 ↦ ?_⟩
  have hr4 : 4 ≤ r := by omega
  have hsplit : Finset.range r = Finset.range 4 ∪ Finset.Ico 4 r := by
    ext i
    simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Ico]
    omega
  have hdisj : Disjoint (Finset.range 4) (Finset.Ico 4 r) := by
    rw [Finset.disjoint_left]
    intro i h1 h2
    rw [Finset.mem_range] at h1
    rw [Finset.mem_Ico] at h2
    omega
  rw [hsplit, Finset.sum_union hdisj]
  have hhead : ∑ i ∈ Finset.range 4, (Nat.nth Nat.Prime i : ℝ)⁻¹ ≤ 4 := by
    calc ∑ i ∈ Finset.range 4, (Nat.nth Nat.Prime i : ℝ)⁻¹
        ≤ ∑ _ ∈ Finset.range 4, (1 : ℝ) := by
          refine Finset.sum_le_sum fun i _ ↦ ?_
          have hp2 : (2 : ℝ) ≤ (Nat.nth Nat.Prime i : ℝ) := by
            exact_mod_cast (Nat.add_two_le_nth_prime i).trans' (by omega)
          exact inv_le_one_of_one_le₀ (by linarith)
      _ = 4 := by simp
  let K := Nat.log 2 r + 1
  have hK4 : 4 ≤ Nat.log 2 r := by
    rw [Nat.le_log_iff_pow_le (by norm_num) (by omega)]
    omega
  have hK5 : 5 ≤ K := by omega
  have hsub_dyad : Finset.Ico 4 r ⊆
      (Finset.Ico 2 K).biUnion (fun m ↦ Finset.Ico (2 ^ m) (2 ^ (m + 1))) := by
    intro i hi
    rw [Finset.mem_Ico] at hi
    rw [Finset.mem_biUnion]
    let m := Nat.log 2 i
    refine ⟨m, Finset.mem_Ico.mpr ⟨?_, ?_⟩, Finset.mem_Ico.mpr ⟨?_, ?_⟩⟩
    · rw [Nat.le_log_iff_pow_le (by norm_num) (by omega)]
      omega
    · have hm_le : m ≤ Nat.log 2 r := Nat.log_mono_right hi.2.le
      omega
    · exact Nat.pow_log_le_self 2 (by omega)
    · exact Nat.lt_pow_succ_log_self (by norm_num) i
  have htail_le : ∑ i ∈ Finset.Ico 4 r, (Nat.nth Nat.Prime i : ℝ)⁻¹ ≤
      ∑ m ∈ Finset.Ico 2 K,
        ∑ i ∈ Finset.Ico (2 ^ m) (2 ^ (m + 1)), (Nat.nth Nat.Prime i : ℝ)⁻¹ := by
    have hdisj_dyad : (Finset.Ico 2 K : Set ℕ).PairwiseDisjoint
        (fun m ↦ Finset.Ico (2 ^ m) (2 ^ (m + 1))) := by
      intro m₁ _ m₂ _ hne
      rw [Function.onFun, Finset.disjoint_left]
      intro i hi1 hi2
      rw [Finset.mem_Ico] at hi1 hi2
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hpow : 2 ^ (m₁ + 1) ≤ 2 ^ m₂ := Nat.pow_le_pow_right (by norm_num) hlt
        omega
      · have hpow : 2 ^ (m₂ + 1) ≤ 2 ^ m₁ := Nat.pow_le_pow_right (by norm_num) hgt
        omega
    calc ∑ i ∈ Finset.Ico 4 r, (Nat.nth Nat.Prime i : ℝ)⁻¹
        ≤ ∑ i ∈ (Finset.Ico 2 K).biUnion (fun m ↦ Finset.Ico (2 ^ m) (2 ^ (m + 1))),
            (Nat.nth Nat.Prime i : ℝ)⁻¹ :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub_dyad fun _ _ _ ↦ by positivity
      _ = ∑ m ∈ Finset.Ico 2 K,
            ∑ i ∈ Finset.Ico (2 ^ m) (2 ^ (m + 1)), (Nat.nth Nat.Prime i : ℝ)⁻¹ :=
          Finset.sum_biUnion hdisj_dyad
  have hblock : ∀ m ∈ Finset.Ico 2 K,
      ∑ i ∈ Finset.Ico (2 ^ m) (2 ^ (m + 1)), (Nat.nth Nat.Prime i : ℝ)⁻¹ ≤
        (C / Real.log 2) * (m : ℝ)⁻¹ := by
    intro m hm
    rw [Finset.mem_Ico] at hm
    have hm2 : 2 ≤ m := hm.1
    have hm_pos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
    have h2m_pos : (0 : ℝ) < (2 ^ m : ℕ) := by positivity
    have hterm : ∀ i ∈ Finset.Ico (2 ^ m) (2 ^ (m + 1)),
        (Nat.nth Nat.Prime i : ℝ)⁻¹ ≤ C / ((2 ^ m : ℝ) * (m * Real.log 2)) := by
      intro i hi
      rw [Finset.mem_Ico] at hi
      have hi4 : 4 ≤ i := (show 4 ≤ 2 ^ m by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2).trans hi.1
      have hi2 : 2 ≤ i := by omega
      have hp_pos : (0 : ℝ) < (Nat.nth Nat.Prime i : ℝ) := by
        exact_mod_cast (Nat.add_two_le_nth_prime i).trans_lt' (by omega)
      have hCi := hC i hi2
      have hi_ge : (2 ^ m : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi.1
      have hlog_ge : (m : ℝ) * Real.log 2 ≤ Real.log (i : ℝ) := by
        have hpow : Real.log ((2 : ℝ) ^ m) = (m : ℝ) * Real.log 2 := Real.log_pow 2 m
        rw [← hpow]
        exact Real.log_le_log (by positivity) (by exact_mod_cast hi.1)
      have hden_le : (2 ^ m : ℝ) * (m * Real.log 2) ≤ (i : ℝ) * Real.log (i : ℝ) := by
        exact mul_le_mul hi_ge hlog_ge (by positivity) (by positivity)
      have hmul_pos : 0 < (2 ^ m : ℝ) * (m * Real.log 2) := by positivity
      have hCi' : (2 ^ m : ℝ) * (m * Real.log 2) ≤ C * (Nat.nth Nat.Prime i : ℝ) :=
        hden_le.trans hCi
      rw [inv_eq_one_div, div_le_div_iff₀ hp_pos hmul_pos]
      linarith
    have hsum_b : ∑ i ∈ Finset.Ico (2 ^ m) (2 ^ (m + 1)), (Nat.nth Nat.Prime i : ℝ)⁻¹ ≤
        ((Finset.Ico (2 ^ m) (2 ^ (m + 1))).card : ℝ) *
          (C / ((2 ^ m : ℝ) * (m * Real.log 2))) := by
      calc ∑ i ∈ Finset.Ico (2 ^ m) (2 ^ (m + 1)), (Nat.nth Nat.Prime i : ℝ)⁻¹
          ≤ ∑ _ ∈ Finset.Ico (2 ^ m) (2 ^ (m + 1)),
              (C / ((2 ^ m : ℝ) * (m * Real.log 2))) := Finset.sum_le_sum hterm
        _ = _ := by simp
    have hcard : (Finset.Ico (2 ^ m) (2 ^ (m + 1))).card = 2 ^ m := by
      rw [Nat.card_Ico]
      have hpow2 : 2 ^ (m + 1) = 2 ^ m + 2 ^ m := by ring
      rw [hpow2, Nat.add_sub_cancel]
    rw [hcard] at hsum_b
    refine hsum_b.trans_eq ?_
    push_cast
    field_simp
  have hsum_blocks : ∑ m ∈ Finset.Ico 2 K,
      ∑ i ∈ Finset.Ico (2 ^ m) (2 ^ (m + 1)), (Nat.nth Nat.Prime i : ℝ)⁻¹ ≤
      (C / Real.log 2) * (1 + Real.log K) := by
    calc ∑ m ∈ Finset.Ico 2 K,
          ∑ i ∈ Finset.Ico (2 ^ m) (2 ^ (m + 1)), (Nat.nth Nat.Prime i : ℝ)⁻¹
        ≤ ∑ m ∈ Finset.Ico 2 K, (C / Real.log 2) * (m : ℝ)⁻¹ := Finset.sum_le_sum hblock
      _ = (C / Real.log 2) * ∑ m ∈ Finset.Ico 2 K, (m : ℝ)⁻¹ := (Finset.mul_sum _ _ _).symm
      _ ≤ (C / Real.log 2) * ∑ m ∈ Finset.Icc 1 K, (m : ℝ)⁻¹ := by
          gcongr
          intro m hm
          rw [Finset.mem_Ico] at hm
          rw [Finset.mem_Icc]
          omega
      _ = (C / Real.log 2) * (harmonic K : ℝ) := by
          rw [harmonic_eq_sum_Icc]
          push_cast
          rfl
      _ ≤ (C / Real.log 2) * (1 + Real.log K) := by
          gcongr
          exact harmonic_le_one_add_log K
  have hlogr3 : 3 < Real.log (r : ℝ) :=
    lt_of_lt_of_le log_thirty_gt_three (Real.log_le_log (by norm_num) (by exact_mod_cast hr30))
  have hloglogr1 : 1 < Real.log (Real.log (r : ℝ)) :=
    lt_of_lt_of_le log_log_thirty_gt_one
      (Real.log_le_log (by linarith [log_thirty_gt_three])
        (Real.log_le_log (by norm_num) (by exact_mod_cast hr30)))
  have hK_le : (K : ℝ) ≤ (2 / Real.log 2) * Real.log (r : ℝ) := by
    have hpow_le : (2 : ℝ) ^ (Nat.log 2 r) ≤ (r : ℝ) := by
      exact_mod_cast Nat.pow_log_le_self 2 (by omega)
    have hlog_pow : (Nat.log 2 r : ℝ) * Real.log 2 ≤ Real.log (r : ℝ) := by
      rw [← Real.log_pow]
      exact Real.log_le_log (by positivity) hpow_le
    have hlogr_div : (Nat.log 2 r : ℝ) ≤ Real.log (r : ℝ) / Real.log 2 :=
      (le_div_iff₀ hlog2_pos).mpr hlog_pow
    have hK4' : (4 : ℝ) ≤ (Nat.log 2 r : ℝ) := by exact_mod_cast hK4
    have hK_real : (K : ℝ) = (Nat.log 2 r : ℝ) + 1 := by push_cast [K]; rfl
    rw [hK_real]
    have : (1 : ℝ) ≤ Real.log (r : ℝ) / Real.log 2 := by
      linarith
    linarith [show (2 / Real.log 2) * Real.log (r : ℝ) = 2 * (Real.log (r : ℝ) / Real.log 2) by ring]
  have hlogK_le : Real.log (K : ℝ) ≤ Real.log (2 / Real.log 2) + Real.log (Real.log (r : ℝ)) := by
    have hK_pos : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
    calc Real.log (K : ℝ)
        ≤ Real.log ((2 / Real.log 2) * Real.log (r : ℝ)) := Real.log_le_log hK_pos hK_le
      _ = Real.log (2 / Real.log 2) + Real.log (Real.log (r : ℝ)) :=
        Real.log_mul (by positivity) (by linarith)
  have hfinal_tail : ∑ i ∈ Finset.Ico 4 r, (Nat.nth Nat.Prime i : ℝ)⁻¹ ≤
      (C / Real.log 2) * (1 + Real.log (2 / Real.log 2) + Real.log (Real.log (r : ℝ))) := by
    have h1K : 1 + Real.log (K : ℝ) ≤ 1 + Real.log (2 / Real.log 2) + Real.log (Real.log (r : ℝ)) := by
      linarith
    exact htail_le.trans (hsum_blocks.trans (mul_le_mul_of_nonneg_left h1K (by positivity)))
  calc ∑ i ∈ Finset.range 4, (Nat.nth Nat.Prime i : ℝ)⁻¹ +
        ∑ i ∈ Finset.Ico 4 r, (Nat.nth Nat.Prime i : ℝ)⁻¹
      ≤ 4 + (C / Real.log 2) * (1 + Real.log (2 / Real.log 2) + Real.log (Real.log (r : ℝ))) :=
        add_le_add hhead hfinal_tail
    _ = (4 + (C / Real.log 2) * (1 + Real.log (2 / Real.log 2))) * 1 +
          (C / Real.log 2) * Real.log (Real.log (r : ℝ)) := by ring
    _ ≤ (4 + (C / Real.log 2) * (1 + Real.log (2 / Real.log 2))) * Real.log (Real.log (r : ℝ)) +
          (C / Real.log 2) * Real.log (Real.log (r : ℝ)) := by
        have hpos_coef : 0 ≤ 4 + (C / Real.log 2) * (1 + Real.log (2 / Real.log 2)) := by
          have h2 : 1 < 2 / Real.log 2 := (one_lt_div hlog2_pos).mpr (by linarith [log_two_lt_one])
          have : 0 < Real.log (2 / Real.log 2) := Real.log_pos h2
          positivity
        have := mul_le_mul_of_nonneg_left hloglogr1.le hpos_coef
        linarith
    _ = D * Real.log (Real.log (r : ℝ)) := by ring

private lemma prod_nth_prime_bounds :
    ∃ M : ℕ, 1 ≤ M ∧ ∀ r : ℕ,
      (Real.log ((r : ℝ) + 30) ^ M)⁻¹ ≤
        ∏ i ∈ Finset.range r, (1 - (1 : ℝ) / (Nat.nth Nat.Prime i : ℝ)) ∧
      ∏ i ∈ Finset.range r, (1 - (1 : ℝ) / (Nat.nth Nat.Prime i : ℝ))⁻¹ ≤
        Real.log ((r : ℝ) + 30) ^ M := by
  obtain ⟨D, hDpos, hD⟩ := sum_inv_nth_prime_le
  let M : ℕ := max (⌈2 * D⌉₊) 1
  have hM1 : 1 ≤ M := le_max_right _ _
  have h2DM : 2 * D ≤ (M : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast le_max_left (⌈2 * D⌉₊) 1)
  refine ⟨M, hM1, fun r ↦ ?_⟩
  let R := max r 30
  have hrR : r ≤ R := le_max_left _ _
  have hR30 : 30 ≤ R := le_max_right _ _
  have hRr30 : (R : ℝ) ≤ (r : ℝ) + 30 := by exact_mod_cast (by omega : R ≤ r + 30)
  have hlogR3 : 3 < Real.log (R : ℝ) :=
    lt_of_lt_of_le log_thirty_gt_three (Real.log_le_log (by norm_num) (by exact_mod_cast hR30))
  have hloglogR_pos : 0 < Real.log (Real.log (R : ℝ)) := Real.log_pos (by linarith)
  have hsum_le : 2 * ∑ i ∈ Finset.range r, (Nat.nth Nat.Prime i : ℝ)⁻¹ ≤
      (M : ℝ) * Real.log (Real.log ((r : ℝ) + 30)) := by
    have h1 : ∑ i ∈ Finset.range r, (Nat.nth Nat.Prime i : ℝ)⁻¹ ≤
        ∑ i ∈ Finset.range R, (Nat.nth Nat.Prime i : ℝ)⁻¹ :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hrR) fun _ _ _ ↦ by positivity
    have h2 : ∑ i ∈ Finset.range R, (Nat.nth Nat.Prime i : ℝ)⁻¹ ≤ D * Real.log (Real.log (R : ℝ)) :=
      hD R hR30
    have h3 : Real.log (Real.log (R : ℝ)) ≤ Real.log (Real.log ((r : ℝ) + 30)) :=
      Real.log_le_log (by linarith) (Real.log_le_log (by exact_mod_cast (by omega : 0 < R)) hRr30)
    calc 2 * ∑ i ∈ Finset.range r, (Nat.nth Nat.Prime i : ℝ)⁻¹
        ≤ 2 * (D * Real.log (Real.log (R : ℝ))) := by linarith
      _ = (2 * D) * Real.log (Real.log (R : ℝ)) := by ring
      _ ≤ (M : ℝ) * Real.log (Real.log (R : ℝ)) :=
          mul_le_mul_of_nonneg_right h2DM hloglogR_pos.le
      _ ≤ (M : ℝ) * Real.log (Real.log ((r : ℝ) + 30)) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
  have hlogr30_pos : 0 < Real.log ((r : ℝ) + 30) := by
    refine lt_trans (by norm_num : (0 : ℝ) < 3) ?_
    refine lt_of_lt_of_le log_thirty_gt_three (Real.log_le_log (by norm_num) ?_)
    linarith [show (0 : ℝ) ≤ r by positivity]
  have hexp_pow : Real.exp (2 * ∑ i ∈ Finset.range r, (Nat.nth Nat.Prime i : ℝ)⁻¹) ≤
      Real.log ((r : ℝ) + 30) ^ M := by
    calc Real.exp (2 * ∑ i ∈ Finset.range r, (Nat.nth Nat.Prime i : ℝ)⁻¹)
        ≤ Real.exp ((M : ℝ) * Real.log (Real.log ((r : ℝ) + 30))) := Real.exp_le_exp.mpr hsum_le
      _ = Real.exp (Real.log (Real.log ((r : ℝ) + 30) ^ M)) := by
          rw [Real.log_pow]
      _ = Real.log ((r : ℝ) + 30) ^ M := Real.exp_log (pow_pos hlogr30_pos M)
  constructor
  · have hprod_exp : Real.exp (- (2 * ∑ i ∈ Finset.range r, (Nat.nth Nat.Prime i : ℝ)⁻¹)) ≤
        ∏ i ∈ Finset.range r, (1 - (1 : ℝ) / (Nat.nth Nat.Prime i : ℝ)) := by
      have heq : - (2 * ∑ i ∈ Finset.range r, (Nat.nth Nat.Prime i : ℝ)⁻¹) =
          ∑ i ∈ Finset.range r, - (2 / (Nat.nth Nat.Prime i : ℝ)) := by
        rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        ring
      rw [heq, Real.exp_sum]
      refine Finset.prod_le_prod (fun _ _ ↦ (Real.exp_pos _).le) fun i _ ↦ ?_
      have hp2 : (2 : ℝ) ≤ (Nat.nth Nat.Prime i : ℝ) := by
        exact_mod_cast (Nat.add_two_le_nth_prime i).trans' (by omega)
      exact exp_neg_le_one_sub_inv hp2
    have hinv_exp : (Real.log ((r : ℝ) + 30) ^ M)⁻¹ ≤
        Real.exp (- (2 * ∑ i ∈ Finset.range r, (Nat.nth Nat.Prime i : ℝ)⁻¹)) := by
      rw [Real.exp_neg]
      exact inv_anti₀ (Real.exp_pos _) hexp_pow
    exact hinv_exp.trans hprod_exp
  · have hprod_exp : ∏ i ∈ Finset.range r, (1 - (1 : ℝ) / (Nat.nth Nat.Prime i : ℝ))⁻¹ ≤
        Real.exp (2 * ∑ i ∈ Finset.range r, (Nat.nth Nat.Prime i : ℝ)⁻¹) := by
      have heq : 2 * ∑ i ∈ Finset.range r, (Nat.nth Nat.Prime i : ℝ)⁻¹ =
          ∑ i ∈ Finset.range r, (2 / (Nat.nth Nat.Prime i : ℝ)) := by
        simp_rw [div_eq_mul_inv, ← Finset.mul_sum]
      rw [heq, Real.exp_sum]
      refine Finset.prod_le_prod (fun i _ ↦ ?_) fun i _ ↦ ?_
      · have hp2 : (2 : ℝ) ≤ (Nat.nth Nat.Prime i : ℝ) := by
          exact_mod_cast (Nat.add_two_le_nth_prime i).trans' (by omega)
        have hpos : 0 < 1 - (1 : ℝ) / (Nat.nth Nat.Prime i : ℝ) := by
          rw [sub_pos, div_lt_one (by linarith)]
          linarith
        exact (inv_pos.mpr hpos).le
      · have hp2 : (2 : ℝ) ≤ (Nat.nth Nat.Prime i : ℝ) := by
          exact_mod_cast (Nat.add_two_le_nth_prime i).trans' (by omega)
        exact inv_one_sub_inv_le_exp hp2
    exact hprod_exp.trans hexp_pow

private lemma nth_prime_le_orderEmb {k : ℕ} (S : Finset ℕ) (hcard : S.card = k)
    (hprime : ∀ p ∈ S, p.Prime) :
    ∀ i : ℕ, ∀ hi : i < k, Nat.nth Nat.Prime i ≤ S.orderEmbOfFin hcard ⟨i, hi⟩ := by
  intro i
  induction i with
  | zero =>
    intro hi
    rw [Nat.nth_prime_zero_eq_two]
    exact (hprime _ (Finset.orderEmbOfFin_mem S hcard ⟨0, hi⟩)).two_le
  | succ i ih =>
    intro hi
    have hi0 : i < k := Nat.lt_of_succ_lt hi
    have h1 : Nat.nth Nat.Prime i ≤ S.orderEmbOfFin hcard ⟨i, hi0⟩ := ih hi0
    have h2 : S.orderEmbOfFin hcard ⟨i, hi0⟩ < S.orderEmbOfFin hcard ⟨i + 1, hi⟩ :=
      (S.orderEmbOfFin hcard).strictMono (Fin.mk_lt_mk.mpr (Nat.lt_succ_self i))
    have hlt : Nat.nth Nat.Prime i < S.orderEmbOfFin hcard ⟨i + 1, hi⟩ := lt_of_le_of_lt h1 h2
    have hq : (S.orderEmbOfFin hcard ⟨i + 1, hi⟩).Prime :=
      hprime _ (Finset.orderEmbOfFin_mem S hcard ⟨i + 1, hi⟩)
    have hcnt_lt : Nat.count Nat.Prime (Nat.nth Nat.Prime i) <
        Nat.count Nat.Prime (S.orderEmbOfFin hcard ⟨i + 1, hi⟩) := by
      have hsub := Nat.count_monotone Nat.Prime hlt.le
      have hsucc : Nat.count Nat.Prime (Nat.nth Nat.Prime i + 1) ≤
          Nat.count Nat.Prime (S.orderEmbOfFin hcard ⟨i + 1, hi⟩) :=
        Nat.count_monotone Nat.Prime hlt
      rw [Nat.count_nth_succ_of_infinite Nat.infinite_setOfPred_prime] at hsucc
      rw [Nat.count_nth_of_infinite Nat.infinite_setOfPred_prime]
      omega
    rw [Nat.count_nth_of_infinite Nat.infinite_setOfPred_prime] at hcnt_lt
    calc Nat.nth Nat.Prime (i + 1)
        ≤ Nat.nth Nat.Prime (Nat.count Nat.Prime (S.orderEmbOfFin hcard ⟨i + 1, hi⟩)) :=
          Nat.nth_monotone Nat.infinite_setOfPred_prime hcnt_lt
      _ = S.orderEmbOfFin hcard ⟨i + 1, hi⟩ := Nat.nth_count hq

private lemma theta_ge_linear :
    ∃ A : ℝ, 0 < A ∧ ∀ P : ℕ, (P : ℝ) ≤ A * Chebyshev.theta P + A := by
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have ho1 : Real.log =o[atTop] (fun x : ℝ ↦ x ^ (1 : ℝ)) :=
    isLittleO_log_rpow_atTop one_pos
  have ho2 : (fun x : ℝ ↦ Real.sqrt x * Real.log x) =o[atTop] (fun x : ℝ ↦ x ^ (1 : ℝ)) := by
    have h : Real.log =o[atTop] (fun x : ℝ ↦ x ^ (1 / 2 : ℝ)) :=
      isLittleO_log_rpow_atTop (by norm_num)
    have hmul : (fun x : ℝ ↦ Real.sqrt x * Real.log x) =o[atTop]
        (fun x : ℝ ↦ Real.sqrt x * x ^ (1 / 2 : ℝ)) :=
      (isBigO_refl Real.sqrt atTop).mul_isLittleO h
    refine hmul.trans_eventuallyEq ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add' hx (by norm_num)]
    norm_num
  have hb1 := ho1.bound (by positivity : 0 < Real.log 2 / 8)
  have hb2 := ho2.bound (by positivity : 0 < Real.log 2 / 8)
  have hev : ∀ᶠ x : ℝ in atTop,
      Real.log (x + 1) ≤ Real.log 2 / 4 * x ∧
      2 * Real.sqrt x * Real.log x ≤ Real.log 2 / 4 * x := by
    filter_upwards [hb1, hb2, eventually_ge_atTop (8 : ℝ)] with x h1 h2 hx8
    have hlogx : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
    rw [Real.norm_of_nonneg hlogx, Real.rpow_one, Real.norm_of_nonneg (by linarith)] at h1
    rw [Real.norm_of_nonneg (by positivity), Real.rpow_one, Real.norm_of_nonneg (by linarith)] at h2
    have hlog_add : Real.log (x + 1) ≤ Real.log 2 + Real.log x := by
      calc Real.log (x + 1) ≤ Real.log (2 * x) := Real.log_le_log (by linarith) (by linarith)
        _ = Real.log 2 + Real.log x := Real.log_mul (by norm_num) (by linarith)
    have hlog2_le : Real.log 2 ≤ Real.log 2 / 8 * x := by nlinarith
    exact ⟨by linarith, by linarith⟩
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.mp (hev.and (eventually_ge_atTop (4 / Real.log 2)))
  let A : ℝ := max (4 / Real.log 2) (max X₀ 1)
  have hApos : 0 < A := lt_of_lt_of_le (by positivity) (le_max_left _ _)
  refine ⟨A, hApos, fun P ↦ ?_⟩
  by_cases hPX : (P : ℝ) < X₀
  · have hPA : (P : ℝ) ≤ A := hPX.le.trans ((le_max_left _ _).trans (le_max_right _ _))
    have hth : 0 ≤ Chebyshev.theta P := Chebyshev.theta_nonneg P
    nlinarith
  · have hP_ge : X₀ ≤ (P : ℝ) := not_lt.mp hPX
    obtain ⟨⟨h1, h2⟩, hP_big⟩ := hX₀ P hP_ge
    have hth_ge := Chebyshev.theta_ge P
    have hhalf : Real.log 2 / 2 * (P : ℝ) ≤ Chebyshev.theta P + Real.log 2 / 4 := by linarith
    have h4 : (4 / Real.log 2) ≤ A := le_max_left _ _
    have hth : 0 ≤ Chebyshev.theta P := Chebyshev.theta_nonneg P
    have hP_pos : 0 ≤ (P : ℝ) := by positivity
    have h3 : (P : ℝ) ≤ (2 / Real.log 2) * Chebyshev.theta P + 1 / 2 := by
      have hPeq : (P : ℝ) = (2 / Real.log 2) * (Real.log 2 / 2 * (P : ℝ)) := by
        field_simp [hlog2_pos.ne']
      calc (P : ℝ) = (2 / Real.log 2) * (Real.log 2 / 2 * (P : ℝ)) := hPeq
        _ ≤ (2 / Real.log 2) * (Chebyshev.theta P + Real.log 2 / 4) := by gcongr
        _ = (2 / Real.log 2) * Chebyshev.theta P + 1 / 2 := by
            field_simp [hlog2_pos.ne']
            ring
    have h24 : 2 / Real.log 2 ≤ A := by
      calc 2 / Real.log 2 ≤ 4 / Real.log 2 := by gcongr; norm_num
        _ ≤ A := h4
    have h1A : 1 / 2 ≤ A := (by norm_num : (1 / 2 : ℝ) ≤ 1).trans
      ((le_max_right X₀ 1).trans (le_max_right _ _))
    calc (P : ℝ) ≤ (2 / Real.log 2) * Chebyshev.theta P + 1 / 2 := h3
      _ ≤ A * Chebyshev.theta P + A := add_le_add (mul_le_mul_of_nonneg_right h24 hth) h1A

private lemma totient_ratio_eventually_le :
    ∃ M : ℕ, 1 ≤ M ∧ ∀ᶠ n : ℕ in atTop,
      (n : ℝ) / (n.totient : ℝ) ≤ (2 : ℝ) ^ M * Real.log (Real.log n) ^ M := by
  obtain ⟨M, hM1, hprod⟩ := prod_nth_prime_bounds
  obtain ⟨A, hApos, htheta⟩ := theta_ge_linear
  refine ⟨M, hM1, ?_⟩
  have hev : ∀ᶠ n : ℕ in atTop, 3 ≤ n ∧ A * Real.log n + A + 31 ≤ Real.log n ^ 2 := by
    let X₁ := max (2 * A) (Real.sqrt (2 * (A + 31)) + 1)
    have hcomp := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop X₁)
    filter_upwards [eventually_ge_atTop 3, hcomp] with n hn3 hx
    dsimp only [Function.comp_def] at hx
    refine ⟨hn3, ?_⟩
    have hx1 : 2 * A ≤ Real.log (n : ℝ) := (le_max_left _ _).trans hx
    have hx2 : Real.sqrt (2 * (A + 31)) ≤ Real.log (n : ℝ) := by
      have hle := (le_max_right (2 * A) (Real.sqrt (2 * (A + 31)) + 1)).trans hx
      linarith
    have hsq2 : 2 * (A + 31) ≤ Real.log (n : ℝ) ^ 2 := by
      have hpow := pow_le_pow_left₀ (Real.sqrt_nonneg _) hx2 2
      rwa [Real.sq_sqrt (by positivity)] at hpow
    have hlog_nn : 0 ≤ Real.log (n : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
    have hmul : 2 * A * Real.log (n : ℝ) ≤ Real.log (n : ℝ) ^ 2 := by nlinarith
    linarith
  filter_upwards [hev] with n ⟨hn3, hlog_sq⟩
  have hn_pos : 0 < n := by omega
  let k := n.primeFactors.card
  have hk_le_theta : (k : ℝ) ≤ A * Real.log n + A + 1 := by
    by_cases hk0 : k = 0
    · simp [hk0]
      positivity
    · have hk1 : 1 ≤ k := Nat.pos_of_ne_zero hk0
      let P := Nat.nth Nat.Prime (k - 1)
      have hP_prim : primorial P = ∏ i ∈ Finset.range k, Nat.nth Nat.Prime i := by
        rw [primorial_eq_prod_primesLE]
        have himg : Nat.primesLE P = (Finset.range k).image (Nat.nth Nat.Prime) := by
          ext p
          simp only [Nat.mem_primesLE, Finset.mem_image, Finset.mem_range]
          constructor
          · rintro ⟨hp_le, hp_pr⟩
            refine ⟨Nat.count Nat.Prime p, ?_, Nat.nth_count hp_pr⟩
            have hcnt_le : Nat.count Nat.Prime p ≤ Nat.count Nat.Prime P :=
              Nat.count_monotone Nat.Prime hp_le
            rw [Nat.count_nth_of_infinite Nat.infinite_setOfPred_prime] at hcnt_le
            omega
          · rintro ⟨i, hi, rfl⟩
            exact ⟨Nat.nth_monotone Nat.infinite_setOfPred_prime (by omega),
              Nat.prime_nth_prime i⟩
        rw [himg, Finset.prod_image]
        intro i _ j _ hij
        exact (Nat.nth_strictMono Nat.infinite_setOfPred_prime).injective hij
      have hprod_le : primorial P ≤ n := by
        rw [hP_prim]
        have h1 : ∏ i ∈ Finset.range k, Nat.nth Nat.Prime i =
            ∏ i : Fin k, Nat.nth Nat.Prime i.1 := by
          rw [← Fin.prod_univ_eq_prod_range]
        have h2 : ∏ i : Fin k, Nat.nth Nat.Prime i.1 ≤
            ∏ i : Fin k, n.primeFactors.orderEmbOfFin rfl i := by
          refine Finset.prod_le_prod' fun i _ ↦ ?_
          exact nth_prime_le_orderEmb n.primeFactors rfl (fun p hp ↦ Nat.prime_of_mem_primeFactors hp) i.1 i.2
        have h3 : ∏ i : Fin k, n.primeFactors.orderEmbOfFin rfl i =
            ∏ p ∈ n.primeFactors, p := by
          refine Finset.prod_bij (fun i _ ↦ n.primeFactors.orderEmbOfFin rfl i)
            (fun i _ ↦ Finset.orderEmbOfFin_mem _ _ i)
            (fun i _ j _ hij ↦ (n.primeFactors.orderEmbOfFin rfl).injective hij)
            (fun p hp ↦ ?_) (fun _ _ ↦ rfl)
          exact ⟨⟨n.primeFactors.orderIsoOfFin rfl |>.symm ⟨p, hp⟩ |>.1,
            (n.primeFactors.orderIsoOfFin rfl |>.symm ⟨p, hp⟩).2⟩, Finset.mem_univ _, by
              simp [Finset.orderEmbOfFin]⟩
        have h4 : ∏ p ∈ n.primeFactors, p ≤ n :=
          Nat.le_of_dvd hn_pos (Nat.prod_primeFactors_dvd n)
        exact (h1.trans_le h2).trans (h3.le.trans h4)
      have hth_le : Chebyshev.theta P ≤ Real.log n := by
        rw [Chebyshev.theta_eq_log_primorial]
        have hfl : ⌊(P : ℝ)⌋₊ = P := Nat.floor_natCast P
        rw [hfl]
        exact Real.log_le_log (by exact_mod_cast primorial_pos P) (by exact_mod_cast hprod_le)
      have hk_le_P : (k : ℝ) ≤ (P : ℝ) + 1 := by
        have := Nat.add_two_le_nth_prime (k - 1)
        exact_mod_cast (by omega : k ≤ P + 1)
      calc (k : ℝ) ≤ (P : ℝ) + 1 := hk_le_P
        _ ≤ A * Chebyshev.theta P + A + 1 := by linarith [htheta P]
        _ ≤ A * Real.log n + A + 1 := by linarith [mul_le_mul_of_nonneg_left hth_le hApos.le]
  have htot_eq : (n : ℝ) / (n.totient : ℝ) =
      ∏ p ∈ n.primeFactors, (1 - (1 : ℝ) / (p : ℝ))⁻¹ := by
    have hq := congrArg ((↑) : ℚ → ℝ) (Nat.totient_eq_mul_prod_factors n)
    push_cast at hq
    have htot_pos : (0 : ℝ) < n.totient := by exact_mod_cast Nat.totient_pos.mpr hn_pos
    have hn_r : (0 : ℝ) < n := by exact_mod_cast hn_pos
    have hprod_ne : (∏ p ∈ n.primeFactors, (1 - (1 : ℝ) / (p : ℝ))) ≠ 0 := by
      refine Finset.prod_ne_zero_iff.mpr fun p hp ↦ ?_
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
      have hdiv_lt : (1 : ℝ) / (p : ℝ) < 1 := (div_lt_one (by linarith)).mpr (by linarith)
      linarith
    have hq' : (n.totient : ℝ) = (n : ℝ) * ∏ p ∈ n.primeFactors, (1 - (1 : ℝ) / (p : ℝ)) := by
      simpa only [one_div] using hq
    rw [hq', div_mul_eq_div_div, div_self hn_r.ne', one_div, Finset.prod_inv_distrib]
  have hprod_le_nth : ∏ p ∈ n.primeFactors, (1 - (1 : ℝ) / (p : ℝ))⁻¹ ≤
      ∏ i ∈ Finset.range k, (1 - (1 : ℝ) / (Nat.nth Nat.Prime i : ℝ))⁻¹ := by
    have heq_f : ∏ p ∈ n.primeFactors, (1 - (1 : ℝ) / (p : ℝ))⁻¹ =
        ∏ i : Fin k, (1 - (1 : ℝ) / (n.primeFactors.orderEmbOfFin rfl i : ℝ))⁻¹ := by
      refine (Finset.prod_bij (fun i _ ↦ n.primeFactors.orderEmbOfFin rfl i)
        (fun i _ ↦ Finset.orderEmbOfFin_mem _ _ i)
        (fun i _ j _ hij ↦ (n.primeFactors.orderEmbOfFin rfl).injective hij)
        (fun p hp ↦ ⟨(n.primeFactors.orderIsoOfFin rfl).symm ⟨p, hp⟩, Finset.mem_univ _, by
          simp [Finset.orderEmbOfFin]⟩) (fun _ _ ↦ rfl)).symm
    have heq_r : ∏ i ∈ Finset.range k, (1 - (1 : ℝ) / (Nat.nth Nat.Prime i : ℝ))⁻¹ =
        ∏ i : Fin k, (1 - (1 : ℝ) / (Nat.nth Nat.Prime i.1 : ℝ))⁻¹ := by
      rw [← Fin.prod_univ_eq_prod_range]
    rw [heq_f, heq_r]
    refine Finset.prod_le_prod (fun i _ ↦ ?_) fun i _ ↦ ?_
    · have hp2 : (2 : ℝ) ≤ n.primeFactors.orderEmbOfFin rfl i := by
        exact_mod_cast (Nat.prime_of_mem_primeFactors (Finset.orderEmbOfFin_mem _ _ i)).two_le
      have hpos : 0 < 1 - (1 : ℝ) / (n.primeFactors.orderEmbOfFin rfl i : ℝ) := by
        rw [sub_pos, div_lt_one (by linarith)]
        linarith
      exact (inv_pos.mpr hpos).le
    · have hle := nth_prime_le_orderEmb n.primeFactors rfl
        (fun p hp ↦ Nat.prime_of_mem_primeFactors hp) i.1 i.2
      have hp2 : (2 : ℝ) ≤ Nat.nth Nat.Prime i.1 := by
        exact_mod_cast (Nat.add_two_le_nth_prime i.1).trans' (by omega)
      have hpos : 0 < 1 - (1 : ℝ) / (Nat.nth Nat.Prime i.1 : ℝ) := by
        rw [sub_pos, div_lt_one (by linarith)]
        linarith
      refine inv_anti₀ hpos ?_
      have hle' : (Nat.nth Nat.Prime i.1 : ℝ) ≤ n.primeFactors.orderEmbOfFin rfl i := by
        exact_mod_cast hle
      gcongr
  have hk30 : (k : ℝ) + 30 ≤ Real.log n ^ 2 := by linarith
  have hlog_k : Real.log ((k : ℝ) + 30) ≤ 2 * Real.log (Real.log n) := by
    have hk_pos : 0 < (k : ℝ) + 30 := by positivity
    calc Real.log ((k : ℝ) + 30)
        ≤ Real.log (Real.log n ^ 2) := Real.log_le_log hk_pos hk30
      _ = 2 * Real.log (Real.log n) := by rw [Real.log_pow]; norm_num
  have hk_nonneg : 0 ≤ Real.log ((k : ℝ) + 30) := by
    refine Real.log_nonneg ?_
    linarith [show (0 : ℝ) ≤ k by positivity]
  calc (n : ℝ) / (n.totient : ℝ)
      = ∏ p ∈ n.primeFactors, (1 - (1 : ℝ) / (p : ℝ))⁻¹ := htot_eq
    _ ≤ ∏ i ∈ Finset.range k, (1 - (1 : ℝ) / (Nat.nth Nat.Prime i : ℝ))⁻¹ := hprod_le_nth
    _ ≤ Real.log ((k : ℝ) + 30) ^ M := (hprod k).2
    _ ≤ (2 * Real.log (Real.log n)) ^ M := pow_le_pow_left₀ hk_nonneg hlog_k M
    _ = (2 : ℝ) ^ M * Real.log (Real.log n) ^ M := mul_pow _ _ _

end Helpers

set_option maxHeartbeats 800000 in
theorem OMA.solution : OMA.R_Erdos360_erdos_360_R1.H3 := by
  intro c hc
  obtain ⟨M₁, hM₁_pos, hprod⟩ := prod_nth_prime_bounds
  obtain ⟨M₂, hM₂_pos, htot_ev⟩ := totient_ratio_eventually_le
  have hlog_rpow_1_12 : Real.log =o[atTop] (fun x : ℝ ↦ x ^ (1 / 12 : ℝ)) :=
    isLittleO_log_rpow_atTop (by norm_num)
  have hlog_rpow_2M1 : (fun x : ℝ ↦ Real.log x ^ (2 * M₁)) =o[atTop] (fun x : ℝ ↦ x ^ (1 / 3 : ℝ)) := by
    simpa only [Real.rpow_natCast] using isLittleO_log_rpow_rpow_atTop (2 * M₁ : ℕ) (by norm_num)
  have hlog_rpow_M2 : (fun x : ℝ ↦ Real.log x ^ M₂) =o[atTop] (fun x : ℝ ↦ x ^ (1 / 2 : ℝ)) := by
    simpa only [Real.rpow_natCast] using isLittleO_log_rpow_rpow_atTop (M₂ : ℕ) (by norm_num)
  have hloglog_3M2 : (fun x : ℝ ↦ Real.log (Real.log x) ^ (3 * M₂)) =o[atTop] Real.log := by
    have h := isLittleO_log_rpow_rpow_atTop (3 * M₂ : ℕ) one_pos
    simpa only [Function.comp_def, Real.rpow_natCast, Real.rpow_one] using
      h.comp_tendsto Real.tendsto_log_atTop
  have hlog_n_ev : ∀ᶠ n : ℕ in atTop,
      30 ≤ n ∧
      Real.exp 3 < (n : ℝ) ∧
      Real.log (n : ℝ) ≤ (n : ℝ) ^ (1 / 12 : ℝ) ∧
      (15 : ℝ)⁻¹ ≤ c * (n : ℝ) ^ (1 / 20 : ℝ) / 2 ∧
      (2 : ℝ) ≤ c * (n : ℝ) ^ (1 / 4 : ℝ) ∧
      (c * (2 : ℝ) ^ M₂) ^ 3 * Real.log (Real.log n) ^ (3 * M₂) ≤ 15 * Real.log n ∧
      (n : ℝ) ^ (1 / 3 : ℝ) * (c * (2 : ℝ) ^ M₂ * Real.log n ^ M₂) + 30 ≤ (n : ℝ) ∧
      80 * c * (2 : ℝ) ^ M₂ * Real.log n ^ (2 * M₁) * Real.log n ^ M₂ < (n : ℝ) ^ (2 / 3 : ℝ) := by
    have hn30 : ∀ᶠ n : ℕ in atTop, 30 ≤ n := eventually_ge_atTop 30
    have hexp3 : ∀ᶠ n : ℕ in atTop, Real.exp 3 < (n : ℝ) :=
      (tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop (Real.exp 3)))
    have h1_12 : ∀ᶠ n : ℕ in atTop, Real.log (n : ℝ) ≤ (n : ℝ) ^ (1 / 12 : ℝ) := by
      have h := tendsto_natCast_atTop_atTop.eventually (hlog_rpow_1_12.bound one_pos)
      filter_upwards [h, eventually_ge_atTop 3] with n hn hn3
      have hlog0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
      rw [Real.norm_of_nonneg hlog0, Real.norm_of_nonneg (by positivity), one_mul] at hn
      exact hn
    have h20 : ∀ᶠ n : ℕ in atTop, (15 : ℝ)⁻¹ ≤ c * (n : ℝ) ^ (1 / 20 : ℝ) / 2 := by
      have ht := (_root_.tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 20)).comp
        tendsto_natCast_atTop_atTop
      filter_upwards [ht.eventually (eventually_ge_atTop ((2 / c) * (15 : ℝ)⁻¹))] with n hn
      calc (15 : ℝ)⁻¹ = c * ((2 / c) * (15 : ℝ)⁻¹) / 2 := by field_simp
        _ ≤ c * (n : ℝ) ^ (1 / 20 : ℝ) / 2 :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hn hc.le) (by norm_num)
    have h1_4 : ∀ᶠ n : ℕ in atTop, (2 : ℝ) ≤ c * (n : ℝ) ^ (1 / 4 : ℝ) := by
      have ht := (_root_.tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp
        tendsto_natCast_atTop_atTop
      filter_upwards [ht.eventually (eventually_ge_atTop (2 / c))] with n hn
      calc (2 : ℝ) = c * (2 / c) := by field_simp
        _ ≤ c * (n : ℝ) ^ (1 / 4 : ℝ) := mul_le_mul_of_nonneg_left hn hc.le
    have h3M2 : ∀ᶠ n : ℕ in atTop,
        (c * (2 : ℝ) ^ M₂) ^ 3 * Real.log (Real.log n) ^ (3 * M₂) ≤ 15 * Real.log n := by
      have hε : 0 < 15 / ((c * (2 : ℝ) ^ M₂) ^ 3 + 1) := by positivity
      have hb := tendsto_natCast_atTop_atTop.eventually (hloglog_3M2.bound hε)
      filter_upwards [hb, hexp3] with n hn hn_exp
      have hlog3 : 3 < Real.log (n : ℝ) := by
        rw [← Real.log_exp 3]
        exact Real.log_lt_log (Real.exp_pos 3) hn_exp
      have hloglog1 : 1 < Real.log (Real.log (n : ℝ)) := by
        rw [← Real.log_exp 1]
        exact Real.log_lt_log (Real.exp_pos 1) (lt_trans exp_one_lt_three hlog3)
      rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by linarith)] at hn
      have h1 : (c * (2 : ℝ) ^ M₂) ^ 3 * Real.log (Real.log n) ^ (3 * M₂) ≤
          ((c * (2 : ℝ) ^ M₂) ^ 3 + 1) * Real.log (Real.log n) ^ (3 * M₂) := by
        gcongr
        linarith
      refine h1.trans ?_
      calc ((c * (2 : ℝ) ^ M₂) ^ 3 + 1) * Real.log (Real.log n) ^ (3 * M₂)
          ≤ ((c * (2 : ℝ) ^ M₂) ^ 3 + 1) * (15 / ((c * (2 : ℝ) ^ M₂) ^ 3 + 1) * Real.log n) := by
            gcongr
        _ = 15 * Real.log n := by field_simp
    have hM2_bound : ∀ᶠ n : ℕ in atTop,
        (n : ℝ) ^ (1 / 3 : ℝ) * (c * (2 : ℝ) ^ M₂ * Real.log n ^ M₂) + 30 ≤ (n : ℝ) := by
      have hε : 0 < (2 * (c * (2 : ℝ) ^ M₂ + 1))⁻¹ := by positivity
      have hb := tendsto_natCast_atTop_atTop.eventually (hlog_rpow_M2.bound hε)
      filter_upwards [hb, eventually_ge_atTop 60] with n hn hn60
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
      have hlog_nn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
      rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)] at hn
      have h1 : c * (2 : ℝ) ^ M₂ * Real.log (n : ℝ) ^ M₂ ≤ (1 / 2 : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ) := by
        calc c * (2 : ℝ) ^ M₂ * Real.log (n : ℝ) ^ M₂
            ≤ (c * (2 : ℝ) ^ M₂ + 1) * Real.log (n : ℝ) ^ M₂ := by gcongr; linarith
          _ ≤ (c * (2 : ℝ) ^ M₂ + 1) * ((2 * (c * (2 : ℝ) ^ M₂ + 1))⁻¹ * (n : ℝ) ^ (1 / 2 : ℝ)) := by
              gcongr
          _ = (1 / 2 : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ) := by field_simp
      have hpow_le : (n : ℝ) ^ (1 / 3 : ℝ) * ((1 / 2 : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ)) ≤
          (1 / 2 : ℝ) * (n : ℝ) := by
        have hrw : (n : ℝ) ^ (1 / 3 : ℝ) * ((1 / 2 : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ)) =
            (1 / 2 : ℝ) * (n : ℝ) ^ (5 / 6 : ℝ) := by
          have : (n : ℝ) ^ (1 / 3 : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ) = (n : ℝ) ^ (5 / 6 : ℝ) := by
            rw [← Real.rpow_add (by linarith)]
            norm_num
          linarith
        rw [hrw]
        have hle1 : (n : ℝ) ^ (5 / 6 : ℝ) ≤ (n : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
        rw [Real.rpow_one] at hle1
        linarith
      have h30 : (30 : ℝ) ≤ (1 / 2 : ℝ) * (n : ℝ) := by
        have : (60 : ℝ) ≤ n := by exact_mod_cast hn60
        linarith
      calc (n : ℝ) ^ (1 / 3 : ℝ) * (c * (2 : ℝ) ^ M₂ * Real.log n ^ M₂) + 30
          ≤ (n : ℝ) ^ (1 / 3 : ℝ) * ((1 / 2 : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ)) + 30 := by gcongr
        _ ≤ (1 / 2 : ℝ) * (n : ℝ) + (1 / 2 : ℝ) * (n : ℝ) := add_le_add hpow_le h30
        _ = (n : ℝ) := by ring
    have h2_3 : ∀ᶠ n : ℕ in atTop,
        80 * c * (2 : ℝ) ^ M₂ * Real.log n ^ (2 * M₁) * Real.log n ^ M₂ < (n : ℝ) ^ (2 / 3 : ℝ) := by
      have hpow : (fun x : ℝ ↦ Real.log x ^ (2 * M₁ + M₂)) =o[atTop] (fun x : ℝ ↦ x ^ (2 / 3 : ℝ)) := by
        simpa only [Real.rpow_natCast] using
          isLittleO_log_rpow_rpow_atTop (2 * M₁ + M₂ : ℕ) (by norm_num)
      have hε : 0 < (2 * (80 * c * (2 : ℝ) ^ M₂ + 1))⁻¹ := by positivity
      have hb := tendsto_natCast_atTop_atTop.eventually (hpow.bound hε)
      filter_upwards [hb, hn30] with n hn hn_30
      have hlog_pos : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
      have hn_pos : (0 : ℝ) < (n : ℝ) ^ (2 / 3 : ℝ) := by positivity
      rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg hn_pos.le] at hn
      have hmul : Real.log (n : ℝ) ^ (2 * M₁) * Real.log (n : ℝ) ^ M₂ =
          Real.log (n : ℝ) ^ (2 * M₁ + M₂) := (pow_add _ _ _).symm
      rw [mul_assoc (80 * c * (2 : ℝ) ^ M₂), hmul]
      calc 80 * c * (2 : ℝ) ^ M₂ * Real.log (n : ℝ) ^ (2 * M₁ + M₂)
          ≤ (80 * c * (2 : ℝ) ^ M₂ + 1) * Real.log (n : ℝ) ^ (2 * M₁ + M₂) := by gcongr; linarith
        _ ≤ (80 * c * (2 : ℝ) ^ M₂ + 1) * ((2 * (80 * c * (2 : ℝ) ^ M₂ + 1))⁻¹ * (n : ℝ) ^ (2 / 3 : ℝ)) := by
            gcongr
        _ = (1 / 2 : ℝ) * (n : ℝ) ^ (2 / 3 : ℝ) := by field_simp
        _ < (n : ℝ) ^ (2 / 3 : ℝ) := by linarith
    filter_upwards [hn30, hexp3, h1_12, h20, h1_4, h3M2, hM2_bound, h2_3] with
      n h1 h2 h3 h4 h5 h6 h7 h8
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
  filter_upwards [htot_ev, hlog_n_ev] with n htot ⟨hn30, hexp3, hlog_1_12, h20, h1_4, h3M2, hM2_bound, h2_3⟩
  have hn_pos : 0 < n := by omega
  have hlog3 : 3 < Real.log (n : ℝ) := by
    rw [← Real.log_exp 3]
    exact Real.log_lt_log (Real.exp_pos 3) hexp3
  have hloglog1 : 1 < Real.log (Real.log (n : ℝ)) := by
    rw [← Real.log_exp 1]
    exact Real.log_lt_log (Real.exp_pos 1) (lt_trans exp_one_lt_three hlog3)
  have hlog_pos : 0 < Real.log (n : ℝ) := by linarith
  have hloglog_pos : 0 < Real.log (Real.log (n : ℝ)) := by linarith
  have htot_ge1 : (1 : ℝ) ≤ (n : ℝ) / (n.totient : ℝ) := by
    have h1 : (0 : ℝ) < n.totient := by exact_mod_cast Nat.totient_pos.mpr hn_pos
    have h2 : (n.totient : ℝ) ≤ n := by exact_mod_cast Nat.totient_le n
    exact (one_le_div h1).mpr h2
  set psi : ℝ := (n : ℝ) ^ (1 / 3 : ℝ) * ((n : ℝ) / (n.totient : ℝ)) /
    (Real.log n ^ (1 / 3 : ℝ) * Real.log (Real.log n) ^ (2 / 3 : ℝ))
  set r : ℕ := ⌊c * psi⌋₊
  set tau : ℝ := ∏ p ∈ n.primeFactors ∪ (Finset.range r).image (Nat.nth Nat.Prime),
    (1 - (1 : ℝ) / p)
  set Q : ℝ := ((n : ℝ) / (n.totient : ℝ)) * tau
  have hQ_eq : Q = ∏ p ∈ ((Finset.range r).image (Nat.nth Nat.Prime)) \ n.primeFactors,
      (1 - (1 : ℝ) / (p : ℝ)) := by
    have hsub : n.primeFactors ⊆ n.primeFactors ∪ (Finset.range r).image (Nat.nth Nat.Prime) :=
      Finset.subset_union_left
    have htau_split : tau = (∏ p ∈ ((Finset.range r).image (Nat.nth Nat.Prime)) \ n.primeFactors,
        (1 - (1 : ℝ) / (p : ℝ))) * ∏ p ∈ n.primeFactors, (1 - (1 : ℝ) / (p : ℝ)) := by
      dsimp only [tau]
      have hsdiff : (n.primeFactors ∪ (Finset.range r).image (Nat.nth Nat.Prime)) \ n.primeFactors =
          ((Finset.range r).image (Nat.nth Nat.Prime)) \ n.primeFactors := by
        ext p
        simp only [Finset.mem_sdiff, Finset.mem_union]
        tauto
      rw [← hsdiff]
      exact (Finset.prod_sdiff hsub).symm
    have htot_prod : ((n : ℝ) / (n.totient : ℝ)) *
        ∏ p ∈ n.primeFactors, (1 - (1 : ℝ) / (p : ℝ)) = 1 := by
      have hq := congrArg ((↑) : ℚ → ℝ) (Nat.totient_eq_mul_prod_factors n)
      push_cast at hq
      have hq' : (n.totient : ℝ) = (n : ℝ) * ∏ p ∈ n.primeFactors, (1 - (1 : ℝ) / (p : ℝ)) := by
        simpa only [one_div] using hq
      have htot_ne : (n.totient : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr hn_pos).ne'
      calc ((n : ℝ) / (n.totient : ℝ)) * ∏ p ∈ n.primeFactors, (1 - (1 : ℝ) / (p : ℝ))
          = ((n : ℝ) * ∏ p ∈ n.primeFactors, (1 - (1 : ℝ) / (p : ℝ))) / (n.totient : ℝ) := by
            rw [div_mul_eq_mul_div]
        _ = (n.totient : ℝ) / (n.totient : ℝ) := by rw [← hq']
        _ = 1 := div_self htot_ne
    dsimp only [Q]
    rw [htau_split]
    calc ((n : ℝ) / (n.totient : ℝ)) *
          ((∏ p ∈ ((Finset.range r).image (Nat.nth Nat.Prime)) \ n.primeFactors,
            (1 - (1 : ℝ) / (p : ℝ))) * ∏ p ∈ n.primeFactors, (1 - (1 : ℝ) / (p : ℝ)))
        = (∏ p ∈ ((Finset.range r).image (Nat.nth Nat.Prime)) \ n.primeFactors,
            (1 - (1 : ℝ) / (p : ℝ))) *
          (((n : ℝ) / (n.totient : ℝ)) * ∏ p ∈ n.primeFactors, (1 - (1 : ℝ) / (p : ℝ))) := by ring
      _ = ∏ p ∈ ((Finset.range r).image (Nat.nth Nat.Prime)) \ n.primeFactors,
            (1 - (1 : ℝ) / (p : ℝ)) := by rw [htot_prod, mul_one]
  have hQ_pos : 0 < Q := by
    rw [hQ_eq]
    refine Finset.prod_pos fun p hp ↦ ?_
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_sdiff.mp hp).1
    have hp2 : (2 : ℝ) ≤ Nat.nth Nat.Prime i := by
      exact_mod_cast (Nat.add_two_le_nth_prime i).trans' (by omega)
    rw [sub_pos, div_lt_one (by linarith)]
    linarith
  have hQ_le_one : Q ≤ 1 := by
    rw [hQ_eq]
    refine Finset.prod_le_one (fun p hp ↦ ?_) (fun p hp ↦ ?_)
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_sdiff.mp hp).1
      have hp2 : (2 : ℝ) ≤ Nat.nth Nat.Prime i := by
        exact_mod_cast (Nat.add_two_le_nth_prime i).trans' (by omega)
      rw [sub_nonneg, div_le_one (by linarith)]
      linarith
    · exact sub_le_self 1 (by positivity)
  have hQ_ge_prod : ∏ i ∈ Finset.range r, (1 - (1 : ℝ) / (Nat.nth Nat.Prime i : ℝ)) ≤ Q := by
    let A := (Finset.range r).image (Nat.nth Nat.Prime)
    have hprodA : ∏ i ∈ Finset.range r, (1 - (1 : ℝ) / (Nat.nth Nat.Prime i : ℝ)) =
        ∏ p ∈ A, (1 - (1 : ℝ) / (p : ℝ)) := by
      dsimp only [A]
      rw [Finset.prod_image]
      intro i _ j _ hij
      exact (Nat.nth_strictMono Nat.infinite_setOfPred_prime).injective hij
    rw [hprodA, hQ_eq]
    have hsub : A \ n.primeFactors ⊆ A := Finset.sdiff_subset
    rw [← Finset.prod_sdiff hsub]
    have hrem_le : ∏ p ∈ A \ (A \ n.primeFactors), (1 - (1 : ℝ) / (p : ℝ)) ≤ 1 := by
      refine Finset.prod_le_one (fun p hp ↦ ?_) (fun p _ ↦ sub_le_self 1 (by positivity))
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_sdiff.mp hp).1
      have hp2 : (2 : ℝ) ≤ Nat.nth Nat.Prime i := by
        exact_mod_cast (Nat.add_two_le_nth_prime i).trans' (by omega)
      rw [sub_nonneg, div_le_one (by linarith)]
      linarith
    calc (∏ p ∈ A \ (A \ n.primeFactors), (1 - (1 : ℝ) / (p : ℝ))) *
          ∏ p ∈ A \ n.primeFactors, (1 - (1 : ℝ) / (p : ℝ))
        ≤ 1 * ∏ p ∈ A \ n.primeFactors, (1 - (1 : ℝ) / (p : ℝ)) :=
          mul_le_mul_of_nonneg_right hrem_le (hQ_eq ▸ hQ_pos.le)
      _ = _ := one_mul _
  have hpsi_lb : (n : ℝ) ^ (1 / 4 : ℝ) ≤ psi := by
    have hloglog_le : Real.log (Real.log (n : ℝ)) ≤ Real.log (n : ℝ) :=
      Real.log_le_self hlog_pos.le
    have hden_le : Real.log n ^ (1 / 3 : ℝ) * Real.log (Real.log n) ^ (2 / 3 : ℝ) ≤ Real.log n := by
      calc Real.log n ^ (1 / 3 : ℝ) * Real.log (Real.log n) ^ (2 / 3 : ℝ)
          ≤ Real.log n ^ (1 / 3 : ℝ) * Real.log n ^ (2 / 3 : ℝ) := by
            gcongr
        _ = Real.log n ^ ((1 / 3 : ℝ) + (2 / 3 : ℝ)) := (Real.rpow_add hlog_pos _ _).symm
        _ = Real.log n := by norm_num
    have h1 : (n : ℝ) ^ (1 / 3 : ℝ) / Real.log n ≤ psi := by
      calc (n : ℝ) ^ (1 / 3 : ℝ) / Real.log n
          ≤ (n : ℝ) ^ (1 / 3 : ℝ) /
              (Real.log n ^ (1 / 3 : ℝ) * Real.log (Real.log n) ^ (2 / 3 : ℝ)) := by
            exact div_le_div_of_nonneg_left (by positivity) (by positivity) hden_le
        _ ≤ (n : ℝ) ^ (1 / 3 : ℝ) * ((n : ℝ) / (n.totient : ℝ)) /
              (Real.log n ^ (1 / 3 : ℝ) * Real.log (Real.log n) ^ (2 / 3 : ℝ)) := by
            gcongr
            exact le_mul_of_one_le_right (by positivity) htot_ge1
    have h2 : (n : ℝ) ^ (1 / 4 : ℝ) ≤ (n : ℝ) ^ (1 / 3 : ℝ) / Real.log n := by
      rw [le_div_iff₀ hlog_pos]
      calc (n : ℝ) ^ (1 / 4 : ℝ) * Real.log n
          ≤ (n : ℝ) ^ (1 / 4 : ℝ) * (n : ℝ) ^ (1 / 12 : ℝ) := by gcongr
        _ = (n : ℝ) ^ ((1 / 4 : ℝ) + (1 / 12 : ℝ)) :=
          (Real.rpow_add (by exact_mod_cast hn_pos) _ _).symm
        _ = (n : ℝ) ^ (1 / 3 : ℝ) := by norm_num
    exact h2.trans h1
  have hr_lb : c * (n : ℝ) ^ (1 / 4 : ℝ) / 2 ≤ (r : ℝ) := by
    have hfloor : c * psi - 1 < (r : ℝ) := Nat.sub_one_lt_floor _
    have h1 : c * (n : ℝ) ^ (1 / 4 : ℝ) - 1 < (r : ℝ) := by
      have : c * (n : ℝ) ^ (1 / 4 : ℝ) ≤ c * psi := mul_le_mul_of_nonneg_left hpsi_lb hc.le
      linarith
    linarith
  have hr_pos : (1 : ℝ) ≤ (r : ℝ) := by linarith
  have hr_ub : (r : ℝ) ≤ c * (2 : ℝ) ^ M₂ * (n : ℝ) ^ (1 / 3 : ℝ) *
      Real.log (Real.log n) ^ M₂ / Real.log n ^ (1 / 3 : ℝ) := by
    have hfloor : (r : ℝ) ≤ c * psi := Nat.floor_le (by positivity)
    have hloglog23 : 1 ≤ Real.log (Real.log n) ^ (2 / 3 : ℝ) :=
      Real.one_le_rpow hloglog1.le (by norm_num)
    have hden_ge : Real.log n ^ (1 / 3 : ℝ) ≤
        Real.log n ^ (1 / 3 : ℝ) * Real.log (Real.log n) ^ (2 / 3 : ℝ) :=
      le_mul_of_one_le_right (by positivity) hloglog23
    have hpsi_ub : psi ≤ (n : ℝ) ^ (1 / 3 : ℝ) * ((2 : ℝ) ^ M₂ * Real.log (Real.log n) ^ M₂) /
        Real.log n ^ (1 / 3 : ℝ) := by
      calc psi = (n : ℝ) ^ (1 / 3 : ℝ) * ((n : ℝ) / (n.totient : ℝ)) /
            (Real.log n ^ (1 / 3 : ℝ) * Real.log (Real.log n) ^ (2 / 3 : ℝ)) := rfl
        _ ≤ (n : ℝ) ^ (1 / 3 : ℝ) * ((2 : ℝ) ^ M₂ * Real.log (Real.log n) ^ M₂) /
            (Real.log n ^ (1 / 3 : ℝ) * Real.log (Real.log n) ^ (2 / 3 : ℝ)) := by
          gcongr
        _ ≤ (n : ℝ) ^ (1 / 3 : ℝ) * ((2 : ℝ) ^ M₂ * Real.log (Real.log n) ^ M₂) /
            Real.log n ^ (1 / 3 : ℝ) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hden_ge
    calc (r : ℝ) ≤ c * psi := hfloor
      _ ≤ c * ((n : ℝ) ^ (1 / 3 : ℝ) * ((2 : ℝ) ^ M₂ * Real.log (Real.log n) ^ M₂) /
            Real.log n ^ (1 / 3 : ℝ)) := by gcongr
      _ = _ := by ring
  have hr_cubed : (r : ℝ) ^ 3 ≤ 15 * (n : ℝ) := by
    have hpow := pow_le_pow_left₀ (by positivity) hr_ub 3
    have hsimp : (c * (2 : ℝ) ^ M₂ * (n : ℝ) ^ (1 / 3 : ℝ) *
        Real.log (Real.log n) ^ M₂ / Real.log n ^ (1 / 3 : ℝ)) ^ 3 =
        (c * (2 : ℝ) ^ M₂) ^ 3 * (n : ℝ) * Real.log (Real.log n) ^ (3 * M₂) / Real.log n := by
      have hn3 : ((n : ℝ) ^ (1 / 3 : ℝ)) ^ 3 = (n : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        norm_num
      have hl3 : (Real.log n ^ (1 / 3 : ℝ)) ^ 3 = Real.log n := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hlog_pos.le]
        norm_num
      rw [div_pow, mul_pow, mul_pow, mul_pow, hn3, hl3, ← pow_mul, mul_comm M₂ 3]
      ring
    rw [hsimp] at hpow
    refine hpow.trans ?_
    rw [div_le_iff₀ hlog_pos]
    calc (c * (2 : ℝ) ^ M₂) ^ 3 * (n : ℝ) * Real.log (Real.log n) ^ (3 * M₂)
        = (n : ℝ) * ((c * (2 : ℝ) ^ M₂) ^ 3 * Real.log (Real.log n) ^ (3 * M₂)) := by ring
      _ ≤ (n : ℝ) * (15 * Real.log n) := by gcongr
      _ = 15 * (n : ℝ) * Real.log n := by ring
  have hr_ub2 : (r : ℝ) ≤ c * (2 : ℝ) ^ M₂ * (n : ℝ) ^ (1 / 3 : ℝ) * Real.log n ^ M₂ := by
    have hlog13 : 1 ≤ Real.log n ^ (1 / 3 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
    have hloglog_le : Real.log (Real.log n) ≤ Real.log n := Real.log_le_self hlog_pos.le
    calc (r : ℝ) ≤ c * (2 : ℝ) ^ M₂ * (n : ℝ) ^ (1 / 3 : ℝ) *
          Real.log (Real.log n) ^ M₂ / Real.log n ^ (1 / 3 : ℝ) := hr_ub
      _ ≤ c * (2 : ℝ) ^ M₂ * (n : ℝ) ^ (1 / 3 : ℝ) * Real.log (Real.log n) ^ M₂ / 1 :=
          div_le_div_of_nonneg_left (by positivity) zero_lt_one hlog13
      _ = c * (2 : ℝ) ^ M₂ * (n : ℝ) ^ (1 / 3 : ℝ) * Real.log (Real.log n) ^ M₂ := div_one _
      _ ≤ c * (2 : ℝ) ^ M₂ * (n : ℝ) ^ (1 / 3 : ℝ) * Real.log n ^ M₂ := by gcongr
  have hQ_lb : (Real.log n ^ M₁)⁻¹ ≤ Q := by
    have hr30_le : (r : ℝ) + 30 ≤ (n : ℝ) := by
      calc (r : ℝ) + 30 ≤ c * (2 : ℝ) ^ M₂ * (n : ℝ) ^ (1 / 3 : ℝ) * Real.log n ^ M₂ + 30 := by linarith
        _ = (n : ℝ) ^ (1 / 3 : ℝ) * (c * (2 : ℝ) ^ M₂ * Real.log n ^ M₂) + 30 := by ring
        _ ≤ (n : ℝ) := hM2_bound
    have hlog_le : Real.log ((r : ℝ) + 30) ≤ Real.log (n : ℝ) :=
      Real.log_le_log (by positivity) hr30_le
    have hpow_le : Real.log ((r : ℝ) + 30) ^ M₁ ≤ Real.log (n : ℝ) ^ M₁ :=
      pow_le_pow_left₀ (Real.log_nonneg (by linarith)) hlog_le M₁
    have hinv_le : (Real.log (n : ℝ) ^ M₁)⁻¹ ≤ (Real.log ((r : ℝ) + 30) ^ M₁)⁻¹ :=
      inv_anti₀ (pow_pos (Real.log_pos (by linarith [show (0 : ℝ) ≤ r by positivity])) M₁) hpow_le
    exact hinv_le.trans ((hprod r).1.trans hQ_ge_prod)
  set T : ℝ := 20 * (r : ℝ) * (n : ℝ) / Q
  have hT_ge : 20 * (n : ℝ) ≤ T := by
    calc 20 * (n : ℝ) = 20 * 1 * (n : ℝ) / 1 := by ring
      _ ≤ 20 * (r : ℝ) * (n : ℝ) / Q := by gcongr
  have hT_100 : 100 ≤ T := by
    have : (30 : ℝ) ≤ n := by exact_mod_cast hn30
    linarith
  set y : ℕ := ⌊Real.sqrt T⌋₊
  have hy_ub : (y : ℝ) ≤ Real.sqrt T := Nat.floor_le (Real.sqrt_nonneg T)
  have hy_lb : Real.sqrt (3 / 4 * T) ≤ (y : ℝ) := by
    have hfl : Real.sqrt T - 1 < (y : ℝ) := Nat.sub_one_lt_floor _
    have h1 : 1 ≤ (1 - Real.sqrt (3 / 4)) * Real.sqrt T := by
      have hsq : Real.sqrt (3 / 4 : ℝ) < 9 / 10 := by
        rw [Real.sqrt_lt' (by norm_num)]
        norm_num
      have hsqrt10 : 10 ≤ Real.sqrt T := Real.le_sqrt_of_sq_le (by linarith)
      nlinarith
    have h2 : Real.sqrt (3 / 4 * T) = Real.sqrt (3 / 4) * Real.sqrt T :=
      Real.sqrt_mul (by norm_num) T
    linarith
  have hy_sq_ub : (y : ℝ) ^ 2 ≤ T := by
    calc (y : ℝ) ^ 2 ≤ Real.sqrt T ^ 2 := pow_le_pow_left₀ (by positivity) hy_ub 2
      _ = T := Real.sq_sqrt (by linarith)
  have hy_sq_lb : 15 * (r : ℝ) * (n : ℝ) / Q ≤ (y : ℝ) ^ 2 := by
    have hpow := pow_le_pow_left₀ (Real.sqrt_nonneg _) hy_lb 2
    rw [Real.sq_sqrt (by linarith)] at hpow
    calc 15 * (r : ℝ) * (n : ℝ) / Q = 3 / 4 * T := by simp only [T]; ring
      _ ≤ (y : ℝ) ^ 2 := hpow
  refine ⟨y, ?_, ?_, ?_, ?_, ?_⟩
  · -- 2 * y < n
    have h4y2 : (2 * (y : ℝ)) ^ 2 < (n : ℝ) ^ 2 := by
      have h1 : (2 * (y : ℝ)) ^ 2 ≤ 4 * T := by linarith
      have h2 : 4 * T = 80 * (r : ℝ) * (n : ℝ) / Q := by simp only [T]; ring
      have h3 : 80 * (r : ℝ) * (n : ℝ) / Q ≤
          80 * (c * (2 : ℝ) ^ M₂ * (n : ℝ) ^ (1 / 3 : ℝ) * Real.log n ^ M₂) * (n : ℝ) *
            Real.log n ^ M₁ := by
        rw [div_eq_mul_inv]
        have hQinv : Q⁻¹ ≤ Real.log n ^ M₁ := by
          have := inv_anti₀ (inv_pos.mpr (pow_pos hlog_pos M₁)) hQ_lb
          simpa using this
        exact show 80 * (r : ℝ) * (n : ℝ) * Q⁻¹ ≤
            80 * (c * (2 : ℝ) ^ M₂ * (n : ℝ) ^ (1 / 3 : ℝ) * Real.log n ^ M₂) * (n : ℝ) *
              Real.log n ^ M₁ by gcongr
      have hlog_le_M : Real.log n ^ M₁ ≤ Real.log n ^ (2 * M₁) :=
        pow_le_pow_right₀ (by linarith) (by omega)
      have h4 : 80 * (c * (2 : ℝ) ^ M₂ * (n : ℝ) ^ (1 / 3 : ℝ) * Real.log n ^ M₂) * (n : ℝ) *
            Real.log n ^ M₁ ≤
          (80 * c * (2 : ℝ) ^ M₂ * Real.log n ^ (2 * M₁) * Real.log n ^ M₂) *
            (n : ℝ) ^ (4 / 3 : ℝ) := by
        have hn_pow : (n : ℝ) ^ (1 / 3 : ℝ) * (n : ℝ) = (n : ℝ) ^ (4 / 3 : ℝ) := by
          nth_rw 2 [← Real.rpow_one (n : ℝ)]
          rw [← Real.rpow_add (by exact_mod_cast hn_pos)]
          norm_num
        calc 80 * (c * (2 : ℝ) ^ M₂ * (n : ℝ) ^ (1 / 3 : ℝ) * Real.log n ^ M₂) * (n : ℝ) *
              Real.log n ^ M₁
            ≤ 80 * (c * (2 : ℝ) ^ M₂ * (n : ℝ) ^ (1 / 3 : ℝ) * Real.log n ^ M₂) * (n : ℝ) *
              Real.log n ^ (2 * M₁) := by gcongr
          _ = (80 * c * (2 : ℝ) ^ M₂ * Real.log n ^ (2 * M₁) * Real.log n ^ M₂) *
              ((n : ℝ) ^ (1 / 3 : ℝ) * (n : ℝ)) := by ring
          _ = _ := by rw [hn_pow]
      have h5 : (80 * c * (2 : ℝ) ^ M₂ * Real.log n ^ (2 * M₁) * Real.log n ^ M₂) *
            (n : ℝ) ^ (4 / 3 : ℝ) < (n : ℝ) ^ (2 / 3 : ℝ) * (n : ℝ) ^ (4 / 3 : ℝ) :=
        mul_lt_mul_of_pos_right h2_3 (by positivity)
      have h6 : (n : ℝ) ^ (2 / 3 : ℝ) * (n : ℝ) ^ (4 / 3 : ℝ) = (n : ℝ) ^ 2 := by
        have hsum : (2 / 3 : ℝ) + 4 / 3 = ((2 : ℕ) : ℝ) := by norm_num
        rw [← Real.rpow_add (by exact_mod_cast hn_pos), hsum, Real.rpow_natCast]
      linarith
    have hlt_real : (2 * (y : ℝ)) < (n : ℝ) := by
      nlinarith only [h4y2, show (0 : ℝ) ≤ 2 * (y : ℝ) by positivity, show (0 : ℝ) ≤ (n : ℝ) by positivity]
    exact_mod_cast hlt_real
  · -- r ^ 2 ≤ y
    have h4y : (r : ℝ) ^ 4 ≤ (y : ℝ) ^ 2 := by
      calc (r : ℝ) ^ 4 = (r : ℝ) * (r : ℝ) ^ 3 := by ring
        _ ≤ (r : ℝ) * (15 * (n : ℝ)) := mul_le_mul_of_nonneg_left hr_cubed (by positivity)
        _ = 15 * (r : ℝ) * (n : ℝ) / 1 := by ring
        _ ≤ 15 * (r : ℝ) * (n : ℝ) / Q :=
          div_le_div_of_nonneg_left (by positivity) hQ_pos hQ_le_one
        _ ≤ (y : ℝ) ^ 2 := hy_sq_lb
    have hr2y : ((r ^ 2 : ℕ) : ℝ) ≤ (y : ℝ) := by
      push_cast
      nlinarith only [h4y, show ((r : ℝ) ^ 2) ^ 2 = (r : ℝ) ^ 4 by ring,
        show (0 : ℝ) ≤ (r : ℝ) ^ 2 by positivity, show (0 : ℝ) ≤ (y : ℝ) by positivity]
    exact Nat.cast_le.mp hr2y
  · -- n ^ (3 / 5) ≤ y
    have h15rn : (n : ℝ) ^ (6 / 5 : ℝ) ≤ 15 * (r : ℝ) * (n : ℝ) := by
      have hn15 : (n : ℝ) ^ (1 / 5 : ℝ) ≤ 15 * (r : ℝ) := by
        calc (n : ℝ) ^ (1 / 5 : ℝ)
            = 15 * ((15 : ℝ)⁻¹ * (n : ℝ) ^ (1 / 5 : ℝ)) := by ring
          _ ≤ 15 * ((c * (n : ℝ) ^ (1 / 20 : ℝ) / 2) * (n : ℝ) ^ (1 / 5 : ℝ)) := by gcongr
          _ = 15 * (c * ((n : ℝ) ^ (1 / 20 : ℝ) * (n : ℝ) ^ (1 / 5 : ℝ)) / 2) := by ring
          _ = 15 * (c * (n : ℝ) ^ (1 / 4 : ℝ) / 2) := by
              rw [← Real.rpow_add (by exact_mod_cast hn_pos)]
              norm_num
          _ ≤ 15 * (r : ℝ) := by gcongr
      calc (n : ℝ) ^ (6 / 5 : ℝ) = (n : ℝ) ^ ((1 / 5 : ℝ) + 1) := by norm_num
        _ = (n : ℝ) ^ (1 / 5 : ℝ) * (n : ℝ) := by rw [Real.rpow_add (by exact_mod_cast hn_pos), Real.rpow_one]
        _ ≤ 15 * (r : ℝ) * (n : ℝ) := mul_le_mul_of_nonneg_right hn15 (by positivity)
    have hsq : ((n : ℝ) ^ (3 / 5 : ℝ)) ^ 2 ≤ (y : ℝ) ^ 2 := by
      calc ((n : ℝ) ^ (3 / 5 : ℝ)) ^ 2 = (n : ℝ) ^ (6 / 5 : ℝ) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
            norm_num
        _ ≤ 15 * (r : ℝ) * (n : ℝ) := h15rn
        _ = 15 * (r : ℝ) * (n : ℝ) / 1 := by ring
        _ ≤ 15 * (r : ℝ) * (n : ℝ) / Q :=
          div_le_div_of_nonneg_left (by positivity) hQ_pos hQ_le_one
        _ ≤ (y : ℝ) ^ 2 := hy_sq_lb
    nlinarith only [hsq, show (0 : ℝ) ≤ (n : ℝ) ^ (3 / 5 : ℝ) by positivity, show (0 : ℝ) ≤ (y : ℝ) by positivity]
  · -- y^2 * (n / n.totient) * tau / (25 * r) ≤ n
    have hgoal : (y : ℝ) ^ 2 * Q / (25 * (r : ℝ)) ≤ (n : ℝ) := by
      rw [div_le_iff₀ (by linarith only [hr_pos])]
      have h1 : (y : ℝ) ^ 2 * Q ≤ T * Q := mul_le_mul_of_nonneg_right hy_sq_ub hQ_pos.le
      have h2 : T * Q = 20 * (r : ℝ) * (n : ℝ) := by
        dsimp only [T]
        exact div_mul_cancel₀ _ hQ_pos.ne'
      have h3 : 20 * (r : ℝ) * (n : ℝ) ≤ (n : ℝ) * (25 * (r : ℝ)) := by
        nlinarith only [show (0 : ℝ) ≤ (r : ℝ) by linarith only [hr_pos], show (0 : ℝ) ≤ (n : ℝ) by positivity]
      linarith only [h1, h2, h3]
    have hgoal' : (y : ℝ) ^ 2 * ((n : ℝ) / (n.totient : ℝ)) * tau / (25 * (r : ℝ)) ≤ (n : ℝ) := by
      dsimp only [Q] at hgoal
      rwa [← mul_assoc ((y : ℝ) ^ 2)] at hgoal
    exact hgoal'
  · -- n ≤ y^2 * (n / n.totient) * tau / (15 * r)
    have hgoal : (n : ℝ) ≤ (y : ℝ) ^ 2 * Q / (15 * (r : ℝ)) := by
      rw [le_div_iff₀ (by linarith only [hr_pos])]
      have h1 : (n : ℝ) * (15 * (r : ℝ)) = (15 * (r : ℝ) * (n : ℝ) / Q) * Q := by
        rw [div_mul_cancel₀ _ hQ_pos.ne']
        ring
      rw [h1]
      exact mul_le_mul_of_nonneg_right hy_sq_lb hQ_pos.le
    have hgoal' : (n : ℝ) ≤ (y : ℝ) ^ 2 * ((n : ℝ) / (n.totient : ℝ)) * tau / (15 * (r : ℝ)) := by
      dsimp only [Q] at hgoal
      rwa [← mul_assoc ((y : ℝ) ^ 2)] at hgoal
    exact hgoal'
