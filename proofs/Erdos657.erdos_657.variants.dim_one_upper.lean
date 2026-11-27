import FormalConjectures.ErdosProblems.«657»

-- Problem: Erdős Problem 657 — dim one upper
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/657.lean:107 (declaration Erdos657.erdos_657.variants.dim_one_upper)
-- Credit: @senamakel (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Real Filter

-- Behrend: a 3AP-free subset of range N of size n, with N about n * exp (8 * sqrt (log n)).
theorem OMA.solution : type_of% @Erdos657.erdos_657.variants.dim_one_upper := by
  refine ⟨14, by norm_num, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop (3 ^ 16)] with n hn
  have hn1 : (1 : ℝ) ≤ n := by
    have : 1 ≤ n := le_trans (by norm_num) hn
    exact_mod_cast this
  have hnpos : (0 : ℝ) < n := by linarith
  have hlogn : 16 ≤ log n := by
    have h3 : (1 : ℝ) < log 3 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num)]
      have := Real.exp_one_lt_d9
      linarith
    have : ((3 : ℕ) ^ 16 : ℝ) ≤ n := by exact_mod_cast hn
    have hl : log ((3 : ℝ) ^ 16) ≤ log n :=
      Real.log_le_log (by positivity) (by simpa using this)
    rw [Real.log_pow] at hl
    push_cast at hl
    linarith
  set s := √(log n) with hs
  have hs2 : s ^ 2 = log n := Real.sq_sqrt (by linarith)
  have hs4 : 4 ≤ s := by
    rw [hs, show (4 : ℝ) = √16 by
      rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hlogn
  set N := ⌈(n : ℝ) * exp (8 * s)⌉₊ with hNdef
  have hM1 : (1 : ℝ) ≤ n * exp (8 * s) := by
    have : (1 : ℝ) ≤ exp (8 * s) := Real.one_le_exp (by linarith)
    nlinarith
  have hN1 : (n : ℝ) * exp (8 * s) ≤ N := Nat.le_ceil _
  have hN2 : (N : ℝ) < n * exp (8 * s) + 1 := Nat.ceil_lt_add_one (by linarith)
  have hNle : (N : ℝ) ≤ 2 * (n * exp (8 * s)) := by linarith
  have hNpos : (0 : ℝ) < N := by linarith
  have hlogN : log N ≤ (s + 4) ^ 2 := by
    have h1 : log N ≤ log (2 * (n * exp (8 * s))) := Real.log_le_log hNpos hNle
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_exp] at h1
    have h2 : log 2 < 1 := by
      have := Real.log_two_lt_d9
      linarith
    nlinarith
  have hsqrt : √(log N) ≤ s + 4 := by
    calc √(log N) ≤ √((s + 4) ^ 2) := Real.sqrt_le_sqrt hlogN
      _ = s + 4 := Real.sqrt_sq (by linarith)
  have hroth : (n : ℝ) ≤ rothNumberNat N := by
    have h1 : (n : ℝ) ≤ n * exp (8 * s) * exp (-4 * (s + 4)) := by
      rw [mul_assoc, ← Real.exp_add]
      have : (1 : ℝ) ≤ exp (8 * s + -4 * (s + 4)) := Real.one_le_exp (by linarith)
      nlinarith
    have h2 : (n : ℝ) * exp (8 * s) * exp (-4 * (s + 4)) ≤ N * exp (-4 * √(log N)) := by
      apply mul_le_mul hN1 (Real.exp_le_exp.2 (by linarith)) (by positivity) (by positivity)
    exact h1.trans (h2.trans Behrend.roth_lower_bound)
  obtain ⟨t, htN, htcard, htAP⟩ := rothNumberNat_spec N
  have hnt : n ≤ t.card := by
    rw [htcard]
    exact_mod_cast hroth
  obtain ⟨u, hut, hucard⟩ := Finset.exists_subset_card_eq hnt
  have key : ∀ a ∈ u, ∀ b ∈ u, ∀ c ∈ u, a ≠ c → a ≠ b →
      dist (a : ℝ) (b : ℝ) ≠ dist (b : ℝ) (c : ℝ) := by
    intro a ha b hb c hc hac hab h
    rw [Real.dist_eq, Real.dist_eq] at h
    rcases abs_eq_abs.mp h with h' | h'
    · have h3 : a + c = b + b := by
        have : (a : ℝ) + c = b + b := by linarith
        exact_mod_cast this
      exact hab (htAP (Finset.mem_coe.2 (hut ha)) (Finset.mem_coe.2 (hut hb))
        (Finset.mem_coe.2 (hut hc)) h3)
    · have : (a : ℝ) = c := by linarith
      exact hac (by exact_mod_cast this)
  refine ⟨u.image (Nat.cast : ℕ → ℝ), ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ Nat.cast_injective, hucard]
  · intro x hx y hy z hz hxy hyz hxz hiso
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hx hy hz
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    obtain ⟨c, hc, rfl⟩ := hz
    have hab : a ≠ b := fun e => hxy (by rw [e])
    have hbc : b ≠ c := fun e => hyz (by rw [e])
    have hac : a ≠ c := fun e => hxz (by rw [e])
    rcases hiso with h | h | h
    · exact key a ha b hb c hc hac hab h
    · exact key b hb c hc a ha hab.symm hbc h
    · exact key c hc a ha b hb hbc.symm hac.symm h
  · have hsub : distanceSet (u.image (Nat.cast : ℕ → ℝ)) ⊆
        (Finset.range N).image (Nat.cast : ℕ → ℝ) := by
      intro d hd
      simp only [distanceSet, Finset.mem_image, Finset.mem_offDiag] at hd
      obtain ⟨⟨x, y⟩, ⟨hx, hy, -⟩, rfl⟩ := hd
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨b, hb, rfl⟩ := hy
      have haN : a < N := Finset.mem_range.1 (htN (hut ha))
      have hbN : b < N := Finset.mem_range.1 (htN (hut hb))
      simp only [Finset.mem_image, Finset.mem_range]
      rcases le_total a b with h | h
      · refine ⟨b - a, by omega, ?_⟩
        rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (by simp only [sub_nonneg]; exact_mod_cast h),
          Nat.cast_sub h]
      · refine ⟨a - b, by omega, ?_⟩
        rw [Real.dist_eq, abs_of_nonneg (by simp only [sub_nonneg]; exact_mod_cast h),
          Nat.cast_sub h]
    have hcard : distinctDistances (u.image (Nat.cast : ℕ → ℝ)) ≤ N := by
      unfold distinctDistances
      calc _ ≤ ((Finset.range N).image (Nat.cast : ℕ → ℝ)).card := Finset.card_le_card hsub
        _ ≤ (Finset.range N).card := Finset.card_image_le
        _ = N := Finset.card_range N
    have hcardR : (distinctDistances (u.image (Nat.cast : ℕ → ℝ)) : ℝ) ≤ N := by
      exact_mod_cast hcard
    have hpow : 2 * exp (8 * s) ≤ (2 : ℝ) ^ (14 * √(log n)) := by
      rw [← hs, Real.rpow_def_of_pos (by norm_num)]
      have hl := Real.log_two_gt_d9
      have hl2 : log 2 < 1 := by have := Real.log_two_lt_d9; linarith
      calc 2 * exp (8 * s) = exp (log 2 + 8 * s) := by
            rw [Real.exp_add, Real.exp_log (by norm_num)]
        _ ≤ exp (log 2 * (14 * s)) := Real.exp_le_exp.2 (by nlinarith)
    calc _ ≤ (N : ℝ) := hcardR
      _ ≤ 2 * (n * exp (8 * s)) := hNle
      _ = n * (2 * exp (8 * s)) := by ring
      _ ≤ n * (2 : ℝ) ^ (14 * √(log n)) := mul_le_mul_of_nonneg_left hpow hnpos.le
