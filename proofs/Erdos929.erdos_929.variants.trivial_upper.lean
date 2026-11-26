import FormalConjectures.ErdosProblems.«929»

-- Problem: Erdős Problem 929 — trivial upper
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/929.lean:108 (declaration Erdos929.erdos_929.variants.trivial_upper)
-- Credit: @sho-404 (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Filter Topology in
theorem OMA.periodic_hasPosDensity (T : Set ℕ) (M : ℕ) (hM : 0 < M)
    (hper : ∀ n, n + M ∈ T ↔ n ∈ T) (hne : ∃ n, n ∈ T) : T.HasPosDensity := by
  classical
  set g : ℕ → ℕ := fun b => Nat.count (fun n => n ∈ T) b with hg
  have hstep : ∀ b, g (M + b) = g M + g b := by
    intro b
    induction b with
    | zero => simp [hg]
    | succ b ih =>
      have e : M + (b + 1) = (M + b) + 1 := by ring
      have h2 : (M + b ∈ T) ↔ b ∈ T := by rw [add_comm]; exact hper b
      simp only [hg] at ih ⊢
      rw [e, Nat.count_succ, Nat.count_succ, ih]
      simp only [h2]
      ring
  have hmul : ∀ q r, g (r + q * M) = g r + q * g M := by
    intro q
    induction q with
    | zero => intro r; simp
    | succ q ih =>
      intro r
      have e : r + (q + 1) * M = M + (r + q * M) := by ring
      rw [e, hstep, ih]; ring
  have hmem : ∀ q r, r + q * M ∈ T ↔ r ∈ T := by
    intro q
    induction q with
    | zero => intro r; simp
    | succ q ih =>
      intro r
      rw [← ih r, Nat.succ_mul, ← Nat.add_assoc]
      exact hper _
  have hle : ∀ b, g b ≤ b := fun b => Nat.count_le _
  have hcpos : 0 < g M := by
    obtain ⟨n, hn⟩ := hne
    have h1 : n % M ∈ T := by
      rw [← hmem (n / M) (n % M), Nat.mod_add_div']; exact hn
    have h2 : g (n % M + 1) ≤ g M := Nat.count_monotone _ (Nat.mod_lt _ hM)
    have h3 : g (n % M + 1) = g (n % M) + 1 := by
      simp only [hg]; rw [Nat.count_succ]; simp [h1]
    omega
  have hcard : ∀ b : ℕ, ((T ∩ Set.univ) ∩ Set.Iio b).ncard = g b := by
    intro b
    simp only [hg]
    rw [Nat.count_eq_card_filter_range, ← Set.ncard_coe_finset]
    congr 1
    ext x
    simp [and_comm]
  have hcard2 : ∀ b : ℕ, ((Set.univ : Set ℕ) ∩ Set.Iio b).ncard = b := by
    intro b; simp
  refine ⟨(g M : ℝ) / M, by positivity, ?_⟩
  unfold Set.HasDensity Set.partialDensity
  simp only [hcard, hcard2]
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have key : ∀ b : ℕ, 0 < b → |(g b : ℝ) / b - (g M : ℝ) / M| ≤ M / b := by
    intro b hb
    have hbr : (0 : ℝ) < b := by exact_mod_cast hb
    have e1 := hmul (b / M) (b % M)
    rw [Nat.mod_add_div'] at e1
    have e2 : b = b % M + b / M * M := (Nat.mod_add_div' b M).symm
    have hr : b % M < M := Nat.mod_lt _ hM
    have hgr : g (b % M) ≤ b % M := hle _
    have hgM : g M ≤ M := hle _
    have e1r : (g b : ℝ) = g (b % M) + (b / M : ℕ) * g M := by exact_mod_cast e1
    have e2r : (b : ℝ) = (b % M : ℕ) + (b / M : ℕ) * M := by exact_mod_cast e2
    have hrr : ((b % M : ℕ) : ℝ) ≤ M := by exact_mod_cast hr.le
    have hgrr : (g (b % M) : ℝ) ≤ M := by exact_mod_cast (hgr.trans hr.le)
    have hgMr : (g M : ℝ) ≤ M := by exact_mod_cast hgM
    have h0 : (0:ℝ) ≤ g (b % M) := by positivity
    have h0' : (0:ℝ) ≤ g M := by positivity
    have h0'' : (0:ℝ) ≤ ((b % M : ℕ) : ℝ) := by positivity
    have eq : (g b : ℝ) / b - (g M : ℝ) / M
        = ((g (b % M) : ℝ) * M - g M * (b % M : ℕ)) / (b * M) := by
      field_simp
      rw [e1r]
      linear_combination (-(g M : ℝ)) * e2r
    rw [eq, abs_le]
    have hbM : (0:ℝ) < b * M := by positivity
    constructor
    · rw [le_div_iff₀ hbM]
      have : (M : ℝ) / b * (b * M) = M * M := by field_simp
      nlinarith
    · rw [div_le_iff₀ hbM]
      have : (M : ℝ) / b * (b * M) = M * M := by field_simp
      nlinarith
  have hlim : Tendsto (fun b : ℕ => (M : ℝ) / b) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
  filter_upwards [eventually_gt_atTop 0] with b hb
  simpa using key b hb

theorem OMA.solution : type_of% @Erdos929.erdos_929.variants.trivial_upper := by
  intro k
  apply Erdos929.S_le
  apply OMA.periodic_hasPosDensity _ (k + 1).factorial (Nat.factorial_pos _)
  · intro n
    have hiff : ∀ i p : ℕ, p.Prime ∧ p ≤ k + 1 ∧ p ∣ n + (k + 1).factorial + i ↔
        p.Prime ∧ p ≤ k + 1 ∧ p ∣ n + i := by
      intro i p
      constructor
      · rintro ⟨hp, hle, hd⟩
        refine ⟨hp, hle, ?_⟩
        have hpM : p ∣ (k + 1).factorial := (Nat.Prime.dvd_factorial hp).2 hle
        have e : n + (k + 1).factorial + i = (n + i) + (k + 1).factorial := by ring
        rw [e] at hd
        exact (Nat.dvd_add_left hpM).1 hd
      · rintro ⟨hp, hle, hd⟩
        refine ⟨hp, hle, ?_⟩
        have hpM : p ∣ (k + 1).factorial := (Nat.Prime.dvd_factorial hp).2 hle
        have e : n + (k + 1).factorial + i = (n + i) + (k + 1).factorial := by ring
        rw [e]
        exact (Nat.dvd_add_left hpM).2 hd
    change Erdos929.AllHaveSmallPrimeFactor _ _ _ ↔ Erdos929.AllHaveSmallPrimeFactor _ _ _
    simp only [Erdos929.AllHaveSmallPrimeFactor, hiff]
  · refine ⟨1, ?_⟩
    intro i hi
    rw [Finset.mem_Icc] at hi
    refine ⟨(1 + i).minFac, Nat.minFac_prime (by omega), ?_, Nat.minFac_dvd _⟩
    exact (Nat.minFac_le (by omega)).trans (by omega)
