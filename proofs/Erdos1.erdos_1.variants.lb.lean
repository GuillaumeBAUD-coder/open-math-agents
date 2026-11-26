import FormalConjectures.ErdosProblems.«1»

-- Problem: Erdős Problem 1 — lb
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/1.lean:91 (declaration Erdos1.erdos_1.variants.lb)
-- Credit: @michielkosters (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

lemma oma_variance_identity (A : Finset ℕ) :
    ∑ S ∈ A.powerset, (2 * (∑ a ∈ S, (a : ℝ)) - ∑ a ∈ A, (a : ℝ)) ^ 2 =
      (2 : ℝ) ^ A.card * ∑ a ∈ A, (a : ℝ) ^ 2 := by
  induction A using Finset.induction_on with
  | empty => simp
  | @insert x A hx ih =>
    rw [Finset.powerset_insert]
    have hdisj : Disjoint A.powerset (A.powerset.image (insert x)) := by
      rw [Finset.disjoint_left]
      intro S hS1 hS2
      rw [Finset.mem_powerset] at hS1
      rw [Finset.mem_image] at hS2
      rcases hS2 with ⟨T, _, rfl⟩
      exact hx (hS1 (Finset.mem_insert_self x T))
    rw [Finset.sum_union hdisj]
    have hinj : Set.InjOn (insert x) (A.powerset : Set (Finset ℕ)) := by
      intro S hS T hT hST
      rw [Finset.mem_coe, Finset.mem_powerset] at hS hT
      have hxS : x ∉ S := fun h => hx (hS h)
      have hxT : x ∉ T := fun h => hx (hT h)
      have := congrArg (fun U => Finset.erase U x) hST
      simpa [Finset.erase_insert hxS, Finset.erase_insert hxT] using this
    rw [Finset.sum_image (fun S hS T hT h => hinj hS hT h)]
    have hsumA : ∑ a ∈ insert x A, (a : ℝ) = (x : ℝ) + ∑ a ∈ A, (a : ℝ) :=
      Finset.sum_insert hx
    have hsum1 : ∑ S ∈ A.powerset, (2 * (∑ a ∈ S, (a : ℝ)) - ∑ a ∈ insert x A, (a : ℝ)) ^ 2 =
        ∑ S ∈ A.powerset, ((2 * (∑ a ∈ S, (a : ℝ)) - ∑ a ∈ A, (a : ℝ)) - (x : ℝ)) ^ 2 := by
      refine Finset.sum_congr rfl fun S _ => ?_
      rw [hsumA]
      ring
    have hsum2 : ∑ S ∈ A.powerset, (2 * (∑ a ∈ insert x S, (a : ℝ)) - ∑ a ∈ insert x A, (a : ℝ)) ^ 2 =
        ∑ S ∈ A.powerset, ((2 * (∑ a ∈ S, (a : ℝ)) - ∑ a ∈ A, (a : ℝ)) + (x : ℝ)) ^ 2 := by
      refine Finset.sum_congr rfl fun S hS => ?_
      have hxS : x ∉ S := fun h => hx ((Finset.mem_powerset.mp hS) h)
      rw [Finset.sum_insert hxS, hsumA]
      ring
    rw [hsum1, hsum2, ← Finset.sum_add_distrib]
    have hcombine : ∑ S ∈ A.powerset,
        (((2 * (∑ a ∈ S, (a : ℝ)) - ∑ a ∈ A, (a : ℝ)) - (x : ℝ)) ^ 2 +
         ((2 * (∑ a ∈ S, (a : ℝ)) - ∑ a ∈ A, (a : ℝ)) + (x : ℝ)) ^ 2) =
        ∑ S ∈ A.powerset, (2 * (2 * (∑ a ∈ S, (a : ℝ)) - ∑ a ∈ A, (a : ℝ)) ^ 2 + 2 * (x : ℝ) ^ 2) := by
      refine Finset.sum_congr rfl fun S _ => by ring
    rw [hcombine, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_powerset,
      nsmul_eq_mul, ih, Finset.card_insert_of_notMem hx, Finset.sum_insert hx]
    push_cast
    ring

lemma oma_sum_odd_sq (m : ℕ) :
    ∑ k ∈ Finset.range m, ((2 * k + 1 : ℕ) : ℝ) ^ 2 = (m : ℝ) * (4 * (m : ℝ) ^ 2 - 1) / 3 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

lemma oma_strictMono_diff {m : ℕ} (g : Fin m → ℕ) (hg : StrictMono g) :
    ∀ i j : ℕ, (hij : i ≤ j) → (hj : j < m) → g ⟨i, hij.trans_lt hj⟩ + (j - i) ≤ g ⟨j, hj⟩ := by
  intro i j hij hj
  induction j generalizing i with
  | zero =>
    have : i = 0 := by omega
    subst this
    simp
  | succ j ih =>
    by_cases hij' : i = j + 1
    · subst hij'; simp
    · have hij2 : i ≤ j := by omega
      have hj' : j < m := by omega
      have h1 := ih i hij2 hj'
      have hlt : g ⟨j, hj'⟩ < g ⟨j + 1, hj⟩ := hg (Fin.mk_lt_mk.mpr (Nat.lt_succ_self j))
      omega

theorem OMA.solution : type_of% @Erdos1.erdos_1.variants.lb := by
  refine ⟨fun _ => (0 : ℝ), by simp, ?_⟩
  intro N A ⟨hAsub, hAinj⟩
  simp only [sub_zero]
  set n := A.card
  by_cases hn0 : n = 0
  · simp [hn0]
  by_cases hn1 : n = 1
  · have hne : A.Nonempty := Finset.card_pos.mp (by omega)
    rcases hne with ⟨a, ha⟩
    have haIcc := Finset.mem_Icc.mp (hAsub ha)
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast le_trans haIcc.1 haIcc.2
    rw [hn1]
    norm_num
    linarith
  have hn2 : 2 ≤ n := by omega
  set M : ℝ := ∑ a ∈ A, (a : ℝ)
  have hvar := oma_variance_identity A
  have hupper : ∑ S ∈ A.powerset, (2 * (∑ a ∈ S, (a : ℝ)) - M) ^ 2 ≤
      (2 : ℝ) ^ n * (n : ℝ) * (N : ℝ) ^ 2 := by
    rw [hvar]
    have hsq : ∑ a ∈ A, (a : ℝ) ^ 2 ≤ (n : ℝ) * (N : ℝ) ^ 2 := by
      calc ∑ a ∈ A, (a : ℝ) ^ 2
        _ ≤ ∑ _a ∈ A, (N : ℝ) ^ 2 := by
          refine Finset.sum_le_sum fun a ha => ?_
          have haN : (a : ℝ) ≤ (N : ℝ) := by
            exact_mod_cast (Finset.mem_Icc.mp (hAsub ha)).2
          nlinarith [show (0 : ℝ) ≤ (a : ℝ) from Nat.cast_nonneg a]
        _ = (n : ℝ) * (N : ℝ) ^ 2 := by simp [n]
    have h2pos : (0 : ℝ) ≤ (2 : ℝ) ^ n := by positivity
    nlinarith
  let T : Finset ℕ := A.powerset.image (fun S => S.sum id)
  have hinj_set : Set.InjOn (fun S : Finset ℕ => S.sum id) (A.powerset : Set (Finset ℕ)) := by
    intro S hS T' hT' hST
    have := @hAinj ⟨S, Finset.mem_coe.mp hS⟩ ⟨T', Finset.mem_coe.mp hT'⟩ hST
    exact congrArg Subtype.val this
  have hTcard : T.card = 2 ^ n := by
    rw [Finset.card_image_of_injOn hinj_set, Finset.card_powerset]
  have hsum_eq : ∑ S ∈ A.powerset, (2 * (∑ a ∈ S, (a : ℝ)) - M) ^ 2 =
      ∑ x ∈ T, (2 * (x : ℝ) - M) ^ 2 := by
    dsimp [T]
    rw [Finset.sum_image hinj_set]
    refine Finset.sum_congr rfl fun S _ => ?_
    simp [Nat.cast_sum]
  let e := T.orderIsoOfFin hTcard
  let g : Fin (2 ^ n) → ℕ := fun i => (e i : ℕ)
  have hg : StrictMono g := fun i j hij => e.strictMono hij
  have hsum_fin : ∑ x ∈ T, (2 * (x : ℝ) - M) ^ 2 =
      ∑ i : Fin (2 ^ n), (2 * (g i : ℝ) - M) ^ 2 := by
    rw [← Finset.sum_coe_sort T]
    exact (Fintype.sum_equiv e.toEquiv _ _ (fun _ => rfl)).symm
  set m : ℕ := 2 ^ (n - 1)
  have h2m : 2 * m = 2 ^ n := by
    rw [← pow_succ']
    congr 1
    omega
  have hm_pos : 1 ≤ m := Nat.one_le_pow _ _ (by decide)
  let h_fn : ℕ → ℝ := fun i => if h : i < 2 ^ n then (2 * (g ⟨i, h⟩ : ℝ) - M) ^ 2 else 0
  have hsum_range : ∑ i : Fin (2 ^ n), (2 * (g i : ℝ) - M) ^ 2 = ∑ i ∈ Finset.range (2 * m), h_fn i := by
    rw [h2m, ← Fin.sum_univ_eq_sum_range h_fn]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [h_fn, i.isLt]
  have h_double : 2 * ∑ i ∈ Finset.range (2 * m), h_fn i =
      ∑ i ∈ Finset.range (2 * m), (h_fn i + h_fn (2 * m - 1 - i)) := by
    rw [two_mul, Finset.sum_add_distrib]
    congr 1
    exact (Finset.sum_range_reflect h_fn (2 * m)).symm
  have h_pair_bound : ∑ i ∈ Finset.range m, 2 * ((2 * m - 1 - 2 * i : ℕ) : ℝ) ^ 2 ≤
      ∑ i ∈ Finset.range (2 * m), (h_fn i + h_fn (2 * m - 1 - i)) := by
    have hsub_sum : ∑ i ∈ Finset.range m, (h_fn i + h_fn (2 * m - 1 - i)) ≤
        ∑ i ∈ Finset.range (2 * m), (h_fn i + h_fn (2 * m - 1 - i)) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) ?_
      intro i _ _
      have : ∀ k, 0 ≤ h_fn k := fun k => by
        dsimp [h_fn]
        split_ifs <;> positivity
      exact add_nonneg (this i) (this (2 * m - 1 - i))
    refine le_trans ?_ hsub_sum
    refine Finset.sum_le_sum fun i hi => ?_
    rw [Finset.mem_range] at hi
    have hi1 : i < 2 ^ n := by omega
    have hi2 : 2 * m - 1 - i < 2 ^ n := by omega
    have hle_idx : i ≤ 2 * m - 1 - i := by omega
    have hdiff := oma_strictMono_diff g hg i (2 * m - 1 - i) hle_idx hi2
    have hdiff_r : ((2 * m - 1 - 2 * i : ℕ) : ℝ) ≤ (g ⟨2 * m - 1 - i, hi2⟩ : ℝ) - (g ⟨i, hi1⟩ : ℝ) := by
      have : g ⟨i, hi1⟩ + (2 * m - 1 - 2 * i) ≤ g ⟨2 * m - 1 - i, hi2⟩ := by
        simpa [show 2 * m - 1 - i - i = 2 * m - 1 - 2 * i by omega] using hdiff
      have hcast : (g ⟨i, hi1⟩ : ℝ) + ((2 * m - 1 - 2 * i : ℕ) : ℝ) ≤ (g ⟨2 * m - 1 - i, hi2⟩ : ℝ) := by
        exact_mod_cast this
      linarith
    have hsq_diff : ((2 * m - 1 - 2 * i : ℕ) : ℝ) ^ 2 ≤
        ((g ⟨2 * m - 1 - i, hi2⟩ : ℝ) - (g ⟨i, hi1⟩ : ℝ)) ^ 2 := by
      nlinarith [show (0 : ℝ) ≤ ((2 * m - 1 - 2 * i : ℕ) : ℝ) from Nat.cast_nonneg _]
    have h_alg : 2 * ((g ⟨2 * m - 1 - i, hi2⟩ : ℝ) - (g ⟨i, hi1⟩ : ℝ)) ^ 2 ≤
        (2 * (g ⟨i, hi1⟩ : ℝ) - M) ^ 2 + (2 * (g ⟨2 * m - 1 - i, hi2⟩ : ℝ) - M) ^ 2 := by
      nlinarith [sq_nonneg (2 * (g ⟨i, hi1⟩ : ℝ) + 2 * (g ⟨2 * m - 1 - i, hi2⟩ : ℝ) - 2 * M)]
    simp only [h_fn, dif_pos hi1, dif_pos hi2]
    linarith
  have h_sum_eval : ∑ i ∈ Finset.range m, 2 * ((2 * m - 1 - 2 * i : ℕ) : ℝ) ^ 2 =
      2 * ((m : ℝ) * (4 * (m : ℝ) ^ 2 - 1) / 3) := by
    rw [← Finset.mul_sum]
    congr 1
    have hrefl := Finset.sum_range_reflect (fun k : ℕ => ((2 * k + 1 : ℕ) : ℝ) ^ 2) m
    rw [oma_sum_odd_sq m] at hrefl
    rw [← hrefl]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    congr 2
    omega
  have hm_sq : (m : ℝ) ^ 3 ≤ (m : ℝ) * (4 * (m : ℝ) ^ 2 - 1) / 3 := by
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm_pos
    nlinarith
  have hlower : (m : ℝ) ^ 3 ≤ ∑ S ∈ A.powerset, (2 * (∑ a ∈ S, (a : ℝ)) - M) ^ 2 := by
    rw [hsum_eq, hsum_fin, hsum_range]
    linarith
  have h_m_eq : (2 : ℝ) * (m : ℝ) = (2 : ℝ) ^ n := by exact_mod_cast h2m
  have h_pow_ineq : (2 : ℝ) ^ (2 * n) / 8 ≤ (n : ℝ) * (N : ℝ) ^ 2 := by
    have h2npos : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
    have h2sq : (2 : ℝ) ^ (2 * n) = ((2 : ℝ) ^ n) ^ 2 := by rw [mul_comm, pow_mul]
    have hm3 : (m : ℝ) ^ 3 = (2 : ℝ) ^ n * (2 : ℝ) ^ (2 * n) / 8 := by
      have : (m : ℝ) = (2 : ℝ) ^ n / 2 := by linarith
      rw [this, h2sq]
      ring
    have h1 : (2 : ℝ) ^ n * ((2 : ℝ) ^ (2 * n) / 8) ≤ (2 : ℝ) ^ n * ((n : ℝ) * (N : ℝ) ^ 2) := by
      linarith
    exact le_of_mul_le_mul_left h1 h2npos
  have h_sq_bound : ((1 / 4 : ℝ) * (2 : ℝ) ^ n / Real.sqrt (n : ℝ)) ^ 2 ≤ (N : ℝ) ^ 2 := by
    have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    rw [div_pow, mul_pow, Real.sq_sqrt hn_pos.le, ← pow_mul, mul_comm n 2]
    rw [div_le_iff₀ hn_pos]
    nlinarith [show (0 : ℝ) ≤ (2 : ℝ) ^ (2 * n) by positivity]
  have h_lhs_nonneg : 0 ≤ (1 / 4 : ℝ) * (2 : ℝ) ^ n / Real.sqrt (n : ℝ) := by positivity
  have h_rhs_nonneg : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  exact (sq_le_sq₀ h_lhs_nonneg h_rhs_nonneg).mp h_sq_bound
