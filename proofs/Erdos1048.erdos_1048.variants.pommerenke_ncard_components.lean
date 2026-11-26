import FormalConjectures.ErdosProblems.«1048»

-- Problem: Erdős Problem 1048 — pommerenke ncard components
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/1048.lean:68 (declaration Erdos1048.erdos_1048.variants.pommerenke_ncard_components)
-- Credit: @michielkosters (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

theorem OMA.solution : type_of% @Erdos1048.erdos_1048.variants.pommerenke_ncard_components := by
  intro r hr n hn f hf
  let w0 : ℂ := (r : ℂ) ^ n
  let B : Set ℂ := Metric.closedBall w0 1
  have hhn : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hrn : (1 : ℝ) < r ^ n := one_lt_pow₀ hr (by omega)
  have hB_re : ∀ w ∈ B, (0 : ℝ) < w.re := by
    intro w hw
    have hw' : ‖w - w0‖ ≤ 1 := by
      simpa [Complex.dist_eq] using Metric.mem_closedBall.mp hw
    have hre : (w0 - w).re ≤ 1 := by
      have h1 : (w0 - w).re ≤ ‖w0 - w‖ := Complex.re_le_norm (w0 - w)
      rw [norm_sub_rev] at h1
      linarith
    have hw0_re : w0.re = r ^ n := by
      simp [w0, ← Complex.ofReal_pow]
    simp only [Complex.sub_re, hw0_re] at hre
    linarith
  have hB_slit : B ⊆ Complex.slitPlane := fun w hw => Or.inl (hB_re w hw)
  have hB_ne : ∀ w ∈ B, w ≠ 0 := fun w hw h => by
    have := hB_re w hw
    simp [h] at this
  have hmem_level : ∀ z : ℂ, z ∈ Erdos1043.levelSet f ↔ z ^ n ∈ B := by
    intro z
    rw [hf]
    simp only [Erdos1043.levelSet, Set.mem_ofPred_eq, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_C, B, Metric.mem_closedBall, Complex.dist_eq, w0]
  let g : Fin n → ℂ → ℂ := fun k w =>
    Complex.exp (2 * Real.pi * Complex.I * ((k : ℕ) : ℂ) / (n : ℂ)) *
      Complex.exp (Complex.log w / (n : ℂ))
  have hg_pow : ∀ k w, w ∈ B → (g k w) ^ n = w := by
    intro k w hw
    simp only [g, mul_pow, ← Complex.exp_nat_mul]
    have ha : Complex.exp ((n : ℂ) * (2 * Real.pi * Complex.I * ((k : ℕ) : ℂ) / (n : ℂ))) = 1 := by
      have hmul : (n : ℂ) * (2 * Real.pi * Complex.I * ((k : ℕ) : ℂ) / (n : ℂ)) =
          (((k : ℕ) : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
        push_cast
        field_simp [hhn]
      rw [hmul]
      exact Complex.exp_eq_one_iff.mpr ⟨((k : ℕ) : ℤ), rfl⟩
    have hb : Complex.exp ((n : ℂ) * (Complex.log w / (n : ℂ))) = w := by
      have hmul : (n : ℂ) * (Complex.log w / (n : ℂ)) = Complex.log w := by
        field_simp [hhn]
      rw [hmul]
      exact Complex.exp_log (hB_ne w hw)
    rw [ha, hb, one_mul]
  let C : Fin n → Set ℂ := fun k => g k '' B
  have hg_cont : ∀ k, ContinuousOn (g k) B := by
    intro k
    refine ContinuousOn.mul continuousOn_const ?_
    refine ContinuousOn.cexp ?_
    exact (continuousOn_id.clog fun w hw => hB_slit hw).div_const _
  have hC_conn : ∀ k, IsConnected (C k) := by
    intro k
    have hB_conn : IsConnected B :=
      ⟨⟨w0, Metric.mem_closedBall_self zero_le_one⟩, (convex_closedBall w0 1).isPreconnected⟩
    exact hB_conn.image (g k) (hg_cont k)
  have hC_closed : ∀ k, IsClosed (C k) :=
    fun k => ((isCompact_closedBall w0 1).image_of_continuousOn (hg_cont k)).isClosed
  have hC_disj : ∀ j k : Fin n, j ≠ k → Disjoint (C j) (C k) := by
    intro j k hjk
    rw [Set.disjoint_left]
    intro z hzj hzk
    rcases hzj with ⟨w1, hw1, rfl⟩
    rcases hzk with ⟨w2, hw2, hz2⟩
    have hw12 : w1 = w2 := by
      have h1 := hg_pow j w1 hw1
      have h2 := hg_pow k w2 hw2
      rw [← hz2] at h1
      exact h1.symm.trans h2
    subst hw12
    have hce : Complex.exp (2 * Real.pi * Complex.I * ((j : ℕ) : ℂ) / (n : ℂ)) =
        Complex.exp (2 * Real.pi * Complex.I * ((k : ℕ) : ℂ) / (n : ℂ)) :=
      mul_right_cancel₀ (Complex.exp_ne_zero _) hz2.symm
    have h1 : Complex.exp (2 * Real.pi * Complex.I * (((j : ℕ) : ℂ) - ((k : ℕ) : ℂ)) / (n : ℂ)) = 1 := by
      have hsub : 2 * Real.pi * Complex.I * (((j : ℕ) : ℂ) - ((k : ℕ) : ℂ)) / (n : ℂ) =
          2 * Real.pi * Complex.I * ((j : ℕ) : ℂ) / (n : ℂ) -
            2 * Real.pi * Complex.I * ((k : ℕ) : ℂ) / (n : ℂ) := by
        ring
      rw [hsub, Complex.exp_sub, hce, div_self (Complex.exp_ne_zero _)]
    rcases Complex.exp_eq_one_iff.mp h1 with ⟨m, hm⟩
    have hm' : ((j : ℕ) : ℂ) - ((k : ℕ) : ℂ) = (m : ℂ) * (n : ℂ) := by
      have hmul : (2 * Real.pi * Complex.I) * (((j : ℕ) : ℂ) - ((k : ℕ) : ℂ)) =
          (2 * Real.pi * Complex.I) * ((m : ℂ) * (n : ℂ)) := by
        calc (2 * Real.pi * Complex.I) * (((j : ℕ) : ℂ) - ((k : ℕ) : ℂ))
            = (2 * Real.pi * Complex.I * (((j : ℕ) : ℂ) - ((k : ℕ) : ℂ)) / (n : ℂ)) * (n : ℂ) := by
                field_simp [hhn]
          _ = ((m : ℂ) * (2 * Real.pi * Complex.I)) * (n : ℂ) := by rw [hm]
          _ = (2 * Real.pi * Complex.I) * ((m : ℂ) * (n : ℂ)) := by ring
      exact mul_left_cancel₀ hpi hmul
    have hm_int : ((j : ℕ) : ℤ) - ((k : ℕ) : ℤ) = m * (n : ℤ) := by exact_mod_cast hm'
    have hm0 : m = 0 := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have : m ≤ -1 := by omega
        nlinarith [j.isLt, k.isLt]
      · have : 1 ≤ m := by omega
        nlinarith [j.isLt, k.isLt]
    rw [hm0, zero_mul] at hm_int
    apply hjk
    ext
    omega
  have h_union : Erdos1043.levelSet f = ⋃ k : Fin n, C k := by
    ext z
    rw [Set.mem_iUnion, hmem_level]
    constructor
    · intro hz
      let w := z ^ n
      have hwB : w ∈ B := hz
      let u := z / Complex.exp (Complex.log w / (n : ℂ))
      have hu_pow : u ^ n = 1 := by
        simp only [u, div_pow, ← Complex.exp_nat_mul]
        have hmul : (n : ℂ) * (Complex.log w / (n : ℂ)) = Complex.log w := by field_simp [hhn]
        rw [hmul, Complex.exp_log (hB_ne w hwB)]
        exact div_self (hB_ne w hwB)
      have hu_ne : u ≠ 0 := by
        intro h0
        rw [h0, zero_pow (by omega)] at hu_pow
        exact zero_ne_one hu_pow
      have hu_exp : Complex.exp ((n : ℂ) * Complex.log u) = 1 := by
        rw [Complex.exp_nat_mul, Complex.exp_log hu_ne, hu_pow]
      rcases Complex.exp_eq_one_iff.mp hu_exp with ⟨m, hm⟩
      let q : ℤ := m / (n : ℤ)
      let rem : ℤ := m % (n : ℤ)
      have hrem_nonneg : 0 ≤ rem := Int.emod_nonneg m (by omega)
      have hrem_lt : rem < (n : ℤ) := Int.emod_lt_of_pos m (by omega)
      let k : Fin n := ⟨rem.toNat, by omega⟩
      have hk_eq : ((k : ℕ) : ℤ) = rem := Int.toNat_of_nonneg hrem_nonneg
      have hm_eq : m = ((k : ℕ) : ℤ) + (n : ℤ) * q := by
        rw [hk_eq]
        exact (Int.emod_add_mul_ediv m (n : ℤ)).symm
      have hlog_u : Complex.log u =
          2 * Real.pi * Complex.I * ((k : ℕ) : ℂ) / (n : ℂ) + (q : ℂ) * (2 * Real.pi * Complex.I) := by
        have hm_c : (m : ℂ) = ((k : ℕ) : ℂ) + (n : ℂ) * (q : ℂ) := by exact_mod_cast hm_eq
        calc Complex.log u
            = ((n : ℂ) * Complex.log u) / (n : ℂ) := by field_simp [hhn]
          _ = ((m : ℂ) * (2 * Real.pi * Complex.I)) / (n : ℂ) := by rw [hm]
          _ = ((((k : ℕ) : ℂ) + (n : ℂ) * (q : ℂ)) * (2 * Real.pi * Complex.I)) / (n : ℂ) := by
                rw [hm_c]
          _ = 2 * Real.pi * Complex.I * ((k : ℕ) : ℂ) / (n : ℂ) + (q : ℂ) * (2 * Real.pi * Complex.I) := by
                field_simp [hhn]
      have hu_eq : u = Complex.exp (2 * Real.pi * Complex.I * ((k : ℕ) : ℂ) / (n : ℂ)) := by
        rw [← Complex.exp_log hu_ne, hlog_u, Complex.exp_add]
        have hq1 : Complex.exp ((q : ℂ) * (2 * Real.pi * Complex.I)) = 1 :=
          Complex.exp_eq_one_iff.mpr ⟨q, rfl⟩
        rw [hq1, mul_one]
      refine ⟨k, w, hwB, ?_⟩
      dsimp only [g]
      rw [← hu_eq]
      exact div_mul_cancel₀ z (Complex.exp_ne_zero _)
    · rintro ⟨k, w, hw, rfl⟩
      rw [hg_pow k w hw]
      exact hw
  have h_comp : ∀ k : Fin n, ∀ z ∈ C k,
      connectedComponentIn (Erdos1043.levelSet f) z = C k := by
    intro k z hz
    have hsub1 : C k ⊆ connectedComponentIn (Erdos1043.levelSet f) z := by
      refine (hC_conn k).isPreconnected.subset_connectedComponentIn hz ?_
      rw [h_union]
      exact Set.subset_iUnion C k
    have hsub2 : connectedComponentIn (Erdos1043.levelSet f) z ⊆ C k := by
      let V : Set ℂ := ⋃ j ∈ ({j : Fin n | j ≠ k} : Set (Fin n)), C j
      have hV_closed : IsClosed V :=
        Set.Finite.isClosed_biUnion (Set.toFinite _) (fun j _ => hC_closed j)
      have hUV_disj : Disjoint (C k) V := by
        rw [Set.disjoint_iUnion₂_right]
        intro j hj
        exact hC_disj k j hj.symm
      have h_sub_UV : connectedComponentIn (Erdos1043.levelSet f) z ⊆ C k ∪ V := by
        intro x hx
        have hxS : x ∈ Erdos1043.levelSet f :=
          connectedComponentIn_subset _ _ hx
        rw [h_union, Set.mem_iUnion] at hxS
        rcases hxS with ⟨j, hj⟩
        by_cases hjk : j = k
        · subst hjk; exact Or.inl hj
        · exact Or.inr (Set.mem_biUnion hjk hj)
      have hpre : IsPreconnected (connectedComponentIn (Erdos1043.levelSet f) z) :=
        isPreconnected_connectedComponentIn
      intro x hx
      by_contra hxk
      have hxV : x ∈ V := (h_sub_UV hx).resolve_left hxk
      have hz_comp : z ∈ connectedComponentIn (Erdos1043.levelSet f) z :=
        mem_connectedComponentIn (by rw [h_union]; exact Set.mem_iUnion.mpr ⟨k, hz⟩)
      have hinter := isPreconnected_closed_iff.mp hpre (C k) V (hC_closed k) hV_closed h_sub_UV
        ⟨z, hz_comp, hz⟩ ⟨x, hx, hxV⟩
      rcases hinter with ⟨y, _, hyC, hyV⟩
      exact hUV_disj.notMem_of_mem_left hyC hyV
    exact Set.Subset.antisymm hsub2 hsub1
  have h_set_eq : {K : Set ℂ | ∃ z ∈ Erdos1043.levelSet f,
      K = connectedComponentIn (Erdos1043.levelSet f) z} = Set.range C := by
    ext K
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [h_union, Set.mem_iUnion] at hz
      rcases hz with ⟨k, hzk⟩
      exact ⟨k, (h_comp k z hzk).symm⟩
    · rintro ⟨k, rfl⟩
      rcases (hC_conn k).nonempty with ⟨z, hz⟩
      refine ⟨z, ?_, (h_comp k z hz).symm⟩
      rw [h_union]
      exact Set.mem_iUnion.mpr ⟨k, hz⟩
  rw [h_set_eq]
  have h_inj : Function.Injective C := by
    intro j k hjk
    by_contra hne
    rcases (hC_conn j).nonempty with ⟨z, hz⟩
    have hz' : z ∈ C k := hjk ▸ hz
    exact (hC_disj j k hne).notMem_of_mem_left hz hz'
  rw [Set.ncard_range_of_injective h_inj, Nat.card_eq_fintype_card, Fintype.card_fin]
