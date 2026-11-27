import OMAReductions.R_GromovPolynomialGrowth_GromovPolynomialGrowthTheorem_R1

open GromovPolynomialGrowth

/-!
Polynomial growth passes from a finite-index subgroup `H ≤ G` to the ambient group `G`.
Given a finite generating set `S₀` of `H` with polynomial growth and a finite set `T` of left
coset representatives of `H` in `G` containing `1`, the finite set `S = S₀ ∪ T` generates `G`.
Every product `u * t` with `u ∈ S ∪ S⁻¹` and `t ∈ T` decomposes as `t' * h` with `t' ∈ T` and
`h ∈ CayleyBall S₀ K` for a uniform radius `K ≥ 1`. Induction on word length yields
`CayleyBall S n ⊆ {t * h | t ∈ T, h ∈ CayleyBall S₀ (K * n)}`, giving the polynomial bound
`GrowthFunction S n ≤ T.ncard * C * K ^ d * n ^ d` for all `n > 0`.
-/

theorem OMA.solution : OMA.R_GromovPolynomialGrowth_GromovPolynomialGrowthTheorem_R1.H3 := by
  classical
  intro G _ H hfi hH
  haveI : H.FiniteIndex := hfi
  haveI : Finite (G ⧸ H) := Subgroup.finiteIndex_iff_finite_quotient.mp hfi
  obtain ⟨S₀, hS₀_fin, hS₀_gen, C, d, hC_pos, hbound⟩ := hH
  have h_mk_surj : ∀ q : G ⧸ H, ∃ g : G, QuotientGroup.mk (s := H) g = q :=
    QuotientGroup.mk_surjective
  choose rep hrep using h_mk_surj
  let T : Set G := insert 1 (Set.range rep)
  have h1T : (1 : G) ∈ T := Set.mem_insert 1 _
  have hT_fin : T.Finite := (Set.finite_range rep).insert 1
  have h_decomp : ∀ g : G, ∃ t ∈ T, ∃ h : H, g = t * (h : G) := by
    intro g
    let t : G := rep (QuotientGroup.mk (s := H) g)
    have htT : t ∈ T := Set.mem_insert_of_mem 1 ⟨QuotientGroup.mk (s := H) g, rfl⟩
    have hq : QuotientGroup.mk (s := H) t = QuotientGroup.mk (s := H) g :=
      hrep (QuotientGroup.mk (s := H) g)
    have hmem : t⁻¹ * g ∈ H := QuotientGroup.eq.mp hq
    exact ⟨t, htT, ⟨t⁻¹ * g, hmem⟩, by simp⟩
  let S : Set G := ((Subtype.val : H → G) '' S₀) ∪ T
  have hS_fin : S.Finite := (hS₀_fin.image (Subtype.val : H → G)).union hT_fin
  have hS_gen : Subgroup.closure S = ⊤ := by
    rw [eq_top_iff]
    intro g _
    obtain ⟨t, htT, h, rfl⟩ := h_decomp g
    have ht_cl : t ∈ Subgroup.closure S := Subgroup.subset_closure (Or.inr htT)
    have hh_cl : (h : G) ∈ Subgroup.closure S := by
      have hh0 : h ∈ Subgroup.closure S₀ := hS₀_gen ▸ Subgroup.mem_top h
      induction hh0 using Subgroup.closure_induction with
      | mem x hx =>
        exact Subgroup.subset_closure (Or.inl ⟨x, hx, rfl⟩)
      | one =>
        rw [Subgroup.coe_one]
        exact one_mem _
      | mul x y _ _ ihx ihy =>
        rw [Subgroup.coe_mul]
        exact mul_mem ihx ihy
      | inv x _ ihx =>
        rw [Subgroup.coe_inv]
        exact inv_mem ihx
    exact mul_mem ht_cl hh_cl
  let S_sym : Set G := S ∪ (fun x : G => x⁻¹) '' S
  have hS_sym_fin : S_sym.Finite := hS_fin.union (hS_fin.image fun x : G => x⁻¹)
  have hmem_S_sym : ∀ u : G, (u ∈ S ∨ u⁻¹ ∈ S) → u ∈ S_sym := by
    rintro u (hu | hu)
    · exact Or.inl hu
    · exact Or.inr ⟨u⁻¹, hu, inv_inv u⟩
  have h_step_ex : ∀ p : G × G, ∃ k : ℕ, ∃ t' ∈ T, ∃ h : H,
      p.1 * p.2 = t' * (h : G) ∧ h ∈ CayleyBall S₀ k := by
    intro p
    obtain ⟨t', ht'T, h, heq⟩ := h_decomp (p.1 * p.2)
    obtain ⟨k, hk⟩ := exists_cayleyBall_mem_of_closure_eq_top hS₀_gen h
    exact ⟨k, t', ht'T, h, heq, hk⟩
  choose rad h_rad using h_step_ex
  have hP_fin : (S_sym ×ˢ T).Finite := hS_sym_fin.prod hT_fin
  let K : ℕ := hP_fin.toFinset.sup rad + 1
  have hK_pos : 0 < K := Nat.succ_pos _
  have h_step : ∀ u ∈ S_sym, ∀ t ∈ T,
      ∃ t' ∈ T, ∃ h : H, u * t = t' * (h : G) ∧ h ∈ CayleyBall S₀ K := by
    intro u hu t ht
    obtain ⟨t', ht'T, h, heq, hball⟩ := h_rad (u, t)
    have hmemP : (u, t) ∈ hP_fin.toFinset := hP_fin.mem_toFinset.mpr ⟨hu, ht⟩
    have hle : rad (u, t) ≤ K :=
      le_trans (Finset.le_sup (f := rad) hmemP) (Nat.le_succ _)
    exact ⟨t', ht'T, h, heq, cayleyBall_monotone S₀ hle hball⟩
  have h_word : ∀ l : List G, (∀ s ∈ l, s ∈ S ∨ s⁻¹ ∈ S) →
      ∃ t ∈ T, ∃ h : H, l.prod = t * (h : G) ∧ h ∈ CayleyBall S₀ (K * l.length) := by
    intro l
    induction l with
    | nil =>
      intro _
      refine ⟨1, h1T, 1, by simp, ?_⟩
      simpa using one_mem_cayleyBall S₀ 0
    | cons u l' ih =>
      intro hl
      have hu : u ∈ S_sym := hmem_S_sym u (hl u (by simp))
      have hl' : ∀ s ∈ l', s ∈ S ∨ s⁻¹ ∈ S := fun s hs => hl s (by simp [hs])
      obtain ⟨t₁, ht₁T, h₁, hprod₁, hball₁⟩ := ih hl'
      obtain ⟨t₂, ht₂T, h₂, hstep, hball₂⟩ := h_step u hu t₁ ht₁T
      refine ⟨t₂, ht₂T, h₂ * h₁, ?_, ?_⟩
      · rw [List.prod_cons, hprod₁, ← mul_assoc, hstep, mul_assoc]
        simp
      · have hmul : h₂ * h₁ ∈ CayleyBall S₀ (K + K * l'.length) :=
          cayleyBall_mul S₀ hball₂ hball₁
        have hlen : K + K * l'.length = K * (u :: l').length := by
          rw [List.length_cons, Nat.mul_succ, Nat.add_comm]
        rwa [hlen] at hmul
  have hT_pos : 0 < T.ncard := (Set.ncard_pos hT_fin).mpr ⟨1, h1T⟩
  let C' : ℝ := (T.ncard : ℝ) * C * (K : ℝ) ^ d
  have hC'_pos : C' > 0 :=
    mul_pos (mul_pos (Nat.cast_pos.mpr hT_pos) hC_pos) (pow_pos (Nat.cast_pos.mpr hK_pos) d)
  refine ⟨S, hS_fin, hS_gen, C', d, hC'_pos, ?_⟩
  intro n hn
  have hKn_pos : 0 < K * n := Nat.mul_pos hK_pos hn
  have hBH_fin : (CayleyBall S₀ (K * n)).Finite := cayleyBall_finite hS₀_fin (K * n)
  let φ : G × H → G := fun p => p.1 * (p.2 : G)
  have hsub : CayleyBall S n ⊆ φ '' (T ×ˢ CayleyBall S₀ (K * n)) := by
    intro g hg
    obtain ⟨l, hl_len, hl_mem, rfl⟩ := hg
    obtain ⟨t, htT, h, hprod, hball⟩ := h_word l hl_mem
    have hball' : h ∈ CayleyBall S₀ (K * n) :=
      cayleyBall_monotone S₀ (Nat.mul_le_mul_left K hl_len) hball
    exact ⟨(t, h), ⟨htT, hball'⟩, hprod.symm⟩
  have hP_ball_fin : (T ×ˢ CayleyBall S₀ (K * n)).Finite := hT_fin.prod hBH_fin
  have hcard_nat : GrowthFunction S n ≤ T.ncard * GrowthFunction S₀ (K * n) := by
    unfold GrowthFunction
    calc
      (CayleyBall S n).ncard
          ≤ (φ '' (T ×ˢ CayleyBall S₀ (K * n))).ncard :=
            Set.ncard_le_ncard hsub (hP_ball_fin.image φ)
      _ ≤ (T ×ˢ CayleyBall S₀ (K * n)).ncard :=
            Set.ncard_image_le hP_ball_fin
      _ = T.ncard * (CayleyBall S₀ (K * n)).ncard := by
            rw [Set.ncard_prod]
  have hcard_real : (GrowthFunction S n : ℝ) ≤
      (T.ncard : ℝ) * (GrowthFunction S₀ (K * n) : ℝ) := by
    exact_mod_cast hcard_nat
  have hH_bound : (GrowthFunction S₀ (K * n) : ℝ) ≤ C * ((K * n : ℕ) : ℝ) ^ d :=
    hbound (K * n) hKn_pos
  have hT_nonneg : (0 : ℝ) ≤ (T.ncard : ℝ) := Nat.cast_nonneg _
  calc
    (GrowthFunction S n : ℝ)
        ≤ (T.ncard : ℝ) * (GrowthFunction S₀ (K * n) : ℝ) := hcard_real
    _ ≤ (T.ncard : ℝ) * (C * ((K * n : ℕ) : ℝ) ^ d) :=
          mul_le_mul_of_nonneg_left hH_bound hT_nonneg
    _ = C' * (n : ℝ) ^ d := by
          dsimp [C']
          rw [Nat.cast_mul, mul_pow]
          ring
