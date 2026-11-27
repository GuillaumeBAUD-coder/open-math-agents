import OMAReductions.R_Erdos82_erdos_82_variants_F_upper_bound_R1

/-! Step H2 of Erdos82.erdos_82.variants.F_upper_bound.R1 -/

section Helpers

open scoped Classical

private lemma factorial_mul_exp_ge_pow (j : ℕ) :
    (j : ℝ) ^ j ≤ (Real.exp 1) ^ j * (j.factorial : ℝ) := by
  have hj_pos : (0 : ℝ) < (j.factorial : ℝ) := by positivity
  have hsum : (j : ℝ) ^ j / (j.factorial : ℝ) ≤ Real.exp (j : ℝ) := by
    have h1 : (j : ℝ) ^ j / (j.factorial : ℝ) ≤
        ∑ i ∈ Finset.range (j + 1), (j : ℝ) ^ i / (i.factorial : ℝ) :=
      Finset.single_le_sum (f := fun i => (j : ℝ) ^ i / (i.factorial : ℝ))
        (fun i _ => by positivity) (Finset.mem_range.mpr (Nat.lt_succ_self j))
    exact h1.trans (Real.sum_le_exp_of_nonneg (Nat.cast_nonneg j) (j + 1))
  have hexp : Real.exp (j : ℝ) = (Real.exp 1) ^ j := by
    rw [← mul_one (j : ℝ), Real.exp_nat_mul]
  rw [hexp, div_le_iff₀ hj_pos] at hsum
  exact hsum

private lemma choose_real_le {W j : ℕ} (hj : 1 ≤ j) :
    (Nat.choose W j : ℝ) ≤ (Real.exp 1 * (W : ℝ) / (j : ℝ)) ^ j := by
  have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj
  have h1 : (Nat.choose W j : ℝ) * (j.factorial : ℝ) ≤ (W : ℝ) ^ j := by
    have hnat : Nat.choose W j * j.factorial ≤ W ^ j := by
      rw [mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose]
      exact Nat.descFactorial_le_pow W j
    exact_mod_cast hnat
  have h2 := factorial_mul_exp_ge_pow j
  have h3 : (Nat.choose W j : ℝ) * (j : ℝ) ^ j ≤ (Real.exp 1 * (W : ℝ)) ^ j := by
    calc (Nat.choose W j : ℝ) * (j : ℝ) ^ j
        ≤ (Nat.choose W j : ℝ) * ((Real.exp 1) ^ j * (j.factorial : ℝ)) :=
          mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg _)
      _ = (Real.exp 1) ^ j * ((Nat.choose W j : ℝ) * (j.factorial : ℝ)) := by ring
      _ ≤ (Real.exp 1) ^ j * (W : ℝ) ^ j :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = (Real.exp 1 * (W : ℝ)) ^ j := by rw [mul_pow]
  rw [div_pow, le_div_iff₀ (pow_pos hjpos j)]
  exact h3

private lemma card_leCard_le (n m : ℕ) (hn : 1 ≤ n) :
    ((Finset.univ : Finset (Finset (Fin n))).filter (fun L => L.card ≤ m)).card ≤
      (m + 1) * n ^ m := by
  let S := (Finset.univ : Finset (Finset (Fin n))).filter (fun L => L.card ≤ m)
  let T := (Finset.range (m + 1)).biUnion (fun i => (Finset.univ : Finset (Fin n)).powersetCard i)
  have hsub : S ⊆ T := by
    intro L hL
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hL
    simp only [T, Finset.mem_biUnion, Finset.mem_range, Finset.mem_powersetCard]
    exact ⟨L.card, Nat.lt_succ_of_le hL, Finset.subset_univ _, rfl⟩
  have hcard : S.card ≤ T.card := Finset.card_le_card hsub
  have hT : T.card ≤ ∑ i ∈ Finset.range (m + 1), Nat.choose n i := by
    refine (Finset.card_biUnion_le).trans ?_
    refine Finset.sum_le_sum fun i _ => ?_
    rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  have hsum : ∑ i ∈ Finset.range (m + 1), Nat.choose n i ≤ (m + 1) * n ^ m := by
    calc ∑ i ∈ Finset.range (m + 1), Nat.choose n i
        ≤ ∑ _ ∈ Finset.range (m + 1), n ^ m := by
          refine Finset.sum_le_sum fun i hi => ?_
          rw [Finset.mem_range] at hi
          have hch : Nat.choose n i ≤ n ^ i := by
            have hf : 1 ≤ i.factorial := Nat.factorial_pos i
            calc Nat.choose n i
                ≤ Nat.choose n i * i.factorial := Nat.le_mul_of_pos_right _ hf
              _ = n.descFactorial i := by rw [mul_comm, Nat.descFactorial_eq_factorial_mul_choose]
              _ ≤ n ^ i := Nat.descFactorial_le_pow n i
          exact hch.trans (Nat.pow_le_pow_right hn (Nat.le_of_lt_succ hi))
      _ = (m + 1) * n ^ m := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
  exact hcard.trans (hT.trans hsum)

private lemma pow_div_log_le_four_pow {n k : ℕ} (_hk : 1 ≤ k)
    (hsqrt : Real.sqrt (n : ℝ) ≤ (k : ℝ)) :
    n ^ (k / (Nat.log 2 k + 1)) ≤ 4 ^ k := by
  have hn_le_k2 : n ≤ k ^ 2 := by
    have hr : (n : ℝ) ≤ (k : ℝ) ^ 2 := by
      have hsq := mul_self_le_mul_self (Real.sqrt_nonneg n) hsqrt
      rw [Real.mul_self_sqrt (Nat.cast_nonneg n), ← sq] at hsq
      exact hsq
    exact_mod_cast hr
  have hk_lt : k ≤ 2 ^ (Nat.log 2 k + 1) :=
    (Nat.lt_pow_succ_log_self (by decide : 1 < 2) k).le
  have hn_le_4 : n ≤ 4 ^ (Nat.log 2 k + 1) := by
    calc n ≤ k ^ 2 := hn_le_k2
      _ ≤ (2 ^ (Nat.log 2 k + 1)) ^ 2 := Nat.pow_le_pow_left hk_lt 2
      _ = (2 ^ 2) ^ (Nat.log 2 k + 1) := by rw [← pow_mul, mul_comm, pow_mul]
      _ = 4 ^ (Nat.log 2 k + 1) := by norm_num
  have hmul : (Nat.log 2 k + 1) * (k / (Nat.log 2 k + 1)) ≤ k :=
    Nat.mul_div_le k (Nat.log 2 k + 1)
  calc n ^ (k / (Nat.log 2 k + 1))
      ≤ (4 ^ (Nat.log 2 k + 1)) ^ (k / (Nat.log 2 k + 1)) :=
        Nat.pow_le_pow_left hn_le_4 _
    _ = 4 ^ ((Nat.log 2 k + 1) * (k / (Nat.log 2 k + 1))) := by rw [← pow_mul]
    _ ≤ 4 ^ k := Nat.pow_le_pow_right (by decide) hmul

private lemma card_mid_le (n : ℕ) (a : Fin n) (W : ℕ) :
    ((Finset.univ : Finset (Fin n)).filter (fun x => a ≤ x ∧ (x : ℕ) ≤ (a : ℕ) + W)).card ≤
      W + 1 := by
  let M := (Finset.univ : Finset (Fin n)).filter (fun x => a ≤ x ∧ (x : ℕ) ≤ (a : ℕ) + W)
  change M.card ≤ W + 1
  have h1 : M.card ≤ (Finset.range (W + 1)).card := by
    refine Finset.card_le_card_of_injOn (fun x => (x : ℕ) - (a : ℕ)) ?_ ?_
    · intro x hx
      have hx' := (Finset.mem_filter.mp (Finset.mem_coe.mp hx)).2
      have ha : (a : ℕ) ≤ (x : ℕ) := hx'.1
      have hle : (x : ℕ) ≤ (a : ℕ) + W := hx'.2
      exact Finset.mem_coe.mpr (Finset.mem_range.mpr (by dsimp only; omega))
    · intro x hx y hy hxy
      have hx' := (Finset.mem_filter.mp (Finset.mem_coe.mp hx)).2
      have hy' := (Finset.mem_filter.mp (Finset.mem_coe.mp hy)).2
      have ha1 : (a : ℕ) ≤ (x : ℕ) := hx'.1
      have ha2 : (a : ℕ) ≤ (y : ℕ) := hy'.1
      dsimp only at hxy
      exact Fin.ext (by omega)
  exact h1.trans (by simp [Finset.card_range])

end Helpers

theorem OMA.solution : OMA.R_Erdos82_erdos_82_variants_F_upper_bound_R1.H2 := by
  intro C₁ hC₁
  refine ⟨1 / (4096 * (C₁ + 1)), by positivity, ?_⟩
  set c₂ : ℝ := 1 / (4096 * (C₁ + 1))
  set α : ℝ := (1 / 2 : ℝ) * Real.log (4 / 3)
  have hα : 0 < α := by
    have : 0 < Real.log (4 / 3) := Real.log_pos (by norm_num)
    positivity
  set M_decay : ℝ := 16 * (Nat.factorial 15 : ℝ) / α ^ 15
  set B_req : ℝ := max (max (16 : ℝ) (1 / c₂)) M_decay
  have hB_pos : 0 < B_req := lt_of_lt_of_le (by norm_num) (le_trans (le_max_left _ _) (le_max_left _ _))
  obtain ⟨N₁, hN₁⟩ := exists_nat_gt (B_req ^ 2)
  refine ⟨max N₁ 2, fun n hn k hk_sqrt hk_le => ?_⟩
  have hn2 : 2 ≤ n := le_trans (le_max_right _ _) hn
  have hn1 : 1 ≤ n := by omega
  have hnN₁ : N₁ ≤ n := le_trans (le_max_left _ _) hn
  have hsqrt_gt_B : B_req < Real.sqrt (n : ℝ) := by
    have hn_gt_B2 : B_req ^ 2 < (n : ℝ) := lt_of_lt_of_le hN₁ (by exact_mod_cast hnN₁)
    have hsq := Real.sqrt_lt_sqrt (sq_nonneg B_req) hn_gt_B2
    rwa [Real.sqrt_sq hB_pos.le] at hsq
  have hk_gt_16 : (16 : ℝ) < (k : ℝ) :=
    lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_left _ _)) (lt_of_lt_of_le hsqrt_gt_B hk_sqrt)
  have hk16 : 16 ≤ k := by
    have : (16 : ℝ) ≤ (k : ℝ) := hk_gt_16.le
    exact_mod_cast this
  have hk1 : 1 ≤ k := by omega
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
  have hk_gt_inv_c2 : 1 / c₂ < (k : ℝ) :=
    lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_left _ _)) (lt_of_lt_of_le hsqrt_gt_B hk_sqrt)
  have hc2_k32 : 1 ≤ c₂ * (k : ℝ) ^ (3 / 2 : ℝ) := by
    have hk_le_k32 : (k : ℝ) ≤ (k : ℝ) ^ (3 / 2 : ℝ) := by
      have hk_ge1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
      calc (k : ℝ) = (k : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ (k : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hk_ge1 (by norm_num)
    have h1 : 1 < c₂ * (k : ℝ) := by rwa [div_lt_iff₀ (by positivity : 0 < c₂), mul_comm] at hk_gt_inv_c2
    have h2 : c₂ * (k : ℝ) ≤ c₂ * (k : ℝ) ^ (3 / 2 : ℝ) :=
      mul_le_mul_of_nonneg_left hk_le_k32 (by positivity)
    linarith
  set m : ℕ := k / (Nat.log 2 k + 1)
  have hm5 : 5 * m ≤ k := by
    have hlog : 4 ≤ Nat.log 2 k := by
      have h16 : Nat.log 2 16 = 4 := by decide
      exact h16 ▸ Nat.log_mono_right hk16
    have hmul : (Nat.log 2 k + 1) * m ≤ k := Nat.mul_div_le k (Nat.log 2 k + 1)
    have hle : 5 * m ≤ (Nat.log 2 k + 1) * m := Nat.mul_le_mul_right m (by omega)
    omega
  have hm_le_n : m ≤ n := by omega
  set W : ℕ := Nat.floor (c₂ * (k : ℝ) ^ (3 / 2 : ℝ))
  let LeCard := (Finset.univ : Finset (Finset (Fin n))).filter (fun L => L.card ≤ m)
  let Mid (a : Fin n) :=
    (Finset.univ : Finset (Fin n)).filter (fun x => a ≤ x ∧ (x : ℕ) ≤ (a : ℕ) + W)
  let Small := (Finset.univ : Finset (Finset (Fin n))).filter (fun U =>
    U.card = k ∧ ∃ a b : Fin n, a ≤ b ∧ (b : ℝ) - (a : ℝ) ≤ c₂ * (k : ℝ) ^ (3 / 2 : ℝ) ∧
      (U.filter (· < a)).card ≤ m ∧ (U.filter (b < ·)).card ≤ m)
  let Pool := Finset.univ.sigma (fun a : Fin n =>
    LeCard ×ˢ LeCard ×ˢ ((Mid a).powerset.filter (fun M => k - 2 * m ≤ M.card ∧ M.card ≤ k)))
  have hSmall_sub : Small ⊆ Pool.image (fun p => p.2.1 ∪ p.2.2.2 ∪ p.2.2.1) := by
    intro U hU
    simp only [Small, Finset.mem_filter, Finset.mem_univ, true_and] at hU
    rcases hU with ⟨hUk, a, b, hab, hspan, hLa, hRb⟩
    let L := U.filter (· < a)
    let R := U.filter (b < ·)
    let M := U.filter (fun x => a ≤ x ∧ x ≤ b)
    have hUeq : L ∪ M ∪ R = U := by
      ext x
      simp only [L, M, R, Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro ((⟨hx, _⟩ | ⟨hx, _⟩) | ⟨hx, _⟩) <;> exact hx
      · intro hx
        rcases lt_or_ge x a with hxa | hax
        · exact Or.inl (Or.inl ⟨hx, hxa⟩)
        · rcases le_or_gt x b with hxb | hbx
          · exact Or.inl (Or.inr ⟨hx, hax, hxb⟩)
          · exact Or.inr ⟨hx, hbx⟩
    have hdisjLM : Disjoint L M := by
      rw [Finset.disjoint_left]
      intro x hxL hxM
      simp only [L, M, Finset.mem_filter] at hxL hxM
      exact absurd hxL.2 (not_lt.mpr hxM.2.1)
    have hdisjLR : Disjoint L R := by
      rw [Finset.disjoint_left]
      intro x hxL hxR
      simp only [L, R, Finset.mem_filter] at hxL hxR
      have : x < b := lt_of_lt_of_le hxL.2 hab
      exact absurd hxR.2 (not_lt.mpr this.le)
    have hdisjMR : Disjoint M R := by
      rw [Finset.disjoint_left]
      intro x hxM hxR
      simp only [M, R, Finset.mem_filter] at hxM hxR
      exact absurd hxR.2 (not_lt.mpr hxM.2.2)
    have hdisjLMR : Disjoint (L ∪ M) R := Finset.disjoint_union_left.mpr ⟨hdisjLR, hdisjMR⟩
    have hcard_eq : L.card + M.card + R.card = k := by
      rw [← Finset.card_union_of_disjoint hdisjLM, ← Finset.card_union_of_disjoint hdisjLMR, hUeq, hUk]
    have hL_le : L.card ≤ m := hLa
    have hR_le : R.card ≤ m := hRb
    have hMcard : k - 2 * m ≤ M.card ∧ M.card ≤ k := by omega
    have hb_le_W : (b : ℕ) ≤ (a : ℕ) + W := by
      have hab_nat : (a : ℕ) ≤ (b : ℕ) := hab
      have hba_real : (((b : ℕ) - (a : ℕ) : ℕ) : ℝ) ≤ c₂ * (k : ℝ) ^ (3 / 2 : ℝ) := by
        rw [Nat.cast_sub hab_nat]
        exact hspan
      have hba_nat : (b : ℕ) - (a : ℕ) ≤ W := Nat.le_floor hba_real
      omega
    have hMsub : M ⊆ Mid a := by
      intro x hx
      simp only [M, Finset.mem_filter] at hx
      simp only [Mid, Finset.mem_filter, Finset.mem_univ, true_and]
      have hxb_nat : (x : ℕ) ≤ (b : ℕ) := hx.2.2
      exact ⟨hx.2.1, hxb_nat.trans hb_le_W⟩
    simp only [Finset.mem_image, Pool, Finset.mem_sigma, Finset.mem_univ, Finset.mem_product,
      Finset.mem_powerset, Finset.mem_filter, true_and]
    refine ⟨⟨a, L, R, M⟩, ⟨?_, ?_, hMsub, hMcard⟩, hUeq⟩
    · simp only [LeCard, Finset.mem_filter, Finset.mem_univ, true_and]; exact hLa
    · simp only [LeCard, Finset.mem_filter, Finset.mem_univ, true_and]; exact hRb
  have hLeCard : (LeCard.card : ℝ) ≤ ((n : ℝ) + 1) * (4 : ℝ) ^ k := by
    have h1 : LeCard.card ≤ (m + 1) * n ^ m := card_leCard_le n m hn1
    have h2 : n ^ m ≤ 4 ^ k := pow_div_log_le_four_pow hk1 hk_sqrt
    have h3 : (m + 1) * n ^ m ≤ (n + 1) * 4 ^ k :=
      Nat.mul_le_mul (Nat.add_le_add_right hm_le_n 1) h2
    exact_mod_cast h1.trans h3
  have hW_bound : ((W + 1 : ℕ) : ℝ) ≤ 2 * c₂ * (k : ℝ) ^ (3 / 2 : ℝ) := by
    have hf : (W : ℝ) ≤ c₂ * (k : ℝ) ^ (3 / 2 : ℝ) := Nat.floor_le (by positivity)
    push_cast
    linarith
  have hexp3 : Real.exp 1 < 3 := Real.exp_one_lt_d9.trans (by norm_num)
  have hbase_le : 4 * Real.exp 1 * c₂ ≤ 1 := by
    have h1 : 4 * Real.exp 1 * c₂ = Real.exp 1 / (1024 * (C₁ + 1)) := by
      dsimp only [c₂]; field_simp; ring
    rw [h1, div_le_one (by positivity)]
    nlinarith
  have hchoose_bound : ∀ j ∈ Finset.Icc (k - 2 * m) k,
      (Nat.choose (W + 1) j : ℝ) ≤
        (4 * Real.exp 1 * c₂) ^ ((k : ℝ) / 2) * (k : ℝ) ^ ((k : ℝ) / 2) := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    have hj_ge_half : (k : ℝ) / 2 ≤ (j : ℝ) := by
      have hnat : k ≤ 2 * j := by omega
      have : (k : ℝ) ≤ 2 * (j : ℝ) := by exact_mod_cast hnat
      linarith
    have hj1 : 1 ≤ j := by omega
    have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj1
    have h1 := choose_real_le (W := W + 1) hj1
    have hk32 : (k : ℝ) ^ (3 / 2 : ℝ) = (k : ℝ) * Real.sqrt (k : ℝ) := by
      have hsplit : (3 / 2 : ℝ) = 1 + 1 / 2 := by norm_num
      rw [hsplit, Real.rpow_add hkpos, Real.rpow_one, Real.sqrt_eq_rpow]
    have h2 : Real.exp 1 * ((W + 1 : ℕ) : ℝ) / (j : ℝ) ≤
        4 * Real.exp 1 * c₂ * Real.sqrt (k : ℝ) := by
      calc Real.exp 1 * ((W + 1 : ℕ) : ℝ) / (j : ℝ)
          ≤ Real.exp 1 * (2 * c₂ * (k : ℝ) ^ (3 / 2 : ℝ)) / ((k : ℝ) / 2) := by
            refine div_le_div₀ (by positivity) ?_ (by positivity) hj_ge_half
            exact mul_le_mul_of_nonneg_left hW_bound (Real.exp_pos 1).le
        _ = 4 * Real.exp 1 * c₂ * Real.sqrt (k : ℝ) := by
            rw [hk32]
            field_simp; ring
    have h3 : (Real.exp 1 * ((W + 1 : ℕ) : ℝ) / (j : ℝ)) ^ j ≤
        (4 * Real.exp 1 * c₂ * Real.sqrt (k : ℝ)) ^ j := by
      exact pow_le_pow_left₀ (by positivity) h2 j
    have h4 : (4 * Real.exp 1 * c₂ * Real.sqrt (k : ℝ)) ^ j =
        (4 * Real.exp 1 * c₂) ^ (j : ℝ) * (Real.sqrt (k : ℝ)) ^ (j : ℝ) := by
      rw [mul_pow, ← Real.rpow_natCast (4 * Real.exp 1 * c₂) j, ← Real.rpow_natCast (Real.sqrt (k : ℝ)) j]
    have h5 : (4 * Real.exp 1 * c₂) ^ (j : ℝ) ≤ (4 * Real.exp 1 * c₂) ^ ((k : ℝ) / 2) :=
      Real.rpow_le_rpow_of_exponent_ge (by positivity) hbase_le hj_ge_half
    have h6 : (Real.sqrt (k : ℝ)) ^ (j : ℝ) ≤ (k : ℝ) ^ ((k : ℝ) / 2) := by
      have hsq_ge1 : 1 ≤ Real.sqrt (k : ℝ) := by
        rw [Real.le_sqrt (by norm_num) (Nat.cast_nonneg k)]
        norm_num
        exact_mod_cast hk1
      have hj_le_k : (j : ℝ) ≤ (k : ℝ) := by exact_mod_cast hj.2
      calc (Real.sqrt (k : ℝ)) ^ (j : ℝ)
          ≤ (Real.sqrt (k : ℝ)) ^ (k : ℝ) := Real.rpow_le_rpow_of_exponent_le hsq_ge1 hj_le_k
        _ = ((k : ℝ) ^ (1 / 2 : ℝ)) ^ (k : ℝ) := by rw [Real.sqrt_eq_rpow]
        _ = (k : ℝ) ^ ((k : ℝ) / 2) := by
            rw [← Real.rpow_mul (Nat.cast_nonneg k)]
            congr 1
            ring
    calc (Nat.choose (W + 1) j : ℝ)
        ≤ (Real.exp 1 * ((W + 1 : ℕ) : ℝ) / (j : ℝ)) ^ j := h1
      _ ≤ (4 * Real.exp 1 * c₂ * Real.sqrt (k : ℝ)) ^ j := h3
      _ = (4 * Real.exp 1 * c₂) ^ (j : ℝ) * (Real.sqrt (k : ℝ)) ^ (j : ℝ) := h4
      _ ≤ (4 * Real.exp 1 * c₂) ^ ((k : ℝ) / 2) * (k : ℝ) ^ ((k : ℝ) / 2) :=
          mul_le_mul h5 h6 (by positivity) (by positivity)
  have hMid_bound : ∀ a : Fin n,
      (((Mid a).powerset.filter (fun M => k - 2 * m ≤ M.card ∧ M.card ≤ k)).card : ℝ) ≤
        ((n : ℝ) + 1) * ((4 * Real.exp 1 * c₂) ^ ((k : ℝ) / 2) * (k : ℝ) ^ ((k : ℝ) / 2)) := by
    intro a
    let F := (Mid a).powerset.filter (fun M => k - 2 * m ≤ M.card ∧ M.card ≤ k)
    let G := (Finset.Icc (k - 2 * m) k).biUnion (fun j => (Mid a).powersetCard j)
    have hFG : F ⊆ G := by
      intro M hM
      simp only [F, Finset.mem_filter, Finset.mem_powerset] at hM
      simp only [G, Finset.mem_biUnion, Finset.mem_Icc, Finset.mem_powersetCard]
      exact ⟨M.card, hM.2, hM.1, rfl⟩
    have hcard_le : F.card ≤ ∑ j ∈ Finset.Icc (k - 2 * m) k, Nat.choose (W + 1) j := by
      refine (Finset.card_le_card hFG).trans ((Finset.card_biUnion_le).trans ?_)
      refine Finset.sum_le_sum fun j _ => ?_
      rw [Finset.card_powersetCard]
      exact Nat.choose_le_choose j (card_mid_le n a W)
    have hIcc_le : ((Finset.Icc (k - 2 * m) k).card : ℝ) ≤ (n : ℝ) + 1 := by
      have : (Finset.Icc (k - 2 * m) k).card ≤ n + 1 := by
        rw [Nat.card_Icc]
        omega
      exact_mod_cast this
    calc (F.card : ℝ)
        ≤ ∑ j ∈ Finset.Icc (k - 2 * m) k, (Nat.choose (W + 1) j : ℝ) := by exact_mod_cast hcard_le
      _ ≤ ∑ _ ∈ Finset.Icc (k - 2 * m) k,
            ((4 * Real.exp 1 * c₂) ^ ((k : ℝ) / 2) * (k : ℝ) ^ ((k : ℝ) / 2)) :=
          Finset.sum_le_sum hchoose_bound
      _ = ((Finset.Icc (k - 2 * m) k).card : ℝ) *
            ((4 * Real.exp 1 * c₂) ^ ((k : ℝ) / 2) * (k : ℝ) ^ ((k : ℝ) / 2)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((n : ℝ) + 1) * ((4 * Real.exp 1 * c₂) ^ ((k : ℝ) / 2) * (k : ℝ) ^ ((k : ℝ) / 2)) :=
          mul_le_mul_of_nonneg_right hIcc_le (by positivity)
  have hPool_card : (Small.card : ℝ) ≤
      (n : ℝ) * ((n : ℝ) + 1) ^ 3 * (256 : ℝ) ^ ((k : ℝ) / 2) *
        (4 * Real.exp 1 * c₂) ^ ((k : ℝ) / 2) * (k : ℝ) ^ ((k : ℝ) / 2) := by
    have hc1 : Small.card ≤ Pool.card := (Finset.card_le_card hSmall_sub).trans Finset.card_image_le
    have hc2 : Pool.card = ∑ a : Fin n,
        LeCard.card * (LeCard.card * ((Mid a).powerset.filter (fun M => k - 2 * m ≤ M.card ∧ M.card ≤ k)).card) := by
      simp only [Pool, Finset.card_sigma, Finset.card_product]
    have h16 : (16 : ℝ) ^ k = (256 : ℝ) ^ ((k : ℝ) / 2) := by
      calc (16 : ℝ) ^ k
          = (16 : ℝ) ^ (k : ℝ) := (Real.rpow_natCast 16 k).symm
        _ = (16 : ℝ) ^ ((2 : ℝ) * ((k : ℝ) / 2)) := by congr 1; ring
        _ = ((16 : ℝ) ^ (2 : ℝ)) ^ ((k : ℝ) / 2) := Real.rpow_mul (by norm_num) 2 ((k : ℝ) / 2)
        _ = (256 : ℝ) ^ ((k : ℝ) / 2) := by norm_num
    have hterm : ∀ a : Fin n,
        (LeCard.card : ℝ) * ((LeCard.card : ℝ) *
          (((Mid a).powerset.filter (fun M => k - 2 * m ≤ M.card ∧ M.card ≤ k)).card : ℝ)) ≤
        ((n : ℝ) + 1) ^ 3 * (256 : ℝ) ^ ((k : ℝ) / 2) *
          (4 * Real.exp 1 * c₂) ^ ((k : ℝ) / 2) * (k : ℝ) ^ ((k : ℝ) / 2) := by
      intro a
      calc (LeCard.card : ℝ) * ((LeCard.card : ℝ) *
            (((Mid a).powerset.filter (fun M => k - 2 * m ≤ M.card ∧ M.card ≤ k)).card : ℝ))
          ≤ (((n : ℝ) + 1) * (4 : ℝ) ^ k) * ((((n : ℝ) + 1) * (4 : ℝ) ^ k) *
              (((n : ℝ) + 1) * ((4 * Real.exp 1 * c₂) ^ ((k : ℝ) / 2) * (k : ℝ) ^ ((k : ℝ) / 2)))) := by
            refine mul_le_mul hLeCard (mul_le_mul hLeCard (hMid_bound a) (by positivity) (by positivity))
              (by positivity) (by positivity)
        _ = ((n : ℝ) + 1) ^ 3 * ((4 : ℝ) ^ k * (4 : ℝ) ^ k) *
              (4 * Real.exp 1 * c₂) ^ ((k : ℝ) / 2) * (k : ℝ) ^ ((k : ℝ) / 2) := by ring
        _ = ((n : ℝ) + 1) ^ 3 * (16 : ℝ) ^ k *
              (4 * Real.exp 1 * c₂) ^ ((k : ℝ) / 2) * (k : ℝ) ^ ((k : ℝ) / 2) := by
            have h44 : (4 : ℝ) ^ k * (4 : ℝ) ^ k = (16 : ℝ) ^ k := by
              rw [← mul_pow]; norm_num
            rw [h44]
        _ = ((n : ℝ) + 1) ^ 3 * (256 : ℝ) ^ ((k : ℝ) / 2) *
              (4 * Real.exp 1 * c₂) ^ ((k : ℝ) / 2) * (k : ℝ) ^ ((k : ℝ) / 2) := by rw [h16]
    calc (Small.card : ℝ)
        ≤ (Pool.card : ℝ) := by exact_mod_cast hc1
      _ = ∑ a : Fin n, (LeCard.card : ℝ) * ((LeCard.card : ℝ) *
            (((Mid a).powerset.filter (fun M => k - 2 * m ≤ M.card ∧ M.card ≤ k)).card : ℝ)) := by
          rw [hc2]; push_cast; rfl
      _ ≤ ∑ _ : Fin n, (((n : ℝ) + 1) ^ 3 * (256 : ℝ) ^ ((k : ℝ) / 2) *
            (4 * Real.exp 1 * c₂) ^ ((k : ℝ) / 2) * (k : ℝ) ^ ((k : ℝ) / 2)) :=
          Finset.sum_le_sum fun a _ => hterm a
      _ = (n : ℝ) * ((n : ℝ) + 1) ^ 3 * (256 : ℝ) ^ ((k : ℝ) / 2) *
            (4 * Real.exp 1 * c₂) ^ ((k : ℝ) / 2) * (k : ℝ) ^ ((k : ℝ) / 2) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  have hprod_le : (Small.card : ℝ) * ((n : ℝ) * (C₁ / (k : ℝ)) ^ ((k : ℝ) / 2)) ≤
      (n : ℝ) ^ 2 * ((n : ℝ) + 1) ^ 3 * (3 / 4 : ℝ) ^ (Real.sqrt (n : ℝ) / 2) := by
    have hdiv_rpow : (C₁ / (k : ℝ)) ^ ((k : ℝ) / 2) =
        C₁ ^ ((k : ℝ) / 2) / (k : ℝ) ^ ((k : ℝ) / 2) :=
      Real.div_rpow hC₁.le (Nat.cast_nonneg k) _
    have hk_rpow_ne : (k : ℝ) ^ ((k : ℝ) / 2) ≠ 0 := (Real.rpow_pos_of_pos hkpos _).ne'
    have hbase_34 : 256 * (4 * Real.exp 1 * c₂) * C₁ ≤ 3 / 4 := by
      have h1 : 256 * (4 * Real.exp 1 * c₂) * C₁ = Real.exp 1 / 4 * (C₁ / (C₁ + 1)) := by
        dsimp only [c₂]; field_simp; ring
      have h2 : C₁ / (C₁ + 1) ≤ 1 := div_le_one_of_le₀ (by linarith) (by positivity)
      rw [h1]
      calc Real.exp 1 / 4 * (C₁ / (C₁ + 1))
          ≤ Real.exp 1 / 4 * 1 := mul_le_mul_of_nonneg_left h2 (by positivity)
        _ ≤ 3 / 4 := by linarith
    have hrpow_le : (256 : ℝ) ^ ((k : ℝ) / 2) * (4 * Real.exp 1 * c₂) ^ ((k : ℝ) / 2) *
        C₁ ^ ((k : ℝ) / 2) ≤ (3 / 4 : ℝ) ^ (Real.sqrt (n : ℝ) / 2) := by
      have hmul1 : (256 : ℝ) ^ ((k : ℝ) / 2) * (4 * Real.exp 1 * c₂) ^ ((k : ℝ) / 2) *
          C₁ ^ ((k : ℝ) / 2) = (256 * (4 * Real.exp 1 * c₂) * C₁) ^ ((k : ℝ) / 2) := by
        rw [← Real.mul_rpow (by positivity) (by positivity),
          ← Real.mul_rpow (by positivity) hC₁.le]
      rw [hmul1]
      calc (256 * (4 * Real.exp 1 * c₂) * C₁) ^ ((k : ℝ) / 2)
          ≤ (3 / 4 : ℝ) ^ ((k : ℝ) / 2) :=
            Real.rpow_le_rpow (by positivity) hbase_34 (by positivity)
        _ ≤ (3 / 4 : ℝ) ^ (Real.sqrt (n : ℝ) / 2) :=
            Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by linarith)
    calc (Small.card : ℝ) * ((n : ℝ) * (C₁ / (k : ℝ)) ^ ((k : ℝ) / 2))
        ≤ ((n : ℝ) * ((n : ℝ) + 1) ^ 3 * (256 : ℝ) ^ ((k : ℝ) / 2) *
            (4 * Real.exp 1 * c₂) ^ ((k : ℝ) / 2) * (k : ℝ) ^ ((k : ℝ) / 2)) *
            ((n : ℝ) * (C₁ / (k : ℝ)) ^ ((k : ℝ) / 2)) :=
          mul_le_mul_of_nonneg_right hPool_card (by positivity)
      _ = (n : ℝ) ^ 2 * ((n : ℝ) + 1) ^ 3 *
            ((256 : ℝ) ^ ((k : ℝ) / 2) * (4 * Real.exp 1 * c₂) ^ ((k : ℝ) / 2) *
              C₁ ^ ((k : ℝ) / 2)) := by
          rw [hdiv_rpow]
          field_simp [hk_rpow_ne]
      _ ≤ (n : ℝ) ^ 2 * ((n : ℝ) + 1) ^ 3 * (3 / 4 : ℝ) ^ (Real.sqrt (n : ℝ) / 2) :=
          mul_le_mul_of_nonneg_left hrpow_le (by positivity)
  have hfinal : 2 * (n : ℝ) ^ 4 * ((n : ℝ) + 1) ^ 3 * (3 / 4 : ℝ) ^ (Real.sqrt (n : ℝ) / 2) < 1 := by
    set t : ℝ := Real.sqrt (n : ℝ)
    have ht_pos : 0 < t := lt_trans hB_pos hsqrt_gt_B
    have hM_lt_t : M_decay < t :=
      lt_of_le_of_lt (le_max_right _ _) hsqrt_gt_B
    have hn_eq : (n : ℝ) = t ^ 2 := (Real.sq_sqrt (Nat.cast_nonneg n)).symm
    have hpoly : 2 * (n : ℝ) ^ 4 * ((n : ℝ) + 1) ^ 3 ≤ 16 * t ^ 14 := by
      have hn1_le : (n : ℝ) + 1 ≤ 2 * (n : ℝ) := by
        have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
        linarith
      calc 2 * (n : ℝ) ^ 4 * ((n : ℝ) + 1) ^ 3
          ≤ 2 * (n : ℝ) ^ 4 * (2 * (n : ℝ)) ^ 3 :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hn1_le 3) (by positivity)
        _ = 16 * (n : ℝ) ^ 7 := by ring
        _ = 16 * t ^ 14 := by rw [hn_eq]; ring
    have hexp_inv : (3 / 4 : ℝ) ^ (t / 2) = (Real.exp (α * t))⁻¹ := by
      have h43 : (3 / 4 : ℝ) = (4 / 3 : ℝ)⁻¹ := by norm_num
      rw [h43, Real.inv_rpow (by norm_num), Real.rpow_def_of_pos (by norm_num)]
      congr 1
      dsimp only [α]
      ring
    have hexp_ge : (α * t) ^ 15 / (Nat.factorial 15 : ℝ) ≤ Real.exp (α * t) := by
      have h1 : (α * t) ^ 15 / (Nat.factorial 15 : ℝ) ≤
          ∑ i ∈ Finset.range 16, (α * t) ^ i / (i.factorial : ℝ) :=
        Finset.single_le_sum (f := fun i => (α * t) ^ i / (i.factorial : ℝ))
          (fun i _ => by positivity) (Finset.mem_range.mpr (by decide))
      exact h1.trans (Real.sum_le_exp_of_nonneg (by positivity) 16)
    have hdecay : (3 / 4 : ℝ) ^ (t / 2) ≤ (Nat.factorial 15 : ℝ) / (α * t) ^ 15 := by
      rw [hexp_inv, ← one_div, div_le_div_iff₀ (Real.exp_pos _) (by positivity)]
      have h := mul_le_mul_of_nonneg_left hexp_ge (by positivity : (0 : ℝ) ≤ (Nat.factorial 15 : ℝ))
      have hfact : (Nat.factorial 15 : ℝ) ≠ 0 := by positivity
      calc 1 * (α * t) ^ 15
          = (Nat.factorial 15 : ℝ) * ((α * t) ^ 15 / (Nat.factorial 15 : ℝ)) := by
            field_simp [hfact]
        _ ≤ (Nat.factorial 15 : ℝ) * Real.exp (α * t) := h
    calc 2 * (n : ℝ) ^ 4 * ((n : ℝ) + 1) ^ 3 * (3 / 4 : ℝ) ^ (t / 2)
        ≤ (16 * t ^ 14) * ((Nat.factorial 15 : ℝ) / (α * t) ^ 15) :=
          mul_le_mul hpoly hdecay (by positivity) (by positivity)
      _ = M_decay / t := by
          dsimp only [M_decay]
          field_simp [ht_pos.ne', hα.ne']
      _ < 1 := (div_lt_one ht_pos).mpr hM_lt_t
  have hgoal : ((n : ℝ) ^ 2 * ((n : ℝ) + 1) ^ 3 * (3 / 4 : ℝ) ^ (Real.sqrt (n : ℝ) / 2)) <
      1 / (2 * (n : ℝ) ^ 2) := by
    rw [lt_div_iff₀ (by positivity)]
    linarith
  exact lt_of_le_of_lt hprod_le hgoal

