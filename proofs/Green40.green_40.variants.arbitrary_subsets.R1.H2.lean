import OMAReductions.R_Green40_green_40_variants_arbitrary_subsets_R1

namespace OMA.Green40R1H2

open Green40 Filter Topology Finset
open scoped ENNReal Pointwise

private lemma fin_append_add {n m : ℕ} (x₁ x₂ : 𝔽₂ n) (y₁ y₂ : 𝔽₂ m) :
    Fin.append (x₁ + x₂) (y₁ + y₂) = Fin.append x₁ y₁ + Fin.append x₂ y₂ := by
  ext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp [Fin.append_left]
  · simp [Fin.append_right]

private lemma fin_append_inj {n m : ℕ} :
    Function.Injective (fun p : 𝔽₂ n × 𝔽₂ m => Fin.append p.1 p.2) := by
  rintro ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ h
  ext i
  · have h1 := congrFun h (Fin.castAdd m i)
    simpa [Fin.append_left] using h1
  · have h2 := congrFun h (Fin.natAdd n i)
    simpa [Fin.append_right] using h2

private lemma hammingNorm_append {n m : ℕ} (x : 𝔽₂ n) (y : 𝔽₂ m) :
    hammingNorm (Fin.append x y) = hammingNorm x + hammingNorm y := by
  unfold hammingNorm
  simp only [Finset.card_filter, Fin.sum_univ_add, Fin.append_left, Fin.append_right]

private def natOfF2 : ∀ {k : ℕ}, 𝔽₂ k → ℕ
  | 0, _ => 0
  | _ + 1, s => (if s 0 = 1 then 1 else 0) + 2 * natOfF2 (fun i => s i.succ)

private lemma natOfF2_lt : ∀ {k : ℕ} (s : 𝔽₂ k), natOfF2 s < 2 ^ k
  | 0, _ => by simp [natOfF2]
  | k + 1, s => by
      have ih := natOfF2_lt (fun i => s i.succ)
      have h0 : (if s 0 = 1 then 1 else 0) ≤ 1 := by split_ifs <;> omega
      rw [natOfF2, pow_succ']
      omega

private lemma natOfF2_testBit :
    ∀ {k : ℕ} (s : 𝔽₂ k) (i : Fin k), (natOfF2 s).testBit i.val = decide (s i = 1)
  | 0, _, i => Fin.elim0 i
  | k + 1, s, i => by
      refine Fin.cases ?_ (fun j => ?_) i
      · simp only [natOfF2, Fin.val_zero, Nat.testBit_zero]
        split_ifs with h <;> simp [h]
      · simp only [natOfF2, Fin.val_succ, Nat.testBit_add_one]
        have ih := natOfF2_testBit (fun t => s t.succ) j
        have h0 : (if s 0 = 1 then 1 else 0) < 2 := by split_ifs <;> omega
        have hdiv : ((if s 0 = 1 then 1 else 0) + 2 * natOfF2 (fun t => s t.succ)) / 2 =
            natOfF2 (fun t => s t.succ) := by omega
        rw [hdiv, ih]

private lemma natOfF2_pos :
    ∀ {k : ℕ} (s : 𝔽₂ k), s ≠ 0 → 0 < natOfF2 s
  | 0, s, hs => by
      exfalso
      apply hs
      ext i
      exact Fin.elim0 i
  | k + 1, s, hs => by
      by_cases h0 : s 0 = 1
      · simp [natOfF2, h0]
      · have hs' : (fun i : Fin k => s i.succ) ≠ 0 := by
          intro heq
          apply hs
          ext i
          refine Fin.cases ?_ (fun j => ?_) i
          · have : ∀ a : ZMod 2, a ≠ 1 → a = 0 := by decide
            exact this (s 0) h0
          · exact congrFun heq j
        have ih := natOfF2_pos (fun i => s i.succ) hs'
        rw [natOfF2]
        omega

private def hammingLabel (k : ℕ) (j : Fin (2 ^ k - 1)) : 𝔽₂ k :=
  fun i => if (j.val + 1).testBit i.val then 1 else 0

private lemma hammingLabel_surj (k : ℕ) (s : 𝔽₂ k) (hs : s ≠ 0) :
    ∃ j : Fin (2 ^ k - 1), hammingLabel k j = s := by
  have hpos : 0 < natOfF2 s := natOfF2_pos s hs
  have hlt : natOfF2 s < 2 ^ k := natOfF2_lt s
  refine ⟨⟨natOfF2 s - 1, by omega⟩, ?_⟩
  ext i
  simp only [hammingLabel]
  have hadd : natOfF2 s - 1 + 1 = natOfF2 s := by omega
  rw [hadd, natOfF2_testBit]
  have hdec : ∀ a : ZMod 2, (if decide (a = 1) = true then (1 : ZMod 2) else 0) = a := by
    decide
  exact hdec (s i)

private def hammingStat (k : ℕ) (w : 𝔽₂ (2 ^ k - 1)) : 𝔽₂ k :=
  ∑ j : Fin (2 ^ k - 1), w j • hammingLabel k j

private lemma hammingStat_add (k : ℕ) (w₁ w₂ : 𝔽₂ (2 ^ k - 1)) :
    hammingStat k (w₁ + w₂) = hammingStat k w₁ + hammingStat k w₂ := by
  simp only [hammingStat, Pi.add_apply, add_smul, Finset.sum_add_distrib]

private lemma hammingStat_zero (k : ℕ) : hammingStat k 0 = 0 := by
  simp [hammingStat]

private lemma hammingStat_single (k : ℕ) (j : Fin (2 ^ k - 1)) :
    hammingStat k (Pi.single j (1 : ZMod 2)) = hammingLabel k j := by
  unfold hammingStat
  rw [Finset.sum_eq_single j]
  · rw [Pi.single_eq_same, one_smul]
  · intro t _ ht
    rw [Pi.single_eq_of_ne ht, zero_smul]
  · intro h
    exact absurd (Finset.mem_univ j) h

private lemma hammingStat_surj (k : ℕ) : Function.Surjective (hammingStat k) := by
  intro s
  by_cases hs : s = 0
  · subst hs
    exact ⟨0, hammingStat_zero k⟩
  · obtain ⟨j, hj⟩ := hammingLabel_surj k s hs
    exact ⟨Pi.single j 1, by rw [hammingStat_single, hj]⟩

private def hammingCode (k : ℕ) : Finset (𝔽₂ (2 ^ k - 1)) :=
  Finset.univ.filter (fun w => hammingStat k w = 0)

private lemma hammingNorm_single_le_one {m : ℕ} (j : Fin m) :
    hammingNorm (Pi.single j (1 : ZMod 2) : 𝔽₂ m) ≤ 1 := by
  unfold hammingNorm
  calc
    #{i : Fin m | (Pi.single j (1 : ZMod 2) : 𝔽₂ m) i ≠ 0}
        ≤ #({j} : Finset (Fin m)) := by
          refine Finset.card_le_card (fun i hi => ?_)
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
          simp only [Finset.mem_singleton]
          by_contra hij
          rw [Pi.single_eq_of_ne hij] at hi
          exact hi rfl
    _ = 1 := Finset.card_singleton j

private lemma zmod2_add_self {n : ℕ} (x : 𝔽₂ n) : x + x = 0 := by
  ext i
  have h : ∀ a : ZMod 2, a + a = 0 := by decide
  exact h (x i)

private lemma hammingCode_covering (k : ℕ) :
    IsCoveringFinset (2 ^ k - 1) 1 (hammingCode k) := by
  unfold IsCoveringFinset
  ext y
  simp only [Finset.mem_univ, iff_true, Finset.mem_add]
  by_cases hy : hammingStat k y = 0
  · refine ⟨y, ?_, 0, ?_, add_zero y⟩
    · simp [hammingCode, hy]
    · simp [hammingBallFinset, hammingNorm_zero]
  · obtain ⟨j, hj⟩ := hammingLabel_surj k (hammingStat k y) hy
    let e : 𝔽₂ (2 ^ k - 1) := Pi.single j (1 : ZMod 2)
    refine ⟨y + e, ?_, e, ?_, ?_⟩
    · simp only [hammingCode, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hammingStat_add, hammingStat_single, hj, zmod2_add_self]
    · simp only [hammingBallFinset, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hammingNorm_single_le_one j
    · rw [add_assoc, zmod2_add_self, add_zero]

private lemma hammingCode_card (k : ℕ) :
    (hammingCode k).card * 2 ^ k = 2 ^ (2 ^ k - 1) := by
  have hfiber : ∀ s : 𝔽₂ k,
      (Finset.univ.filter (fun y : 𝔽₂ (2 ^ k - 1) => hammingStat k y = s)).card =
        (hammingCode k).card := by
    intro s
    obtain ⟨xs, hxs⟩ := hammingStat_surj k s
    refine Finset.card_bij (fun y _ => y + xs) ?_ ?_ ?_
    · intro y hy
      simp only [hammingCode, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
      rw [hammingStat_add, hy, hxs, zmod2_add_self]
    · intro y₁ _ y₂ _ h
      have := congrArg (· + xs) h
      simpa [add_assoc, zmod2_add_self] using this
    · intro w hw
      simp only [hammingCode, Finset.mem_filter, Finset.mem_univ, true_and] at hw
      refine ⟨w + xs, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [hammingStat_add, hw, hxs, zero_add]
      · rw [add_assoc, zmod2_add_self, add_zero]
  have hsum : Fintype.card (𝔽₂ (2 ^ k - 1)) =
      ∑ s : 𝔽₂ k, (Finset.univ.filter (fun y : 𝔽₂ (2 ^ k - 1) => hammingStat k y = s)).card := by
    rw [← Finset.card_univ]
    exact Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)
  simp_rw [hfiber, Finset.sum_const, Finset.card_univ, smul_eq_mul] at hsum
  have hcard1 : Fintype.card (𝔽₂ (2 ^ k - 1)) = 2 ^ (2 ^ k - 1) := by
    rw [Fintype.card_fun, ZMod.card, Fintype.card_fin]
  have hcard2 : Fintype.card (𝔽₂ k) = 2 ^ k := by
    rw [Fintype.card_fun, ZMod.card, Fintype.card_fin]
  rw [hcard1, hcard2, mul_comm] at hsum
  exact hsum.symm

private lemma ball_card_le (N R : ℕ) :
    Nat.card (hammingBall N R) ≤ ∑ i ∈ Finset.range (R + 1), N.choose i := by
  classical
  let U := (Finset.univ : Finset (Fin N))
  let S := (Finset.range (R + 1)).biUnion (fun i => U.powersetCard i)
  let supp (x : hammingBall N R) : Finset (Fin N) := U.filter (fun i => x.val i ≠ 0)
  have hs (x : hammingBall N R) : supp x ∈ S := by
    have hcard : (supp x).card ≤ R := x.property
    refine Finset.mem_biUnion.mpr ⟨(supp x).card, Finset.mem_range.mpr (by omega), ?_⟩
    exact Finset.mem_powersetCard.mpr ⟨Finset.filter_subset _ _, rfl⟩
  let F (x : hammingBall N R) : ↥S := ⟨supp x, hs x⟩
  have hinj : Function.Injective F := by
    intro x y h
    apply Subtype.ext
    funext i
    have he : supp x = supp y := congrArg Subtype.val h
    have hm : i ∈ supp x ↔ i ∈ supp y := he ▸ Iff.rfl
    have hb : x.val i ≠ 0 ↔ y.val i ≠ 0 := by simpa [supp, U] using hm
    exact (by decide : ∀ a b : ZMod 2, (a ≠ 0 ↔ b ≠ 0) → a = b) _ _ hb
  have hcount := Nat.card_le_card_of_injective F hinj
  calc
    Nat.card (hammingBall N R) ≤ S.card := by
      simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using hcount
    _ ≤ ∑ i ∈ Finset.range (R + 1), (U.powersetCard i).card := Finset.card_biUnion_le
    _ = ∑ i ∈ Finset.range (R + 1), N.choose i := by
      simp [U, Finset.card_powersetCard]

private lemma choose_le_ball_card (n r : ℕ) :
    n.choose r ≤ Nat.card (hammingBall n r) := by
  classical
  let U := (Finset.univ : Finset (Fin n))
  let P := U.powersetCard r
  let vec (T : ↥P) : 𝔽₂ n := fun i => if i ∈ T.val then 1 else 0
  have hvec (T : ↥P) : vec T ∈ hammingBall n r := by
    change hammingNorm (vec T) ≤ r
    unfold hammingNorm
    have hsub : U.filter (fun i => vec T i ≠ 0) = T.val := by
      ext i
      simp [vec, U]
    rw [hsub]
    exact (Finset.mem_powersetCard.mp T.property).2.le
  let G (T : ↥P) : hammingBall n r := ⟨vec T, hvec T⟩
  have hinj : Function.Injective G := by
    intro T₁ T₂ h
    apply Subtype.ext
    ext i
    have hi := congrFun (congrArg Subtype.val h) i
    simp only [G, vec] at hi
    by_cases h1 : i ∈ T₁.val <;> by_cases h2 : i ∈ T₂.val <;> simp_all
  have hcount := Nat.card_le_card_of_injective G hinj
  simpa only [Nat.card_eq_fintype_card, Fintype.card_coe, P, U, Finset.card_powersetCard,
    Finset.card_univ, Fintype.card_fin] using hcount

private lemma sum_choose_le (N r : ℕ) (hN : 102 * (r + 1) ≤ N) :
    100 * (∑ i ∈ Finset.range (r + 2), N.choose i) ≤ 101 * N.choose (r + 1) := by
  have hstep : ∀ i ≤ r, 101 * N.choose i ≤ N.choose (i + 1) := by
    intro i hi
    have h1 : N.choose (i + 1) * (i + 1) = N.choose i * (N - i) :=
      Nat.choose_succ_right_eq N i
    have h2 : 101 * (i + 1) ≤ N - i := by omega
    have h3 : 101 * N.choose i * (i + 1) ≤ N.choose (i + 1) * (i + 1) := by
      rw [h1]
      calc
        101 * N.choose i * (i + 1) = N.choose i * (101 * (i + 1)) := by ring
        _ ≤ N.choose i * (N - i) := Nat.mul_le_mul_left _ h2
    exact Nat.le_of_mul_le_mul_right h3 (Nat.succ_pos i)
  have haux : ∀ t ≤ r + 1,
      100 * (∑ i ∈ Finset.range (t + 1), N.choose i) ≤ 101 * N.choose t := by
    intro t ht
    induction t with
    | zero => simp
    | succ t ih =>
      rw [Finset.sum_range_succ]
      have iht := ih (by omega)
      have hs := hstep t (by omega)
      omega
  exact haux (r + 1) le_rfl

private lemma choose_prod_bound (n m r : ℕ) (hr : 0 < r)
    (hlow : n < 2 * r * (m + 1)) (hhigh : r * (m + 1) ≤ n) (hn : r < n) :
    101 * (n + m).choose (r + 1) ≤ 600 * n.choose r * (m + 1) := by
  have hr_pos : (0 : ℝ) < r := by exact_mod_cast hr
  have hrm : r * m ≤ n - r := by
    have : r * (m + 1) = r * m + r := by ring
    omega
  have hprod_le :
      (∏ j ∈ Finset.range r, ((n + m - j : ℕ) : ℝ)) ≤
        (∏ j ∈ Finset.range r, ((n - j : ℕ) : ℝ)) * (1 + 1 / (r : ℝ)) ^ r := by
    have hpow : (1 + 1 / (r : ℝ)) ^ r = ∏ _j ∈ Finset.range r, (1 + 1 / (r : ℝ)) := by
      simp [Finset.prod_const, Finset.card_range]
    rw [hpow, ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod (fun j _ => by positivity) (fun j hj => ?_)
    rw [Finset.mem_range] at hj
    have hnj : j ≤ n := by omega
    have hnj_pos : (0 : ℝ) < ((n - j : ℕ) : ℝ) := by
      have : 0 < n - j := by omega
      exact_mod_cast this
    have hmr : (r : ℝ) * (m : ℝ) ≤ ((n - r : ℕ) : ℝ) := by
      exact_mod_cast hrm
    have hmr_j : (m : ℝ) / ((n - j : ℕ) : ℝ) ≤ 1 / (r : ℝ) := by
      rw [div_le_div_iff₀ hnj_pos hr_pos]
      have hnr_le : ((n - r : ℕ) : ℝ) ≤ ((n - j : ℕ) : ℝ) := by
        exact_mod_cast (show n - r ≤ n - j by omega)
      nlinarith
    have hcast_nmj : ((n + m - j : ℕ) : ℝ) = ((n - j : ℕ) : ℝ) + (m : ℝ) := by
      have : n + m - j = (n - j) + m := by omega
      rw [this, Nat.cast_add]
    rw [hcast_nmj]
    calc
      ((n - j : ℕ) : ℝ) + (m : ℝ)
          = ((n - j : ℕ) : ℝ) * (1 + (m : ℝ) / ((n - j : ℕ) : ℝ)) := by
            field_simp [hnj_pos.ne']
      _ ≤ ((n - j : ℕ) : ℝ) * (1 + 1 / (r : ℝ)) := by
            gcongr
  have hexp : (1 + 1 / (r : ℝ)) ^ r ≤ (2.7182818286 : ℝ) := by
    have h1 : 1 + 1 / (r : ℝ) ≤ Real.exp (1 / (r : ℝ)) := by
      linarith [Real.add_one_le_exp (1 / (r : ℝ))]
    have h2 : (1 + 1 / (r : ℝ)) ^ r ≤ (Real.exp (1 / (r : ℝ))) ^ r :=
      pow_le_pow_left₀ (by positivity) h1 r
    have h3 : (Real.exp (1 / (r : ℝ))) ^ r = Real.exp 1 := by
      rw [← Real.exp_nat_mul]
      congr 1
      field_simp [hr_pos.ne']
    linarith [Real.exp_one_lt_d9]
  have hdesc_N :
      ((n + m).descFactorial (r + 1) : ℝ) =
        ((n + m - r : ℕ) : ℝ) * ∏ j ∈ Finset.range r, ((n + m - j : ℕ) : ℝ) := by
    rw [Nat.descFactorial_succ, Nat.descFactorial_eq_prod_range, Nat.cast_mul]
    simp only [Nat.cast_prod]
  have hdesc_n : (n.descFactorial r : ℝ) = ∏ j ∈ Finset.range r, ((n - j : ℕ) : ℝ) := by
    rw [Nat.descFactorial_eq_prod_range]
    simp only [Nat.cast_prod]
  have hN_sub_r : ((n + m - r : ℕ) : ℝ) ≤ (2 * (r : ℝ) + 1) * ((m : ℝ) + 1) := by
    have hexp_mul : (2 * r + 1) * (m + 1) = 2 * r * (m + 1) + m + 1 := by ring
    have hnat : n + m - r ≤ (2 * r + 1) * (m + 1) := by omega
    exact_mod_cast hnat
  have hchoose_N : ((r + 1).factorial : ℝ) * ((n + m).choose (r + 1) : ℝ) =
      ((n + m).descFactorial (r + 1) : ℝ) := by
    exact_mod_cast (Nat.descFactorial_eq_factorial_mul_choose (n + m) (r + 1)).symm
  have hchoose_n : (r.factorial : ℝ) * (n.choose r : ℝ) = (n.descFactorial r : ℝ) := by
    exact_mod_cast (Nat.descFactorial_eq_factorial_mul_choose n r).symm
  have hfact_succ : ((r + 1).factorial : ℝ) = ((r : ℝ) + 1) * (r.factorial : ℝ) := by
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hr_fac_pos : (0 : ℝ) < (r.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos r
  have hr1_pos : (0 : ℝ) < (r : ℝ) + 1 := by linarith
  have hcalc : ((r + 1).factorial : ℝ) * ((n + m).choose (r + 1) : ℝ) ≤
      (2 * (r : ℝ) + 1) * ((m : ℝ) + 1) * ((n.descFactorial r : ℝ) * 2.7182818286) := by
    rw [hchoose_N, hdesc_N]
    have hpr := le_trans hprod_le
      (mul_le_mul_of_nonneg_left hexp (Finset.prod_nonneg (fun _ _ => by positivity)))
    rw [← hdesc_n] at hpr
    exact mul_le_mul hN_sub_r hpr (by positivity) (by positivity)
  rw [← hchoose_n, hfact_succ] at hcalc
  have hden_pos : (0 : ℝ) < ((r : ℝ) + 1) * (r.factorial : ℝ) := mul_pos hr1_pos hr_fac_pos
  have hmain : ((n + m).choose (r + 1) : ℝ) ≤
      (2 * (r : ℝ) + 1) / ((r : ℝ) + 1) * 2.7182818286 * (n.choose r : ℝ) * ((m : ℝ) + 1) := by
    have hdiv : ((n + m).choose (r + 1) : ℝ) ≤
        ((2 * (r : ℝ) + 1) * ((m : ℝ) + 1) * ((r.factorial : ℝ) * (n.choose r : ℝ) * 2.7182818286)) /
          (((r : ℝ) + 1) * (r.factorial : ℝ)) := by
      rw [le_div_iff₀ hden_pos]
      linarith
    have heq :
        ((2 * (r : ℝ) + 1) * ((m : ℝ) + 1) * ((r.factorial : ℝ) * (n.choose r : ℝ) * 2.7182818286)) /
          (((r : ℝ) + 1) * (r.factorial : ℝ)) =
        (2 * (r : ℝ) + 1) / ((r : ℝ) + 1) * 2.7182818286 * (n.choose r : ℝ) * ((m : ℝ) + 1) := by
      field_simp [hr_fac_pos.ne', hr1_pos.ne']
    linarith
  have hratio : (2 * (r : ℝ) + 1) / ((r : ℝ) + 1) ≤ 2 := by
    rw [div_le_iff₀ hr1_pos]
    linarith
  have hreal : (101 : ℝ) * ((n + m).choose (r + 1) : ℝ) ≤
      600 * (n.choose r : ℝ) * ((m : ℝ) + 1) := by
    have h1 : (101 : ℝ) * ((n + m).choose (r + 1) : ℝ) ≤
        101 * (2 * 2.7182818286 * (n.choose r : ℝ) * ((m : ℝ) + 1)) := by
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
      refine le_trans hmain ?_
      gcongr
    have h2 : (101 : ℝ) * (2 * 2.7182818286) ≤ 600 := by norm_num
    have hnn : 0 ≤ (n.choose r : ℝ) * ((m : ℝ) + 1) := by positivity
    nlinarith
  exact_mod_cast hreal

private lemma ball_ratio_bound (n m r : ℕ) (hr : 0 < r)
    (hlow : n < 2 * r * (m + 1)) (hhigh : r * (m + 1) ≤ n) (hn : 102 * (r + 1) ≤ n) :
    Nat.card (hammingBall (n + m) (r + 1)) ≤ 6 * Nat.card (hammingBall n r) * (m + 1) := by
  have h1 := ball_card_le (n + m) (r + 1)
  have h2 := sum_choose_le (n + m) r (by omega)
  have h3 := choose_prod_bound n m r hr hlow hhigh (by omega)
  have h4 := choose_le_ball_card n r
  have h5 : 100 * ∑ i ∈ Finset.range (r + 2), (n + m).choose i ≤
      100 * (6 * n.choose r * (m + 1)) := by
    have : 600 * n.choose r * (m + 1) = 100 * (6 * n.choose r * (m + 1)) := by ring
    linarith
  have h6 : ∑ i ∈ Finset.range (r + 2), (n + m).choose i ≤ 6 * n.choose r * (m + 1) :=
    Nat.le_of_mul_le_mul_left h5 (by norm_num)
  calc
    Nat.card (hammingBall (n + m) (r + 1))
        ≤ ∑ i ∈ Finset.range (r + 2), (n + m).choose i := h1
    _ ≤ 6 * n.choose r * (m + 1) := h6
    _ ≤ 6 * Nat.card (hammingBall n r) * (m + 1) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 6 h4)

private lemma exists_pow_two_between (r n : ℕ) (hr : 0 < r) (hn : 2 * r ≤ n) :
    ∃ k : ℕ, 1 ≤ k ∧ r * 2 ^ k ≤ n ∧ n < 2 * r * 2 ^ k := by
  let k := Nat.findGreatest (fun t => r * 2 ^ t ≤ n) n
  have hk_le : r * 2 ^ k ≤ n :=
    Nat.findGreatest_spec (P := fun t => r * 2 ^ t ≤ n) (Nat.zero_le n) (by simp; omega)
  have hk1 : 1 ≤ k := by
    apply Nat.le_findGreatest
    · omega
    · rw [pow_one, mul_comm]; exact hn
  have hkn : k < n := by
    by_contra h
    have hnk : n ≤ k := by omega
    have hpow : n < r * 2 ^ k := by
      have hlt : n < 2 ^ n := Nat.lt_two_pow_self
      have hle1 : 2 ^ n ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hnk
      have hle2 : 2 ^ k ≤ r * 2 ^ k := Nat.le_mul_of_pos_left _ hr
      omega
    omega
  have hk_succ : ¬ (r * 2 ^ (k + 1) ≤ n) :=
    Nat.findGreatest_is_greatest (P := fun t => r * 2 ^ t ≤ n) (show k < k + 1 by omega) (by omega)
  refine ⟨k, hk1, hk_le, ?_⟩
  rw [pow_succ'] at hk_succ
  have hmul : r * (2 * 2 ^ k) = 2 * r * 2 ^ k := by ring
  rw [hmul] at hk_succ
  omega

end OMA.Green40R1H2

section Solution

open Green40 Filter Topology Finset OMA.Green40R1H2
open scoped ENNReal Pointwise

theorem OMA.solution : OMA.R_Green40_green_40_variants_arbitrary_subsets_R1.H2 := by
  intro r hr
  refine le_of_forall_gt_imp_ge_of_dense fun d hd => ?_
  let C : ℝ≥0∞ := d / 6
  have h60 : (6 : ℝ≥0∞) ≠ 0 := by norm_num
  have h6top : (6 : ℝ≥0∞) ≠ ⊤ := by norm_num
  have hf_lt : f_tilde r < C :=
    (ENNReal.lt_div_iff_mul_lt (Or.inl h60) (Or.inl h6top)).mpr (by simpa [mul_comm] using hd)
  have h6C : 6 * C = d := by
    by_cases hd_top : d = ⊤
    · subst hd_top
      simp only [C]
      rw [ENNReal.top_div_of_ne_top h6top, ENNReal.mul_top h60]
    · simp only [C]
      exact ENNReal.mul_div_cancel' (fun h => absurd h h60) (fun h => absurd h h6top)
  rw [← h6C]
  unfold f_tilde
  refine Filter.liminf_le_of_frequently_le' ?_
  have hfreq : ∃ᶠ n in atTop, minDensityFinset n r < C :=
    Filter.frequently_lt_of_liminf_lt (hu := by isBoundedDefault) hf_lt
  rw [Filter.frequently_atTop] at hfreq ⊢
  intro B
  obtain ⟨n, hn_ge, hn_lt⟩ := hfreq (max B (102 * (r + 1)))
  have hnB : B ≤ n := le_trans (le_max_left _ _) hn_ge
  have hn102 : 102 * (r + 1) ≤ n := le_trans (le_max_right _ _) hn_ge
  unfold minDensityFinset at hn_lt
  rw [iInf_lt_iff] at hn_lt
  obtain ⟨V, hV⟩ := hn_lt
  rw [iInf_lt_iff] at hV
  obtain ⟨hVcov, hVdens⟩ := hV
  obtain ⟨k, hk1, hk_high, hk_low⟩ :=
    exists_pow_two_between r n hr (by omega)
  let m := 2 ^ k - 1
  have hm1 : m + 1 = 2 ^ k := by
    have : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by norm_num)
    omega
  have hlow' : n < 2 * r * (m + 1) := by rwa [hm1]
  have hhigh' : r * (m + 1) ≤ n := by rwa [hm1]
  let emb : 𝔽₂ n × 𝔽₂ m ↪ 𝔽₂ (n + m) := ⟨fun p => Fin.append p.1 p.2, fin_append_inj⟩
  let W : Finset (𝔽₂ (n + m)) := (V ×ˢ hammingCode k).map emb
  have hWcov : IsCoveringFinset (n + m) (r + 1) W := by
    unfold IsCoveringFinset
    ext z
    simp only [Finset.mem_univ, iff_true, Finset.mem_add]
    let x : 𝔽₂ n := fun i => z (Fin.castAdd m i)
    let y : 𝔽₂ m := fun j => z (Fin.natAdd n j)
    have hz_eq : Fin.append x y = z := by
      ext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simp [x, Fin.append_left]
      · simp [y, Fin.append_right]
    have hx : x ∈ V + hammingBallFinset n r := by
      rw [hVcov]
      exact Finset.mem_univ x
    have hy : y ∈ hammingCode k + hammingBallFinset m 1 := by
      rw [hammingCode_covering k]
      exact Finset.mem_univ y
    obtain ⟨v, hv, dx, hdx, hvdx⟩ := Finset.mem_add.mp hx
    obtain ⟨h, hh, dy, hdy, hhdy⟩ := Finset.mem_add.mp hy
    refine ⟨Fin.append v h, ?_, Fin.append dx dy, ?_, ?_⟩
    · exact Finset.mem_map.mpr ⟨(v, h), Finset.mem_product.mpr ⟨hv, hh⟩, rfl⟩
    · simp only [hammingBallFinset, Finset.mem_filter, Finset.mem_univ, true_and] at hdx hdy ⊢
      rw [hammingNorm_append]
      exact Nat.add_le_add hdx hdy
    · rw [← fin_append_add, hvdx, hhdy, hz_eq]
  have hWcard : W.card = V.card * (hammingCode k).card := by
    rw [Finset.card_map, Finset.card_product]
  have hball := ball_ratio_bound n m r hr hlow' hhigh' hn102
  have hHcard : (hammingCode k).card * 2 ^ k = 2 ^ m := hammingCode_card k
  refine ⟨n + m, by omega, ?_⟩
  refine le_trans (iInf₂_le W hWcov) ?_
  rw [hWcard]
  have h2m0 : ((2 ^ m : ℕ) : ℝ≥0∞) ≠ 0 := by positivity
  have h2mtop : ((2 ^ m : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hnum_le :
      ((V.card * (hammingCode k).card : ℕ) : ℝ≥0∞) *
          (Nat.card (hammingBall (n + m) (r + 1)) : ℝ≥0∞) ≤
        6 * ((V.card : ℝ≥0∞) * (Nat.card (hammingBall n r) : ℝ≥0∞)) * ((2 ^ m : ℕ) : ℝ≥0∞) := by
    have hnat :
        V.card * (hammingCode k).card * Nat.card (hammingBall (n + m) (r + 1)) ≤
          6 * (V.card * Nat.card (hammingBall n r)) * 2 ^ m := by
      calc
        V.card * (hammingCode k).card * Nat.card (hammingBall (n + m) (r + 1))
            ≤ V.card * (hammingCode k).card * (6 * Nat.card (hammingBall n r) * (m + 1)) :=
              Nat.mul_le_mul_left _ hball
        _ = 6 * (V.card * Nat.card (hammingBall n r)) * ((hammingCode k).card * 2 ^ k) := by
              rw [hm1]; ring
        _ = 6 * (V.card * Nat.card (hammingBall n r)) * 2 ^ m := by
              rw [hHcard]
    exact_mod_cast hnat
  have hden_eq : (2 ^ (n + m) : ℝ≥0∞) = (2 ^ n : ℝ≥0∞) * ((2 ^ m : ℕ) : ℝ≥0∞) := by
    rw [pow_add]
    norm_cast
  calc
    ((V.card * (hammingCode k).card : ℕ) : ℝ≥0∞) *
        (Nat.card (hammingBall (n + m) (r + 1)) : ℝ≥0∞) / (2 ^ (n + m) : ℝ≥0∞)
        ≤ (6 * ((V.card : ℝ≥0∞) * (Nat.card (hammingBall n r) : ℝ≥0∞)) * ((2 ^ m : ℕ) : ℝ≥0∞)) /
            ((2 ^ n : ℝ≥0∞) * ((2 ^ m : ℕ) : ℝ≥0∞)) := by
          rw [hden_eq]
          exact ENNReal.div_le_div_right hnum_le _
    _ = 6 * ((V.card : ℝ≥0∞) * (Nat.card (hammingBall n r) : ℝ≥0∞)) / (2 ^ n : ℝ≥0∞) :=
          ENNReal.mul_div_mul_right _ _ h2m0 h2mtop
    _ = 6 * ((V.card : ℝ≥0∞) * (Nat.card (hammingBall n r) : ℝ≥0∞) / (2 ^ n : ℝ≥0∞)) := by
          rw [mul_div_assoc]
    _ ≤ 6 * C := by gcongr

end Solution
