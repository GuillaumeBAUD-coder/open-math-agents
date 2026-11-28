import OMAStatements.S_mo_373858

-- Condition number bounds for the factorially scaled Hilbert matrix (MathOverflow 373858).
-- Credit: @EmadY

open Finset

noncomputable section

private def legCoeff (k i : ℕ) : ℝ :=
  (-1 : ℝ) ^ (k - i) * (k.choose i : ℝ) * ((k + i).choose i : ℝ)

private lemma legCoeff_eq_zero_of_lt {k i : ℕ} (h : k < i) : legCoeff k i = 0 := by
  simp [legCoeff, Nat.choose_eq_zero_of_lt h]

private lemma legCoeff_diag (k : ℕ) : legCoeff k k = ((2 * k).choose k : ℝ) := by
  simp [legCoeff, two_mul]

private lemma hilb_prod_sub_eq_factorial (s : ℕ) :
    ∏ r ∈ range s, ((s : ℝ) - r) = (s.factorial : ℝ) := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [prod_range_succ', Nat.factorial_succ]
    have h : ∀ r : ℕ, (((s + 1 : ℕ) : ℝ) - ((r + 1 : ℕ) : ℝ)) = (s : ℝ) - r := fun r => by
      push_cast; ring
    simp_rw [h, ih]
    push_cast; ring

private lemma hilb_prod_add_succ_eq (a n : ℕ) :
    (a.factorial : ℝ) * ∏ r ∈ range n, ((a : ℝ) + r + 1) = ((a + n).factorial : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [prod_range_succ, ← mul_assoc, ih, ← add_assoc, Nat.factorial_succ]
    push_cast; ring

private lemma hilb_prod_erase_sub (k s : ℕ) (hs : s ≤ k) :
    ∏ r ∈ (range (k + 1)).erase s, ((r : ℝ) - s) =
      (-1 : ℝ) ^ s * (s.factorial : ℝ) * ((k - s).factorial : ℝ) := by
  have hsplit : (range (k + 1)).erase s = range s ∪ Ico (s + 1) (k + 1) := by
    ext r
    simp only [mem_erase, mem_range, mem_union, mem_Ico]
    omega
  have hdisj : Disjoint (range s) (Ico (s + 1) (k + 1)) := by
    rw [disjoint_left]
    intro r hr1 hr2
    rw [mem_range] at hr1; rw [mem_Ico] at hr2; omega
  rw [hsplit, prod_union hdisj]
  have hp1 : ∏ r ∈ range s, ((r : ℝ) - s) = (-1 : ℝ) ^ s * (s.factorial : ℝ) := by
    have hneg : ∀ r : ℕ, ((r : ℝ) - s) = -((s : ℝ) - r) := fun r => by ring
    simp_rw [hneg, prod_neg, card_range, hilb_prod_sub_eq_factorial]
  have hp2 : ∏ r ∈ Ico (s + 1) (k + 1), ((r : ℝ) - s) = ((k - s).factorial : ℝ) := by
    rw [prod_Ico_eq_prod_range]
    have hsub : k + 1 - (s + 1) = k - s := by omega
    have hterm : ∀ r : ℕ, (((s + 1 + r : ℕ) : ℝ) - s) = ((0 : ℕ) : ℝ) + r + 1 := fun r => by
      push_cast; ring
    rw [hsub]
    simp_rw [hterm]
    simpa using hilb_prod_add_succ_eq 0 (k - s)
  rw [hp1, hp2]

private lemma hilb_leg_hilbert_sum (k j : ℕ) :
    ∑ i ∈ range (k + 1), legCoeff k i / ((i : ℝ) + j + 1) =
      (∏ r ∈ range k, ((j : ℝ) - r)) / (∏ r ∈ range (k + 1), ((j : ℝ) + r + 1)) := by
  let A : Polynomial ℝ :=
    ∑ i ∈ range (k + 1), Polynomial.C (legCoeff k i) *
      ∏ r ∈ (range (k + 1)).erase i, (Polynomial.X + Polynomial.C ((r : ℝ) + 1))
  let B : Polynomial ℝ :=
    ∏ r ∈ range k, (Polynomial.X - Polynomial.C (r : ℝ))
  have hdegA : A.natDegree ≤ k := by
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun i hi => ?_
    refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
    refine (Polynomial.natDegree_prod_le _ _).trans ?_
    have h1 : ∑ r ∈ (range (k + 1)).erase i,
        (Polynomial.X + Polynomial.C ((r : ℝ) + 1)).natDegree =
        ∑ _r ∈ (range (k + 1)).erase i, 1 :=
      sum_congr rfl fun r _ => Polynomial.natDegree_X_add_C _
    rw [h1, sum_const, smul_eq_mul, card_erase_of_mem hi, card_range]
    omega
  have hdegB : B.natDegree ≤ k := by
    refine (Polynomial.natDegree_prod_le _ _).trans ?_
    have h1 : ∑ r ∈ range k, (Polynomial.X - Polynomial.C (r : ℝ)).natDegree =
        ∑ _r ∈ range k, 1 :=
      sum_congr rfl fun r _ => Polynomial.natDegree_X_sub_C _
    rw [h1, sum_const, smul_eq_mul, card_range]
    omega
  have hinj : Function.Injective (fun s : Fin (k + 1) => -((s.1 : ℝ) + 1)) := by
    intro s₁ s₂ h
    ext
    have h' : (s₁.1 : ℝ) = (s₂.1 : ℝ) := by linarith
    exact_mod_cast h'
  have hAB : A = B := by
    refine Polynomial.eq_of_natDegree_lt_card_of_eval_eq A B hinj (fun s => ?_) ?_
    · have hs : s.1 ≤ k := by omega
      have hevalA : Polynomial.eval (-((s.1 : ℝ) + 1)) A =
          legCoeff k s.1 * ((-1 : ℝ) ^ s.1 * (s.1.factorial : ℝ) * ((k - s.1).factorial : ℝ)) := by
        simp only [A, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
          Polynomial.eval_prod, Polynomial.eval_add, Polynomial.eval_X]
        rw [sum_eq_single s.1]
        · have hsub : ∀ r : ℕ, -((s.1 : ℝ) + 1) + ((r : ℝ) + 1) = (r : ℝ) - s.1 := fun r => by ring
          simp_rw [hsub]
          rw [hilb_prod_erase_sub k s.1 hs]
        · intro i _ his
          have hmem : s.1 ∈ (range (k + 1)).erase i :=
            mem_erase.mpr ⟨his.symm, mem_range.mpr s.2⟩
          rw [prod_eq_zero hmem (by ring), mul_zero]
        · intro hns
          exact False.elim (hns (mem_range.mpr s.2))
      have hevalB : (s.1.factorial : ℝ) * Polynomial.eval (-((s.1 : ℝ) + 1)) B =
          (-1 : ℝ) ^ k * ((k + s.1).factorial : ℝ) := by
        simp only [B, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X,
          Polynomial.eval_C]
        have hneg : ∀ r : ℕ, -((s.1 : ℝ) + 1) - (r : ℝ) = -((s.1 : ℝ) + r + 1) := fun r => by ring
        simp_rw [hneg, prod_neg, card_range]
        calc (s.1.factorial : ℝ) * ((-1 : ℝ) ^ k * ∏ r ∈ range k, ((s.1 : ℝ) + r + 1))
            = (-1 : ℝ) ^ k * ((s.1.factorial : ℝ) * ∏ r ∈ range k, ((s.1 : ℝ) + r + 1)) := by ring
          _ = (-1 : ℝ) ^ k * ((s.1 + k).factorial : ℝ) := by rw [hilb_prod_add_succ_eq]
          _ = (-1 : ℝ) ^ k * ((k + s.1).factorial : ℝ) := by rw [add_comm s.1 k]
      have hsf : (s.1.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
      apply mul_left_cancel₀ hsf
      rw [hevalA, hevalB]
      have hc1 : (k.choose s.1 : ℝ) * (s.1.factorial : ℝ) * ((k - s.1).factorial : ℝ) =
          (k.factorial : ℝ) := by
        exact_mod_cast Nat.choose_mul_factorial_mul_factorial hs
      have hc2 : ((k + s.1).choose s.1 : ℝ) * (s.1.factorial : ℝ) * (k.factorial : ℝ) =
          ((k + s.1).factorial : ℝ) := by
        have h := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_left s.1 k)
        rw [Nat.add_sub_cancel_right] at h
        exact_mod_cast h
      have hpow : (-1 : ℝ) ^ (k - s.1) * (-1 : ℝ) ^ s.1 = (-1 : ℝ) ^ k := by
        rw [← pow_add, Nat.sub_add_cancel hs]
      calc (s.1.factorial : ℝ) *
            (legCoeff k s.1 * ((-1 : ℝ) ^ s.1 * (s.1.factorial : ℝ) * ((k - s.1).factorial : ℝ)))
          = ((-1 : ℝ) ^ (k - s.1) * (-1 : ℝ) ^ s.1) *
              ((k + s.1).choose s.1 : ℝ) * (s.1.factorial : ℝ) *
              ((k.choose s.1 : ℝ) * (s.1.factorial : ℝ) * ((k - s.1).factorial : ℝ)) := by
            unfold legCoeff; ring
        _ = (-1 : ℝ) ^ k *
              (((k + s.1).choose s.1 : ℝ) * (s.1.factorial : ℝ) * (k.factorial : ℝ)) := by
            rw [hpow, hc1]; ring
        _ = (-1 : ℝ) ^ k * ((k + s.1).factorial : ℝ) := by rw [hc2]
    · rw [Fintype.card_fin]
      omega
  let P : ℝ := ∏ r ∈ range (k + 1), ((j : ℝ) + r + 1)
  have hP : P ≠ 0 := ne_of_gt (prod_pos fun r _ => by positivity)
  have hevalj := congr_arg (Polynomial.eval (j : ℝ)) hAB
  simp only [A, B, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_prod, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_X] at hevalj
  rw [show ∏ r ∈ range (k + 1), ((j : ℝ) + r + 1) = P from rfl, eq_div_iff hP, sum_mul]
  refine (sum_congr rfl fun i hi => ?_).trans hevalj
  have hij : (i : ℝ) + j + 1 ≠ 0 := by positivity
  have herase : ((j : ℝ) + ((i : ℝ) + 1)) *
      ∏ r ∈ (range (k + 1)).erase i, ((j : ℝ) + ((r : ℝ) + 1)) = P := by
    have hcomm : ∀ r : ℕ, (j : ℝ) + ((r : ℝ) + 1) = (j : ℝ) + r + 1 := fun r => by ring
    simp_rw [hcomm]
    exact mul_prod_erase (range (k + 1)) (fun r : ℕ => (j : ℝ) + r + 1) hi
  calc legCoeff k i / ((i : ℝ) + j + 1) * P
      = legCoeff k i / ((i : ℝ) + j + 1) *
          (((i : ℝ) + j + 1) * ∏ r ∈ (range (k + 1)).erase i, ((j : ℝ) + ((r : ℝ) + 1))) := by
        rw [← herase]; ring
    _ = legCoeff k i * ∏ r ∈ (range (k + 1)).erase i, ((j : ℝ) + ((r : ℝ) + 1)) := by
        rw [← mul_assoc, div_mul_cancel₀ _ hij]

private lemma hilb_leg_inner_of_le {k₁ k₂ : ℕ} (h : k₂ ≤ k₁) :
    ∑ i ∈ range (k₁ + 1), ∑ j ∈ range (k₂ + 1),
      legCoeff k₁ i * legCoeff k₂ j / ((i : ℝ) + j + 1) =
        if k₁ = k₂ then 1 / (2 * (k₁ : ℝ) + 1) else 0 := by
  rw [sum_comm]
  have hinner : ∀ j : ℕ,
      ∑ i ∈ range (k₁ + 1), legCoeff k₁ i * legCoeff k₂ j / ((i : ℝ) + j + 1) =
        legCoeff k₂ j * ((∏ r ∈ range k₁, ((j : ℝ) - r)) /
          (∏ r ∈ range (k₁ + 1), ((j : ℝ) + r + 1))) := fun j => by
    have hrew : ∀ i : ℕ, legCoeff k₁ i * legCoeff k₂ j / ((i : ℝ) + j + 1) =
        legCoeff k₂ j * (legCoeff k₁ i / ((i : ℝ) + j + 1)) := fun i => by ring
    simp_rw [hrew, ← mul_sum, hilb_leg_hilbert_sum]
  simp_rw [hinner]
  have hzero_lt : ∀ j < k₁, ∏ r ∈ range k₁, ((j : ℝ) - r) = 0 := fun j hj =>
    prod_eq_zero (mem_range.mpr hj) (sub_self _)
  rcases h.lt_or_eq with hlt | rfl
  · rw [if_neg (by omega)]
    refine sum_eq_zero fun j hj => ?_
    rw [mem_range] at hj
    rw [hzero_lt j (by omega), zero_div, mul_zero]
  · rw [if_pos rfl, sum_range_succ]
    have hsum0 : ∑ j ∈ range k₂,
        legCoeff k₂ j * ((∏ r ∈ range k₂, ((j : ℝ) - r)) /
          (∏ r ∈ range (k₂ + 1), ((j : ℝ) + r + 1))) = 0 :=
      sum_eq_zero fun j hj => by
        rw [hzero_lt j (mem_range.mp hj), zero_div, mul_zero]
    rw [hsum0, zero_add, legCoeff_diag, hilb_prod_sub_eq_factorial]
    let P : ℝ := ∏ r ∈ range (k₂ + 1), ((k₂ : ℝ) + r + 1)
    have hP : P ≠ 0 := ne_of_gt (prod_pos fun r _ => by positivity)
    have h2k : (2 * (k₂ : ℝ) + 1) ≠ 0 := by positivity
    have hkf : (k₂.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    rw [show ∏ r ∈ range (k₂ + 1), ((k₂ : ℝ) + r + 1) = P from rfl]
    rw [← mul_div_assoc, div_eq_div_iff hP h2k]
    apply mul_left_cancel₀ hkf
    have hPfact : (k₂.factorial : ℝ) * P = ((2 * k₂ + 1).factorial : ℝ) := by
      have hp := hilb_prod_add_succ_eq k₂ (k₂ + 1)
      have hadd : k₂ + (k₂ + 1) = 2 * k₂ + 1 := by omega
      rwa [hadd] at hp
    have hc : ((2 * k₂).choose k₂ : ℝ) * (k₂.factorial : ℝ) * (k₂.factorial : ℝ) =
        ((2 * k₂).factorial : ℝ) := by
      have h1 := Nat.choose_mul_factorial_mul_factorial (by omega : k₂ ≤ 2 * k₂)
      have h2 : 2 * k₂ - k₂ = k₂ := by omega
      rw [h2] at h1
      exact_mod_cast h1
    calc (k₂.factorial : ℝ) * (((2 * k₂).choose k₂ : ℝ) * (k₂.factorial : ℝ) * (2 * (k₂ : ℝ) + 1))
        = (((2 * k₂).choose k₂ : ℝ) * (k₂.factorial : ℝ) * (k₂.factorial : ℝ)) *
            (2 * (k₂ : ℝ) + 1) := by ring
      _ = ((2 * k₂).factorial : ℝ) * (2 * (k₂ : ℝ) + 1) := by rw [hc]
      _ = ((2 * k₂ + 1).factorial : ℝ) := by rw [Nat.factorial_succ]; push_cast; ring
      _ = (k₂.factorial : ℝ) * (1 * P) := by rw [one_mul, hPfact]

private lemma hilb_leg_inner (k₁ k₂ : ℕ) :
    ∑ i ∈ range (k₁ + 1), ∑ j ∈ range (k₂ + 1),
      legCoeff k₁ i * legCoeff k₂ j / ((i : ℝ) + j + 1) =
        if k₁ = k₂ then 1 / (2 * (k₁ : ℝ) + 1) else 0 := by
  rcases le_total k₂ k₁ with h | h
  · exact hilb_leg_inner_of_le h
  · rcases h.eq_or_lt with rfl | hlt
    · exact hilb_leg_inner_of_le le_rfl
    · rw [sum_comm]
      have hsymm : ∀ j i : ℕ,
          legCoeff k₁ i * legCoeff k₂ j / ((i : ℝ) + j + 1) =
            legCoeff k₂ j * legCoeff k₁ i / ((j : ℝ) + i + 1) := fun j i => by ring
      simp_rw [hsymm]
      rw [hilb_leg_inner_of_le hlt.le, if_neg (by omega), if_neg (by omega)]

private lemma hilb_energy_legendre (m : ℕ) (c : ℕ → ℝ) :
    OMA.S_mo_373858.energy m (fun i => (i.factorial : ℝ) * ∑ k ∈ Ico i (m + 1), legCoeff k i * c k) =
      ∑ k ∈ range (m + 1), c k ^ 2 / (2 * (k : ℝ) + 1) := by
  unfold OMA.S_mo_373858.energy
  have hfac : ∀ i : ℕ,
      ((i.factorial : ℝ) * ∑ k ∈ Ico i (m + 1), legCoeff k i * c k) / (i.factorial : ℝ) =
        ∑ k ∈ range (m + 1), legCoeff k i * c k := fun i => by
    rw [mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero i))]
    refine sum_subset (fun k hk => mem_range.mpr (mem_Ico.mp hk).2) fun k hk hni => ?_
    rw [mem_range] at hk; rw [mem_Ico] at hni
    rw [legCoeff_eq_zero_of_lt (by omega), zero_mul]
  have hswap :
      ∑ i ∈ range (m + 1), ∑ j ∈ range (m + 1),
        ((∑ k₁ ∈ range (m + 1), legCoeff k₁ i * c k₁) *
          (∑ k₂ ∈ range (m + 1), legCoeff k₂ j * c k₂)) / ((i : ℝ) + j + 1) =
      ∑ k₁ ∈ range (m + 1), ∑ k₂ ∈ range (m + 1),
        c k₁ * c k₂ * (∑ i ∈ range (m + 1), ∑ j ∈ range (m + 1),
          legCoeff k₁ i * legCoeff k₂ j / ((i : ℝ) + j + 1)) := by
    calc ∑ i ∈ range (m + 1), ∑ j ∈ range (m + 1),
          ((∑ k₁ ∈ range (m + 1), legCoeff k₁ i * c k₁) *
            (∑ k₂ ∈ range (m + 1), legCoeff k₂ j * c k₂)) / ((i : ℝ) + j + 1)
        = ∑ i ∈ range (m + 1), ∑ j ∈ range (m + 1),
            ∑ k₁ ∈ range (m + 1), ∑ k₂ ∈ range (m + 1),
              c k₁ * c k₂ * (legCoeff k₁ i * legCoeff k₂ j / ((i : ℝ) + j + 1)) := by
          refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
          rw [sum_mul, sum_div]
          refine sum_congr rfl fun k₁ _ => ?_
          rw [mul_sum, sum_div]
          exact sum_congr rfl fun k₂ _ => by ring
      _ = ∑ i ∈ range (m + 1), ∑ k₁ ∈ range (m + 1),
            ∑ j ∈ range (m + 1), ∑ k₂ ∈ range (m + 1),
              c k₁ * c k₂ * (legCoeff k₁ i * legCoeff k₂ j / ((i : ℝ) + j + 1)) :=
          sum_congr rfl fun i _ => sum_comm
      _ = ∑ k₁ ∈ range (m + 1), ∑ i ∈ range (m + 1),
            ∑ k₂ ∈ range (m + 1), ∑ j ∈ range (m + 1),
              c k₁ * c k₂ * (legCoeff k₁ i * legCoeff k₂ j / ((i : ℝ) + j + 1)) := by
          rw [sum_comm]
          exact sum_congr rfl fun k₁ _ => sum_congr rfl fun i _ => sum_comm
      _ = ∑ k₁ ∈ range (m + 1), ∑ k₂ ∈ range (m + 1),
            c k₁ * c k₂ * (∑ i ∈ range (m + 1), ∑ j ∈ range (m + 1),
              legCoeff k₁ i * legCoeff k₂ j / ((i : ℝ) + j + 1)) := by
          refine sum_congr rfl fun k₁ _ => ?_
          rw [sum_comm]
          refine sum_congr rfl fun k₂ _ => ?_
          simp_rw [← mul_sum]
  simp_rw [hfac]
  rw [hswap]
  refine sum_congr rfl fun k₁ hk₁ => ?_
  have hsub : ∀ k₂ ∈ range (m + 1),
      ∑ i ∈ range (m + 1), ∑ j ∈ range (m + 1),
        legCoeff k₁ i * legCoeff k₂ j / ((i : ℝ) + j + 1) =
      if k₁ = k₂ then 1 / (2 * (k₁ : ℝ) + 1) else 0 := by
    intro k₂ hk₂
    rw [mem_range] at hk₁ hk₂
    have hi_trim : ∀ i,
        ∑ j ∈ range (m + 1), legCoeff k₁ i * legCoeff k₂ j / ((i : ℝ) + j + 1) =
        ∑ j ∈ range (k₂ + 1), legCoeff k₁ i * legCoeff k₂ j / ((i : ℝ) + j + 1) := fun i =>
      (sum_subset (fun j hj => mem_range.mpr (by rw [mem_range] at hj; omega)) fun j _ hnj => by
        rw [mem_range] at hnj
        rw [legCoeff_eq_zero_of_lt (by omega : k₂ < j), mul_zero, zero_div]).symm
    simp_rw [hi_trim]
    refine (sum_subset (fun i hi => mem_range.mpr (by rw [mem_range] at hi; omega))
      fun i _ hni => ?_).symm.trans (hilb_leg_inner k₁ k₂)
    rw [mem_range] at hni
    refine sum_eq_zero fun j _ => ?_
    rw [legCoeff_eq_zero_of_lt (by omega : k₁ < i), zero_mul, zero_div]
  rw [sum_congr rfl fun k₂ hk₂ => by rw [hsub k₂ hk₂]]
  rw [sum_eq_single k₁]
  · rw [if_pos rfl]; ring
  · intro k₂ _ hne
    rw [if_neg hne.symm, mul_zero]
  · intro hnk₁
    exact False.elim (hnk₁ hk₁)

private lemma hilb_exists_legendre (m : ℕ) (x : ℕ → ℝ) :
    ∃ c : ℕ → ℝ, ∀ i ≤ m,
      x i = (i.factorial : ℝ) * ∑ k ∈ Ico i (m + 1), legCoeff k i * c k := by
  induction m generalizing x with
  | zero =>
    refine ⟨fun _ => x 0, fun i hi => ?_⟩
    obtain rfl : i = 0 := by omega
    simp [legCoeff]
  | succ m ih =>
    let c_top : ℝ := x (m + 1) / (((m + 1).factorial : ℝ) * legCoeff (m + 1) (m + 1))
    obtain ⟨c', hc'⟩ := ih (fun i => x i - (i.factorial : ℝ) * (legCoeff (m + 1) i * c_top))
    refine ⟨fun k => if k = m + 1 then c_top else c' k, fun i hi => ?_⟩
    rcases hi.eq_or_lt with rfl | hlt
    · have hIco : Ico (m + 1) (m + 1 + 1) = {m + 1} := Nat.Ico_succ_singleton (m + 1)
      have hpos : ((m + 1).factorial : ℝ) * legCoeff (m + 1) (m + 1) ≠ 0 := by
        rw [legCoeff_diag]
        have hch : 0 < (2 * (m + 1)).choose (m + 1) := Nat.choose_pos (by omega)
        have hchR : (0 : ℝ) < ((2 * (m + 1)).choose (m + 1) : ℝ) := by exact_mod_cast hch
        positivity
      rw [hIco, sum_singleton]
      dsimp only
      rw [if_pos rfl, ← mul_assoc, mul_div_cancel₀ _ hpos]
    · have him : i ≤ m := by omega
      rw [sum_Ico_succ_top (by omega : i ≤ m + 1)]
      dsimp only
      rw [if_pos rfl]
      have hcongr : ∑ k ∈ Ico i (m + 1), legCoeff k i * (if k = m + 1 then c_top else c' k) =
          ∑ k ∈ Ico i (m + 1), legCoeff k i * c' k :=
        sum_congr rfl fun k hk => by
          rw [if_neg (by rw [mem_Ico] at hk; omega)]
      rw [hcongr, mul_add, ← hc' i him]
      ring

private lemma energy_congr (m : ℕ) (x x' : ℕ → ℝ) (h : ∀ i ≤ m, x i = x' i) :
    OMA.S_mo_373858.energy m x = OMA.S_mo_373858.energy m x' := by
  unfold OMA.S_mo_373858.energy
  refine sum_congr rfl fun i hi => sum_congr rfl fun j hj => ?_
  rw [h i (Nat.lt_succ_iff.mp (mem_range.mp hi)),
    h j (Nat.lt_succ_iff.mp (mem_range.mp hj))]

private lemma hilb_energy_pos (m : ℕ) (x : ℕ → ℝ) (hx : 0 < OMA.S_mo_373858.lengthSq m x) :
    0 < OMA.S_mo_373858.energy m x := by
  obtain ⟨c, hc⟩ := hilb_exists_legendre m x
  rw [energy_congr m x _ hc, hilb_energy_legendre]
  have hnonneg : 0 ≤ ∑ k ∈ range (m + 1), c k ^ 2 / (2 * (k : ℝ) + 1) :=
    sum_nonneg fun k _ => by positivity
  rcases hnonneg.lt_or_eq with hpos | hzero
  · exact hpos
  · exfalso
    have hck : ∀ k ∈ range (m + 1), c k = 0 := by
      have hall := (sum_eq_zero_iff_of_nonneg (fun k _ => by positivity)).mp hzero.symm
      intro k hk
      have hk0 := hall k hk
      have hdenom : (2 * (k : ℝ) + 1) ≠ 0 := by positivity
      have hsq : c k ^ 2 = 0 := (div_eq_zero_iff.mp hk0).resolve_right hdenom
      exact sq_eq_zero_iff.mp hsq
    have hlen0 : OMA.S_mo_373858.lengthSq m x = 0 := by
      unfold OMA.S_mo_373858.lengthSq
      refine sum_eq_zero fun i hi => ?_
      rw [mem_range] at hi
      have hxi : x i = 0 := by
        rw [hc i (by omega)]
        suffices ∑ k ∈ Ico i (m + 1), legCoeff k i * c k = 0 by rw [this, mul_zero]
        refine sum_eq_zero fun k hk => ?_
        rw [hck k (mem_range.mpr (mem_Ico.mp hk).2), mul_zero]
      rw [hxi, sq, zero_mul]
    linarith

private def ANat (k i : ℕ) : ℕ :=
  i.factorial * k.choose i * (k + i).choose i

private lemma anat_step (k i : ℕ) (hi : i < k) : 2 * ANat k i ≤ ANat k (i + 1) := by
  have h1 : k.choose (i + 1) * (i + 1) = k.choose i * (k - i) := Nat.choose_succ_right_eq k i
  have h2 : (k + i + 1).choose (i + 1) * (i + 1) = (k + i + 1) * (k + i).choose i := by
    have ha := Nat.add_choose_mul_factorial_mul_factorial k (i + 1)
    have hb := Nat.add_choose_mul_factorial_mul_factorial k i
    rw [← Nat.add_assoc, Nat.factorial_succ i, Nat.factorial_succ (k + i), ← hb] at ha
    exact Nat.eq_of_mul_eq_mul_right (Nat.mul_pos (Nat.factorial_pos k) (Nat.factorial_pos i)) (by
      calc ((k + i + 1).choose (i + 1) * (i + 1)) * (k.factorial * i.factorial)
          = (k + i + 1).choose (i + 1) * k.factorial * ((i + 1) * i.factorial) := by ring
        _ = (k + i + 1) * ((k + i).choose i * k.factorial * i.factorial) := ha
        _ = ((k + i + 1) * (k + i).choose i) * (k.factorial * i.factorial) := by ring)
  have hid : (i + 1) * ANat k (i + 1) = (k - i) * (k + i + 1) * ANat k i := by
    calc (i + 1) * ANat k (i + 1)
        = i.factorial * (k.choose (i + 1) * (i + 1)) * ((k + i + 1).choose (i + 1) * (i + 1)) := by
          unfold ANat; rw [Nat.factorial_succ, ← Nat.add_assoc]; ring
      _ = i.factorial * (k.choose i * (k - i)) * ((k + i + 1) * (k + i).choose i) := by rw [h1, h2]
      _ = (k - i) * (k + i + 1) * ANat k i := by unfold ANat; ring
  have hle : 2 * (i + 1) ≤ (k - i) * (k + i + 1) := by
    calc 2 * (i + 1) = 1 * (2 * (i + 1)) := (one_mul _).symm
      _ ≤ (k - i) * (k + i + 1) := Nat.mul_le_mul (by omega) (by omega)
  exact Nat.le_of_mul_le_mul_left (by
    calc (i + 1) * (2 * ANat k i) = 2 * (i + 1) * ANat k i := by ring
      _ ≤ (k - i) * (k + i + 1) * ANat k i := Nat.mul_le_mul_right _ hle
      _ = (i + 1) * ANat k (i + 1) := hid.symm) (Nat.succ_pos i)

private lemma anat_diag_mul (k : ℕ) : ANat k k * k.factorial = (2 * k).factorial := by
  have h := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_left k k)
  rw [Nat.add_sub_cancel, ← two_mul] at h
  unfold ANat
  rw [Nat.choose_self, ← two_mul]
  linarith

private lemma anat_diag_cast (k : ℕ) :
    (ANat k k : ℝ) = ((2 * k).factorial : ℝ) / (k.factorial : ℝ) := by
  have h : (ANat k k : ℝ) * (k.factorial : ℝ) = ((2 * k).factorial : ℝ) := by
    exact_mod_cast anat_diag_mul k
  exact eq_div_of_mul_eq (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)) h

private lemma anat_diag_step (k : ℕ) : 2 * ANat k k ≤ ANat (k + 1) (k + 1) := by
  have h : ANat (k + 1) (k + 1) * (k + 1).factorial =
      (2 * (2 * k + 1) * ANat k k) * (k + 1).factorial := by
    rw [anat_diag_mul (k + 1)]
    have h2 : 2 * (k + 1) = 2 * k + 2 := by ring
    rw [h2, Nat.factorial_succ (2 * k + 1), Nat.factorial_succ (2 * k), ← anat_diag_mul k,
      Nat.factorial_succ k]
    ring
  have heq := Nat.eq_of_mul_eq_mul_right (Nat.factorial_pos (k + 1)) h
  rw [heq]
  calc 2 * ANat k k = 2 * 1 * ANat k k := by ring
    _ ≤ 2 * (2 * k + 1) * ANat k k :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 (by omega))

private lemma sum_le_two_mul_last (f : ℕ → ℝ) (hf0 : 0 ≤ f 0) (k : ℕ)
    (hstep : ∀ i < k, 2 * f i ≤ f (i + 1)) :
    ∑ i ∈ range (k + 1), f i ≤ 2 * f k := by
  induction k with
  | zero => simp; linarith
  | succ k ih =>
    rw [sum_range_succ]
    linarith [ih (fun i hi => hstep i (Nat.lt_succ_of_lt hi)), hstep k (Nat.lt_succ_self k)]

private lemma sum_range_sum_Ico (n : ℕ) (F : ℕ → ℕ → ℝ) :
    ∑ i ∈ range n, ∑ k ∈ Ico i n, F k i =
      ∑ k ∈ range n, ∑ i ∈ range (k + 1), F k i := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc ∑ i ∈ range (n + 1), ∑ k ∈ Ico i (n + 1), F k i
        = (∑ i ∈ range n, ∑ k ∈ Ico i (n + 1), F k i) +
            ∑ k ∈ Ico n (n + 1), F k n := sum_range_succ _ n
      _ = ((∑ i ∈ range n, ∑ k ∈ Ico i n, F k i) +
            ∑ i ∈ range n, F n i) + F n n := by
          rw [sum_Ico_succ_top le_rfl, Ico_self, sum_empty, zero_add, ← sum_add_distrib]
          congr 1
          exact sum_congr rfl fun i hi =>
            sum_Ico_succ_top (Nat.le_of_lt (mem_range.mp hi)) (fun k => F k i)
      _ = (∑ k ∈ range n, ∑ i ∈ range (k + 1), F k i) +
            ∑ i ∈ range (n + 1), F n i := by
          rw [ih, add_assoc, ← sum_range_succ (fun i => F n i) n]
      _ = ∑ k ∈ range (n + 1), ∑ i ∈ range (k + 1), F k i :=
          (sum_range_succ (fun k => ∑ i ∈ range (k + 1), F k i) n).symm

private lemma energy_le_three_lengthSq (m : ℕ) (x : ℕ → ℝ) :
    OMA.S_mo_373858.energy m x ≤ 3 * OMA.S_mo_373858.lengthSq m x := by
  have h1 : OMA.S_mo_373858.energy m x ≤
      (∑ i ∈ range (m + 1), |x i| / (i.factorial : ℝ)) ^ 2 := by
    rw [sq, sum_mul]
    unfold OMA.S_mo_373858.energy
    refine sum_le_sum fun i _ => ?_
    rw [mul_sum]
    refine sum_le_sum fun j _ => ?_
    have hd : (1 : ℝ) ≤ (i : ℝ) + j + 1 := by
      linarith [Nat.cast_nonneg (α := ℝ) i, Nat.cast_nonneg (α := ℝ) j]
    have hd_abs : |(i : ℝ) + j + 1| = (i : ℝ) + j + 1 := abs_of_pos (by linarith)
    have hfi : (0 : ℝ) < i.factorial := Nat.cast_pos.mpr (Nat.factorial_pos i)
    have hfj : (0 : ℝ) < j.factorial := Nat.cast_pos.mpr (Nat.factorial_pos j)
    calc ((x i / i.factorial) * (x j / j.factorial)) / ((i : ℝ) + j + 1)
        ≤ |((x i / i.factorial) * (x j / j.factorial)) / ((i : ℝ) + j + 1)| := le_abs_self _
      _ = |(x i / i.factorial) * (x j / j.factorial)| / ((i : ℝ) + j + 1) := by
          rw [abs_div, hd_abs]
      _ ≤ |(x i / i.factorial) * (x j / j.factorial)| := div_le_self (abs_nonneg _) hd
      _ = (|x i| / i.factorial) * (|x j| / j.factorial) := by
          rw [abs_mul, abs_div, abs_div, abs_of_pos hfi, abs_of_pos hfj]
  have hcs : (∑ i ∈ range (m + 1), |x i| / (i.factorial : ℝ)) ^ 2 ≤
      OMA.S_mo_373858.lengthSq m x * ∑ i ∈ range (m + 1), (1 / (i.factorial : ℝ)) ^ 2 := by
    have h := sum_mul_sq_le_sq_mul_sq (range (m + 1))
      (fun i => |x i|) (fun i => 1 / (i.factorial : ℝ))
    have ha : ∑ i ∈ range (m + 1), |x i| * (1 / (i.factorial : ℝ)) =
        ∑ i ∈ range (m + 1), |x i| / (i.factorial : ℝ) :=
      sum_congr rfl fun i _ => mul_one_div _ _
    have hb : ∑ i ∈ range (m + 1), |x i| ^ 2 = OMA.S_mo_373858.lengthSq m x :=
      sum_congr rfl fun i _ => sq_abs _
    rwa [ha, hb] at h
  have hfac : ∀ k : ℕ, 2 ^ k ≤ (k + 1).factorial := by
    intro k; induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', Nat.factorial_succ]
      exact Nat.mul_le_mul (by omega) ih
  have hgeom : ∀ n : ℕ, ∑ k ∈ range n, (1 / 2 : ℝ) ^ k = 2 - 2 * (1 / 2 : ℝ) ^ n := by
    intro n; induction n with
    | zero => norm_num
    | succ n ih => rw [sum_range_succ, ih]; ring
  have hsum : ∑ i ∈ range (m + 1), (1 / (i.factorial : ℝ)) ^ 2 ≤ 3 := by
    rw [sum_range_succ']
    have hle : ∑ k ∈ range m, (1 / ((k + 1).factorial : ℝ)) ^ 2 ≤
        ∑ k ∈ range m, (1 / 2 : ℝ) ^ k := by
      refine sum_le_sum fun k _ => ?_
      rw [one_div_pow, one_div_pow]
      have h2pos : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
      have hk1 : (1 : ℝ) ≤ ((k + 1).factorial : ℝ) := by
        exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos (k + 1))
      have hk2 : (2 : ℝ) ^ k ≤ ((k + 1).factorial : ℝ) := by exact_mod_cast hfac k
      have hsq : (2 : ℝ) ^ k ≤ ((k + 1).factorial : ℝ) ^ 2 := by nlinarith
      exact one_div_le_one_div_of_le h2pos hsq
    have hg : (0 : ℝ) ≤ 2 * (1 / 2 : ℝ) ^ m := by positivity
    simp only [Nat.factorial_zero, Nat.cast_one, div_self one_ne_zero, one_pow]
    linarith [hgeom m]
  have hlen_nn : 0 ≤ OMA.S_mo_373858.lengthSq m x :=
    sum_nonneg fun i _ => sq_nonneg (x i)
  nlinarith

private lemma hilb_cond_bounds (m : ℕ) :
    OMA.S_mo_373858.scale m ≤ OMA.S_mo_373858.cond₂ m ∧
      OMA.S_mo_373858.cond₂ m ≤ 12 * OMA.S_mo_373858.scale m := by
  have h_len_ub : ∀ y : ℕ → ℝ,
      OMA.S_mo_373858.lengthSq m y ≤ 4 * OMA.S_mo_373858.scale m * OMA.S_mo_373858.energy m y := by
    intro y
    obtain ⟨c, hc⟩ := hilb_exists_legendre m y
    have hey : OMA.S_mo_373858.energy m y =
        ∑ k ∈ range (m + 1), c k ^ 2 / (2 * (k : ℝ) + 1) := by
      rw [energy_congr m y _ hc, hilb_energy_legendre m c]
    have hey_nn : 0 ≤ OMA.S_mo_373858.energy m y := by
      rw [hey]; exact sum_nonneg fun k _ => by positivity
    have hyi : ∀ i ∈ range (m + 1), y i ^ 2 ≤ OMA.S_mo_373858.energy m y *
        ∑ k ∈ Ico i (m + 1), (2 * (k : ℝ) + 1) * (ANat k i : ℝ) ^ 2 := by
      intro i hi
      have him : i ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hi)
      have hy_eq : y i = ∑ k ∈ Ico i (m + 1),
          (c k / Real.sqrt (2 * (k : ℝ) + 1)) *
            (Real.sqrt (2 * (k : ℝ) + 1) * ((i.factorial : ℝ) * legCoeff k i)) := by
        rw [hc i him, mul_sum]
        refine sum_congr rfl fun k _ => ?_
        have hs : Real.sqrt (2 * (k : ℝ) + 1) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
        field_simp [hs]
      have hcs := sum_mul_sq_le_sq_mul_sq (Ico i (m + 1))
        (fun k => c k / Real.sqrt (2 * (k : ℝ) + 1))
        (fun k => Real.sqrt (2 * (k : ℝ) + 1) * ((i.factorial : ℝ) * legCoeff k i))
      rw [← hy_eq] at hcs
      have hs1 : (∑ k ∈ Ico i (m + 1), (c k / Real.sqrt (2 * (k : ℝ) + 1)) ^ 2) ≤
          OMA.S_mo_373858.energy m y := by
        have hrew : ∑ k ∈ Ico i (m + 1), (c k / Real.sqrt (2 * (k : ℝ) + 1)) ^ 2 =
            ∑ k ∈ Ico i (m + 1), c k ^ 2 / (2 * (k : ℝ) + 1) := by
          refine sum_congr rfl fun k _ => ?_
          rw [div_pow, Real.sq_sqrt (by positivity)]
        rw [hrew, hey]
        exact sum_le_sum_of_subset_of_nonneg
          (fun k hk => mem_range.mpr (mem_Ico.mp hk).2)
          (fun k _ _ => by positivity)
      have hs2 : ∑ k ∈ Ico i (m + 1),
          (Real.sqrt (2 * (k : ℝ) + 1) * ((i.factorial : ℝ) * legCoeff k i)) ^ 2 =
          ∑ k ∈ Ico i (m + 1), (2 * (k : ℝ) + 1) * (ANat k i : ℝ) ^ 2 := by
        refine sum_congr rfl fun k _ => ?_
        rw [mul_pow, Real.sq_sqrt (by positivity)]
        congr 1
        unfold legCoeff ANat
        have hneg : ((-1 : ℝ) ^ (k - i)) ^ 2 = 1 := by
          rw [← pow_mul, mul_comm, pow_mul]; norm_num
        push_cast
        linear_combination ((i.factorial : ℝ) * (k.choose i : ℝ) * ((k + i).choose i : ℝ)) ^ 2 * hneg
      rw [hs2] at hcs
      have hb_nn : 0 ≤ ∑ k ∈ Ico i (m + 1), (2 * (k : ℝ) + 1) * (ANat k i : ℝ) ^ 2 :=
        sum_nonneg fun k _ => by positivity
      exact hcs.trans (mul_le_mul_of_nonneg_right hs1 hb_nn)
    have hsum1 : OMA.S_mo_373858.lengthSq m y ≤ OMA.S_mo_373858.energy m y *
        ∑ k ∈ range (m + 1), (2 * (k : ℝ) + 1) * ∑ i ∈ range (k + 1), (ANat k i : ℝ) ^ 2 := by
      calc OMA.S_mo_373858.lengthSq m y
          ≤ ∑ i ∈ range (m + 1), OMA.S_mo_373858.energy m y *
              ∑ k ∈ Ico i (m + 1), (2 * (k : ℝ) + 1) * (ANat k i : ℝ) ^ 2 :=
            sum_le_sum hyi
        _ = OMA.S_mo_373858.energy m y *
            ∑ i ∈ range (m + 1), ∑ k ∈ Ico i (m + 1), (2 * (k : ℝ) + 1) * (ANat k i : ℝ) ^ 2 := by
            rw [← mul_sum]
        _ = OMA.S_mo_373858.energy m y *
            ∑ k ∈ range (m + 1), ∑ i ∈ range (k + 1), (2 * (k : ℝ) + 1) * (ANat k i : ℝ) ^ 2 := by
            rw [sum_range_sum_Ico (m + 1) (fun k i => (2 * (k : ℝ) + 1) * (ANat k i : ℝ) ^ 2)]
        _ = OMA.S_mo_373858.energy m y *
            ∑ k ∈ range (m + 1), (2 * (k : ℝ) + 1) * ∑ i ∈ range (k + 1), (ANat k i : ℝ) ^ 2 := by
            congr 1; refine sum_congr rfl fun k _ => (mul_sum _ _ _).symm
    have h_inner : ∀ k : ℕ, ∑ i ∈ range (k + 1), (ANat k i : ℝ) ^ 2 ≤ 2 * (ANat k k : ℝ) ^ 2 := by
      intro k
      refine sum_le_two_mul_last (fun i => (ANat k i : ℝ) ^ 2) (sq_nonneg _) k fun i hi => ?_
      have hst : 2 * (ANat k i : ℝ) ≤ (ANat k (i + 1) : ℝ) := by exact_mod_cast anat_step k i hi
      have hnn : (0 : ℝ) ≤ ANat k i := Nat.cast_nonneg _
      nlinarith
    have h_outer : ∑ k ∈ range (m + 1), (2 * (k : ℝ) + 1) * (ANat k k : ℝ) ^ 2 ≤
        2 * OMA.S_mo_373858.scale m := by
      have hm_eq : (2 * (m : ℝ) + 1) * (ANat m m : ℝ) ^ 2 = OMA.S_mo_373858.scale m := by
        rw [anat_diag_cast]; rfl
      rw [← hm_eq]
      refine sum_le_two_mul_last (fun k => (2 * (k : ℝ) + 1) * (ANat k k : ℝ) ^ 2)
        (by positivity) m fun k _ => ?_
      have hst : 2 * (ANat k k : ℝ) ≤ (ANat (k + 1) (k + 1) : ℝ) := by
        exact_mod_cast anat_diag_step k
      have hnn : (0 : ℝ) ≤ ANat k k := Nat.cast_nonneg _
      have hsq : 2 * (ANat k k : ℝ) ^ 2 ≤ (ANat (k + 1) (k + 1) : ℝ) ^ 2 := by nlinarith
      have hk1 : 0 ≤ 2 * (k : ℝ) + 1 := by positivity
      have hk2 : 2 * (k : ℝ) + 1 ≤ 2 * ((k + 1 : ℕ) : ℝ) + 1 := by push_cast; linarith
      nlinarith
    have h_tot : ∑ k ∈ range (m + 1),
        (2 * (k : ℝ) + 1) * ∑ i ∈ range (k + 1), (ANat k i : ℝ) ^ 2 ≤
        4 * OMA.S_mo_373858.scale m := by
      have hle : ∑ k ∈ range (m + 1),
          (2 * (k : ℝ) + 1) * ∑ i ∈ range (k + 1), (ANat k i : ℝ) ^ 2 ≤
          2 * ∑ k ∈ range (m + 1), (2 * (k : ℝ) + 1) * (ANat k k : ℝ) ^ 2 := by
        rw [mul_sum]
        refine sum_le_sum fun k _ => ?_
        have hk : 0 ≤ 2 * (k : ℝ) + 1 := by positivity
        linarith [mul_le_mul_of_nonneg_left (h_inner k) hk]
      linarith
    calc OMA.S_mo_373858.lengthSq m y
        ≤ OMA.S_mo_373858.energy m y *
            ∑ k ∈ range (m + 1), (2 * (k : ℝ) + 1) * ∑ i ∈ range (k + 1), (ANat k i : ℝ) ^ 2 := hsum1
      _ ≤ OMA.S_mo_373858.energy m y * (4 * OMA.S_mo_373858.scale m) :=
          mul_le_mul_of_nonneg_left h_tot hey_nn
      _ = 4 * OMA.S_mo_373858.scale m * OMA.S_mo_373858.energy m y := mul_comm _ _
  set S : Set ℝ := {r | ∃ x y : ℕ → ℝ, 0 < OMA.S_mo_373858.lengthSq m x ∧
    0 < OMA.S_mo_373858.lengthSq m y ∧
    r = (OMA.S_mo_373858.energy m x * OMA.S_mo_373858.lengthSq m y) /
      (OMA.S_mo_373858.lengthSq m x * OMA.S_mo_373858.energy m y)}
  have hS_ub : ∀ r ∈ S, r ≤ 12 * OMA.S_mo_373858.scale m := by
    rintro r ⟨x, y, hx, hy, rfl⟩
    have hey_pos : 0 < OMA.S_mo_373858.energy m y := hilb_energy_pos m y hy
    have h1 := energy_le_three_lengthSq m x
    have h2 := h_len_ub y
    rw [div_le_iff₀ (mul_pos hx hey_pos)]
    calc OMA.S_mo_373858.energy m x * OMA.S_mo_373858.lengthSq m y
        ≤ (3 * OMA.S_mo_373858.lengthSq m x) * (4 * OMA.S_mo_373858.scale m * OMA.S_mo_373858.energy m y) :=
          mul_le_mul h1 h2 (le_of_lt hy) (by linarith)
      _ = 12 * OMA.S_mo_373858.scale m * (OMA.S_mo_373858.lengthSq m x * OMA.S_mo_373858.energy m y) := by ring
  let x₀ : ℕ → ℝ := fun i => if i = 0 then 1 else 0
  let c₀ : ℕ → ℝ := fun k => if k = m then 1 else 0
  let y₀ : ℕ → ℝ := fun i => (i.factorial : ℝ) * ∑ k ∈ Ico i (m + 1), legCoeff k i * c₀ k
  have hx₀_len : OMA.S_mo_373858.lengthSq m x₀ = 1 := by
    unfold OMA.S_mo_373858.lengthSq
    rw [sum_eq_single 0]
    · simp [x₀]
    · intro i _ hi; simp [x₀, hi]
    · intro h0; exact absurd (mem_range.mpr (Nat.succ_pos m)) h0
  have hx₀_en : OMA.S_mo_373858.energy m x₀ = 1 := by
    unfold OMA.S_mo_373858.energy
    rw [sum_eq_single 0]
    · rw [sum_eq_single 0]
      · simp [x₀]
      · intro j _ hj; simp [x₀, hj]
      · intro h0; exact absurd (mem_range.mpr (Nat.succ_pos m)) h0
    · intro i _ hi
      exact sum_eq_zero fun j _ => by simp [x₀, hi]
    · intro h0; exact absurd (mem_range.mpr (Nat.succ_pos m)) h0
  have hy₀_en : OMA.S_mo_373858.energy m y₀ = 1 / (2 * (m : ℝ) + 1) := by
    rw [hilb_energy_legendre m c₀, sum_eq_single m]
    · simp [c₀]
    · intro k _ hk; simp [c₀, hk]
    · intro hm; exact absurd (mem_range.mpr (Nat.lt_succ_self m)) hm
  have hy₀_m : y₀ m = ((2 * m).factorial : ℝ) / (m.factorial : ℝ) := by
    dsimp only [y₀, c₀]
    rw [sum_Ico_succ_top le_rfl, Ico_self, sum_empty, zero_add, if_pos rfl,
      mul_one, ← anat_diag_cast m]
    unfold legCoeff ANat
    simp [Nat.choose_self]
  have hy₀_m_pos : 0 < y₀ m := by
    rw [hy₀_m]
    exact div_pos (Nat.cast_pos.mpr (Nat.factorial_pos _)) (Nat.cast_pos.mpr (Nat.factorial_pos _))
  have hy₀_len_ge : (((2 * m).factorial : ℝ) / (m.factorial : ℝ)) ^ 2 ≤
      OMA.S_mo_373858.lengthSq m y₀ := by
    rw [← hy₀_m]
    exact single_le_sum (fun i _ => sq_nonneg (y₀ i)) (mem_range.mpr (Nat.lt_succ_self m))
  have hy₀_len_pos : 0 < OMA.S_mo_373858.lengthSq m y₀ :=
    lt_of_lt_of_le (by rw [← hy₀_m]; exact sq_pos_of_pos hy₀_m_pos) hy₀_len_ge
  let r₀ : ℝ := (OMA.S_mo_373858.energy m x₀ * OMA.S_mo_373858.lengthSq m y₀) /
    (OMA.S_mo_373858.lengthSq m x₀ * OMA.S_mo_373858.energy m y₀)
  have hr₀_mem : r₀ ∈ S := ⟨x₀, y₀, by linarith, hy₀_len_pos, rfl⟩
  have hr₀_ge : OMA.S_mo_373858.scale m ≤ r₀ := by
    have hr₀_eq : r₀ = (2 * (m : ℝ) + 1) * OMA.S_mo_373858.lengthSq m y₀ := by
      simp only [r₀, hx₀_en, hx₀_len, hy₀_en, one_mul]
      have hm_pos : (2 * (m : ℝ) + 1) ≠ 0 := by positivity
      field_simp [hm_pos]
    rw [hr₀_eq]
    exact mul_le_mul_of_nonneg_left hy₀_len_ge (by positivity)
  exact ⟨hr₀_ge.trans (le_csSup ⟨12 * OMA.S_mo_373858.scale m, hS_ub⟩ hr₀_mem),
    csSup_le ⟨r₀, hr₀_mem⟩ hS_ub⟩

end

theorem OMA.solution : type_of% @OMA.S_mo_373858.main := by
  intro m
  exact ⟨hilb_energy_pos m, hilb_cond_bounds m⟩
