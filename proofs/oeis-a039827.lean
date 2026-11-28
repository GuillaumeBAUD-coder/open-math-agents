import OMAStatements.S_oeis_a039827

open OMA.S_oeis_a039827 Polynomial Finset intervalIntegral

namespace OMA_A039827

/-! ### Section 1: Basic algebraic properties of P n -/

private lemma two_mul_half (n : ℕ) : 2 * (n * (n + 1) / 2) = n * (n + 1) := by
  have h : Even (n * (n + 1)) := Nat.even_mul_succ_self n
  rcases h with ⟨k, hk⟩
  omega

private lemma half_succ (n : ℕ) :
    (n + 1) * (n + 2) / 2 = n * (n + 1) / 2 + (n + 1) := by
  have h1 := two_mul_half n
  have h2 := two_mul_half (n + 1)
  have h3 : (n + 1) * (n + 2) = n * (n + 1) + 2 * (n + 1) := by ring
  omega

private lemma P_zero : P 0 = 1 := by
  simp [P]

private lemma P_succ (n : ℕ) :
    P (n + 1) = P n * (1 + X ^ (n + 1) + X ^ (2 * (n + 1))) := by
  unfold P
  have hIcc : Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
    ext x
    simp only [mem_Icc, mem_insert]
    omega
  rw [hIcc, prod_insert (by simp), mul_comm]

private lemma coeff_P_succ (n k : ℕ) :
    (P (n + 1)).coeff k =
      (P n).coeff k +
      (if n + 1 ≤ k then (P n).coeff (k - (n + 1)) else 0) +
      (if 2 * (n + 1) ≤ k then (P n).coeff (k - 2 * (n + 1)) else 0) := by
  rw [P_succ, mul_add, mul_add, mul_one, coeff_add, coeff_add,
    coeff_mul_X_pow', coeff_mul_X_pow']

private lemma factor_natDegree_leadingCoeff (d : ℕ) (hd : 1 ≤ d) :
    (1 + X ^ d + X ^ (2 * d) : ℕ[X]).natDegree = 2 * d ∧
    (1 + X ^ d + X ^ (2 * d) : ℕ[X]).leadingCoeff = 1 := by
  have hlt : (1 + X ^ d : ℕ[X]).natDegree < (X ^ (2 * d) : ℕ[X]).natDegree := by
    rw [natDegree_X_pow]
    calc (1 + X ^ d : ℕ[X]).natDegree
        ≤ max (1 : ℕ[X]).natDegree (X ^ d : ℕ[X]).natDegree := natDegree_add_le _ _
      _ = d := by simp
      _ < 2 * d := by omega
  have hdeg : (1 + X ^ d + X ^ (2 * d) : ℕ[X]).natDegree = 2 * d := by
    rw [natDegree_add_eq_right_of_natDegree_lt hlt, natDegree_X_pow]
  have hlc : (1 + X ^ d + X ^ (2 * d) : ℕ[X]).leadingCoeff = 1 := by
    rw [leadingCoeff_add_of_degree_lt (degree_lt_degree hlt), leadingCoeff_X_pow]
  exact ⟨hdeg, hlc⟩

private lemma natDegree_leadingCoeff_P (n : ℕ) :
    (P n).natDegree = n * (n + 1) ∧ (P n).leadingCoeff = 1 := by
  induction n with
  | zero => simp [P_zero]
  | succ n ih =>
    have hfac := factor_natDegree_leadingCoeff (n + 1) (by omega)
    have hp0 : P n ≠ 0 := by
      intro h
      rw [h, leadingCoeff_zero] at ih
      exact zero_ne_one ih.2
    have hq0 : (1 + X ^ (n + 1) + X ^ (2 * (n + 1)) : ℕ[X]) ≠ 0 := by
      intro h
      rw [h, leadingCoeff_zero] at hfac
      exact zero_ne_one hfac.2
    rw [P_succ, natDegree_mul hp0 hq0, leadingCoeff_mul, ih.1, ih.2, hfac.1, hfac.2, mul_one]
    exact ⟨by ring, rfl⟩

private lemma natDegree_P (n : ℕ) : (P n).natDegree = n * (n + 1) :=
  (natDegree_leadingCoeff_P n).1

private lemma coeff_P_eq_zero_of_gt (n k : ℕ) (hk : n * (n + 1) < k) :
    (P n).coeff k = 0 := by
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  rw [natDegree_P]
  exact hk

private lemma coeff_P_symm (n : ℕ) :
    ∀ k ≤ n * (n + 1), (P n).coeff (n * (n + 1) - k) = (P n).coeff k := by
  induction n with
  | zero =>
    intro k hk
    have : k = 0 := by omega
    subst this
    simp [P_zero]
  | succ n ih =>
    intro k hk
    set d := n + 1
    set D := n * (n + 1)
    have hD' : (n + 1) * (n + 2) = D + 2 * d := by dsimp [D, d]; ring
    rw [hD'] at hk ⊢
    rw [coeff_P_succ, coeff_P_succ]
    change (P n).coeff (D + 2 * d - k) +
        (if d ≤ D + 2 * d - k then (P n).coeff (D + 2 * d - k - d) else 0) +
        (if 2 * d ≤ D + 2 * d - k then (P n).coeff (D + 2 * d - k - 2 * d) else 0) =
      (P n).coeff k +
        (if d ≤ k then (P n).coeff (k - d) else 0) +
        (if 2 * d ≤ k then (P n).coeff (k - 2 * d) else 0)
    have h1 : (P n).coeff (D + 2 * d - k) =
        if 2 * d ≤ k then (P n).coeff (k - 2 * d) else 0 := by
      split_ifs with h
      · have hsub : D + 2 * d - k = D - (k - 2 * d) := by omega
        rw [hsub, ih (k - 2 * d) (by omega)]
      · exact coeff_P_eq_zero_of_gt n _ (by omega)
    have h2 : (if d ≤ D + 2 * d - k then (P n).coeff (D + 2 * d - k - d) else 0) =
        if d ≤ k then (P n).coeff (k - d) else 0 := by
      split_ifs with ha hb hb
      · by_cases hkd : k - d ≤ D
        · have hsub : D + 2 * d - k - d = D - (k - d) := by omega
          rw [hsub, ih (k - d) hkd]
        · rw [coeff_P_eq_zero_of_gt n _ (by omega), coeff_P_eq_zero_of_gt n _ (by omega)]
      · exact coeff_P_eq_zero_of_gt n _ (by omega)
      · exact (coeff_P_eq_zero_of_gt n _ (by omega)).symm
      · rfl
    have h3 : (if 2 * d ≤ D + 2 * d - k then (P n).coeff (D + 2 * d - k - 2 * d) else 0) =
        (P n).coeff k := by
      split_ifs with h
      · have hsub : D + 2 * d - k - 2 * d = D - k := by omega
        rw [hsub, ih k (by omega)]
      · exact (coeff_P_eq_zero_of_gt n _ (by omega)).symm
    omega

/-! ### Section 2: Computable list engine and verification for n = 1..36 -/

private def addList : List ℕ → List ℕ → List ℕ
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys => (x + y) :: addList xs ys

private lemma getD_addList : ∀ (xs ys : List ℕ) (k : ℕ),
    (addList xs ys).getD k 0 = xs.getD k 0 + ys.getD k 0
  | [], ys, k => by simp [addList]
  | x :: xs, [], k => by simp [addList]
  | x :: xs, y :: ys, 0 => by simp [addList]
  | x :: xs, y :: ys, k + 1 => by simp only [addList, List.getD_cons_succ, getD_addList xs ys k]

private lemma length_addList : ∀ (xs ys : List ℕ),
    (addList xs ys).length = max xs.length ys.length
  | [], ys => by simp [addList]
  | x :: xs, [] => by simp [addList]
  | x :: xs, y :: ys => by simp [addList, length_addList xs ys]

private lemma getD_replicate_append (d : ℕ) (xs : List ℕ) (k : ℕ) :
    (List.replicate d 0 ++ xs).getD k 0 = if d ≤ k then xs.getD (k - d) 0 else 0 := by
  induction d generalizing k with
  | zero => simp
  | succ d ih =>
    cases k with
    | zero => simp [List.replicate]
    | succ k =>
      simp only [List.replicate_succ, List.cons_append, List.getD_cons_succ, ih k]
      split_ifs with h1 h2 h2
      · congr 1; omega
      · omega
      · omega
      · rfl

private def polyStep (d : ℕ) (xs : List ℕ) : List ℕ :=
  addList (addList xs (List.replicate d 0 ++ xs)) (List.replicate (2 * d) 0 ++ xs)

private def polyCoeffs : ℕ → List ℕ
  | 0 => [1]
  | n + 1 => polyStep (n + 1) (polyCoeffs n)

private lemma length_polyCoeffs (n : ℕ) :
    (polyCoeffs n).length = n * (n + 1) + 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [polyCoeffs, polyStep, length_addList, List.length_append, List.length_replicate, ih]
    set L := n * (n + 1) + 1
    have hL : (n + 1) * (n + 2) + 1 = 2 * (n + 1) + L := by dsimp [L]; ring
    rw [hL, Nat.max_eq_right (show L ≤ n + 1 + L by omega),
      Nat.max_eq_right (show n + 1 + L ≤ 2 * (n + 1) + L by omega)]

private lemma coeff_P_eq_getD (n k : ℕ) :
    (P n).coeff k = (polyCoeffs n).getD k 0 := by
  induction n generalizing k with
  | zero =>
    cases k with
    | zero => simp [P_zero, polyCoeffs]
    | succ k => simp [P_zero, polyCoeffs, Polynomial.coeff_one]
  | succ n ih =>
    rw [coeff_P_succ]
    simp only [polyCoeffs, polyStep, getD_addList, getD_replicate_append, ih]

private lemma coeff_P_small (n : ℕ) (hn : 3 ≤ n) :
    (P n).coeff 0 = 1 ∧ (P n).coeff 1 = 1 ∧ (P n).coeff 2 = 2 ∧ (P n).coeff 3 = 2 := by
  induction n, hn using Nat.le_induction with
  | base =>
    simp only [coeff_P_eq_getD]
    decide
  | succ n hn ih =>
    rcases ih with ⟨h0, h1, h2, h3⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [coeff_P_succ, if_neg (by omega), if_neg (by omega)]; omega
    · rw [coeff_P_succ, if_neg (by omega), if_neg (by omega)]; omega
    · rw [coeff_P_succ, if_neg (by omega), if_neg (by omega)]; omega
    · rw [coeff_P_succ, if_neg (by omega), if_neg (by omega)]; omega

private lemma a_eq_dedup_length (n : ℕ) : a n = (polyCoeffs n).dedup.length := by
  unfold a
  have hdeg : (P n).natDegree + 1 = (polyCoeffs n).length := by
    rw [natDegree_P, length_polyCoeffs]
  have himg : ((Finset.range ((P n).natDegree + 1)).image (P n).coeff) =
      (polyCoeffs n).dedup.toFinset := by
    ext v
    simp only [mem_image, mem_range, List.mem_toFinset, List.mem_dedup]
    rw [hdeg]
    constructor
    · rintro ⟨k, hk, rfl⟩
      rw [coeff_P_eq_getD, List.getD_eq_getElem _ _ hk]
      exact List.getElem_mem hk
    · intro hv
      rcases List.mem_iff_getElem.mp hv with ⟨k, hk, rfl⟩
      exact ⟨k, hk, by rw [coeff_P_eq_getD, List.getD_eq_getElem _ _ hk]⟩
  rw [himg, List.toFinset_card_of_nodup (List.nodup_dedup _)]

private lemma a_1 : a 1 = 1 := by rw [a_eq_dedup_length]; decide
private lemma a_2 : a 2 = 2 := by rw [a_eq_dedup_length]; decide
private lemma a_3 : a 3 = 3 := by rw [a_eq_dedup_length]; decide
private lemma a_4 : a 4 = 6 := by rw [a_eq_dedup_length]; decide
private lemma a_5 : a 5 = 11 := by rw [a_eq_dedup_length]; decide
private lemma a_6 : a 6 = 19 := by rw [a_eq_dedup_length]; decide
private lemma a_7 : a 7 = 26 := by rw [a_eq_dedup_length]; decide
private lemma a_8 : a 8 = 34 := by rw [a_eq_dedup_length]; decide
set_option maxRecDepth 20000 in
private lemma a_9 : a 9 = 44 := by rw [a_eq_dedup_length]; decide
set_option maxRecDepth 20000 in
private lemma a_10 : a 10 = 54 := by rw [a_eq_dedup_length]; decide

private def checkIncAux : ℕ → List ℕ → Bool
  | 0, _ => true
  | _ + 1, [] => false
  | _ + 1, [_] => false
  | m + 1, x :: y :: rest => decide (x < y) && checkIncAux m (y :: rest)

private lemma checkIncAux_spec : ∀ (count : ℕ) (xs : List ℕ),
    checkIncAux count xs = true → ∀ j < count, xs.getD j 0 < xs.getD (j + 1) 0
  | 0, _, _, _, hj => by omega
  | _ + 1, [], h, _, _ => by simp [checkIncAux] at h
  | _ + 1, [_], h, _, _ => by simp [checkIncAux] at h
  | m + 1, x :: y :: rest, h, j, hj => by
    simp only [checkIncAux, Bool.and_eq_true, decide_eq_true_eq] at h
    cases j with
    | zero => simpa using h.1
    | succ j =>
      simpa using checkIncAux_spec m (y :: rest) h.2 j (by omega)

private def checkIncRange (lo count : ℕ) (xs : List ℕ) : Bool :=
  checkIncAux count (xs.drop lo)

private lemma getD_drop (lo j : ℕ) (xs : List ℕ) :
    (xs.drop lo).getD j 0 = xs.getD (lo + j) 0 := by
  induction lo generalizing xs with
  | zero => simp
  | succ lo ih =>
    cases xs with
    | nil => simp
    | cons x xs =>
      simp only [List.drop_succ_cons, ih, Nat.succ_add, List.getD_cons_succ]

private lemma checkIncRange_spec (lo count : ℕ) (xs : List ℕ)
    (h : checkIncRange lo count xs = true) :
    ∀ k, lo ≤ k → k < lo + count → xs.getD k 0 < xs.getD (k + 1) 0 := by
  intro k hk1 hk2
  have hspec := checkIncAux_spec count (xs.drop lo) h (k - lo) (by omega)
  rw [getD_drop, getD_drop] at hspec
  have heq1 : lo + (k - lo) = k := by omega
  have heq2 : lo + (k - lo + 1) = k + 1 := by omega
  rwa [heq1, heq2] at hspec

private def checkPeakSteps : ℕ → ℕ → List ℕ → Bool
  | _, 0, _ => true
  | n, steps + 1, xs =>
    let xs' := polyStep (n + 1) xs
    checkIncRange (n * (n + 1) / 2) (n + 1) xs' && checkPeakSteps (n + 1) steps xs'

private lemma checkPeakSteps_spec : ∀ (steps n : ℕ),
    checkPeakSteps n steps (polyCoeffs n) = true →
    ∀ m, n < m → m ≤ n + steps →
    ∀ k, (m - 1) * m / 2 ≤ k → k < m * (m + 1) / 2 →
      (P m).coeff k < (P m).coeff (k + 1)
  | 0, n, _, m, h1, h2 => by omega
  | steps + 1, n, h, m, h1, h2 => by
    simp only [checkPeakSteps, Bool.and_eq_true] at h
    have hstep : polyStep (n + 1) (polyCoeffs n) = polyCoeffs (n + 1) := rfl
    rw [hstep] at h
    by_cases hm : m = n + 1
    · subst hm
      intro k hk1 hk2
      rw [coeff_P_eq_getD, coeff_P_eq_getD]
      apply checkIncRange_spec (n * (n + 1) / 2) (n + 1) (polyCoeffs (n + 1)) h.1 k
      · simpa using hk1
      · rw [← half_succ n]
        exact hk2
    · exact checkPeakSteps_spec steps (n + 1) h.2 m (by omega) (by omega)

private lemma strict_inc_P11 :
    ∀ k, 3 ≤ k → k < 11 * 12 / 2 → (P 11).coeff k < (P 11).coeff (k + 1) := by
  have h11 : checkIncRange 3 63 (polyCoeffs 11) = true := by decide
  intro k hk1 hk2
  rw [coeff_P_eq_getD, coeff_P_eq_getD]
  exact checkIncRange_spec 3 63 (polyCoeffs 11) h11 k hk1 (by omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private lemma peak_inc_small :
    ∀ m, 11 < m → m ≤ 36 →
    ∀ k, (m - 1) * m / 2 ≤ k → k < m * (m + 1) / 2 →
      (P m).coeff k < (P m).coeff (k + 1) := by
  have hpeak : checkPeakSteps 11 25 (polyCoeffs 11) = true := by decide
  exact checkPeakSteps_spec 25 11 hpeak

/-! ### Section 3: Real Fourier representation of coefficient differences -/

private noncomputable def F (n : ℕ) (θ : ℝ) : ℝ :=
  ∏ j ∈ Finset.Icc 1 n, (1 + 2 * Real.cos ((j : ℝ) * θ))

private lemma continuous_F (n : ℕ) : Continuous (F n) := by
  unfold F
  fun_prop

private lemma F_zero (θ : ℝ) : F 0 θ = 1 := by
  simp [F]

private lemma F_succ (n : ℕ) (θ : ℝ) :
    F (n + 1) θ = F n θ * (1 + 2 * Real.cos (((n + 1 : ℕ) : ℝ) * θ)) := by
  unfold F
  have hIcc : Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
    ext x
    simp only [mem_Icc, mem_insert]
    omega
  rw [hIcc, prod_insert (by simp), mul_comm]

private lemma two_mul_cos_mul_cos (a b : ℝ) :
    2 * Real.cos a * Real.cos b = Real.cos (a + b) + Real.cos (a - b) := by
  rw [Real.cos_add, Real.cos_sub]
  ring

private lemma cos_sub_cos_eq (a b : ℝ) :
    Real.cos (a - b) - Real.cos (a + b) = 2 * Real.sin a * Real.sin b := by
  rw [Real.cos_sub, Real.cos_add]
  ring

private lemma two_mul_sin_mul_cos (a b : ℝ) :
    2 * Real.sin b * Real.cos a = Real.sin (a + b) - Real.sin (a - b) := by
  rw [Real.sin_add, Real.sin_sub]
  ring

private lemma F_eq_sum_cos (n : ℕ) (θ : ℝ) :
    F n θ = ∑ k ∈ Finset.range (n * (n + 1) + 1),
      ((P n).coeff k : ℝ) * Real.cos ((((n * (n + 1) / 2 : ℕ) : ℝ) - (k : ℝ)) * θ) := by
  induction n with
  | zero => simp [F_zero, P_zero]
  | succ n ih =>
    set d := n + 1
    set D := n * (n + 1)
    set M := n * (n + 1) / 2
    set M' := (n + 1) * (n + 2) / 2
    have hM' : M' = M + d := half_succ n
    have hD' : (n + 1) * (n + 2) = D + 2 * d := by dsimp [D, d]; ring
    rw [F_succ, ih, sum_mul]
    have hterm : ∀ k ∈ Finset.range (D + 1),
        ((P n).coeff k : ℝ) * Real.cos (((M : ℝ) - (k : ℝ)) * θ) *
          (1 + 2 * Real.cos ((d : ℝ) * θ)) =
        ((P n).coeff k : ℝ) * Real.cos (((M' : ℝ) - (k : ℝ)) * θ) +
        ((P n).coeff k : ℝ) * Real.cos (((M' : ℝ) - ((k + d : ℕ) : ℝ)) * θ) +
        ((P n).coeff k : ℝ) * Real.cos (((M' : ℝ) - ((k + 2 * d : ℕ) : ℝ)) * θ) := by
      intro k _
      have hcast : (M' : ℝ) = (M : ℝ) + (d : ℝ) := by exact_mod_cast hM'
      have ha1 : (((M : ℝ) - (k : ℝ)) * θ) + ((d : ℝ) * θ) = ((M' : ℝ) - (k : ℝ)) * θ := by
        rw [hcast]; ring
      have ha2 : (((M : ℝ) - (k : ℝ)) * θ) = ((M' : ℝ) - ((k + d : ℕ) : ℝ)) * θ := by
        rw [hcast]; push_cast; ring
      have ha3 : (((M : ℝ) - (k : ℝ)) * θ) - ((d : ℝ) * θ) =
          ((M' : ℝ) - ((k + 2 * d : ℕ) : ℝ)) * θ := by
        rw [hcast]; push_cast; ring
      have hprod := two_mul_cos_mul_cos (((M : ℝ) - (k : ℝ)) * θ) ((d : ℝ) * θ)
      rw [ha1, ha3] at hprod
      calc ((P n).coeff k : ℝ) * Real.cos (((M : ℝ) - (k : ℝ)) * θ) *
            (1 + 2 * Real.cos ((d : ℝ) * θ))
          = ((P n).coeff k : ℝ) * (Real.cos (((M : ℝ) - (k : ℝ)) * θ) +
              2 * Real.cos (((M : ℝ) - (k : ℝ)) * θ) * Real.cos ((d : ℝ) * θ)) := by ring
        _ = ((P n).coeff k : ℝ) * (Real.cos (((M : ℝ) - (k : ℝ)) * θ) +
              (Real.cos (((M' : ℝ) - (k : ℝ)) * θ) +
                Real.cos (((M' : ℝ) - ((k + 2 * d : ℕ) : ℝ)) * θ))) := by rw [hprod]
        _ = ((P n).coeff k : ℝ) * Real.cos (((M' : ℝ) - (k : ℝ)) * θ) +
            ((P n).coeff k : ℝ) * Real.cos (((M' : ℝ) - ((k + d : ℕ) : ℝ)) * θ) +
            ((P n).coeff k : ℝ) * Real.cos (((M' : ℝ) - ((k + 2 * d : ℕ) : ℝ)) * θ) := by
              rw [ha2]; ring
    rw [sum_congr rfl hterm, sum_add_distrib, sum_add_distrib]
    have hRHS :
        ∑ j ∈ Finset.range ((n + 1) * (n + 2) + 1),
          ((P (n + 1)).coeff j : ℝ) * Real.cos (((M' : ℝ) - (j : ℝ)) * θ) =
        (∑ j ∈ Finset.range ((n + 1) * (n + 2) + 1),
          ((P n).coeff j : ℝ) * Real.cos (((M' : ℝ) - (j : ℝ)) * θ)) +
        (∑ j ∈ Finset.range ((n + 1) * (n + 2) + 1),
          ((if d ≤ j then (P n).coeff (j - d) else 0 : ℕ) : ℝ) *
            Real.cos (((M' : ℝ) - (j : ℝ)) * θ)) +
        (∑ j ∈ Finset.range ((n + 1) * (n + 2) + 1),
          ((if 2 * d ≤ j then (P n).coeff (j - 2 * d) else 0 : ℕ) : ℝ) *
            Real.cos (((M' : ℝ) - (j : ℝ)) * θ)) := by
      rw [← sum_add_distrib, ← sum_add_distrib]
      apply sum_congr rfl
      intro j _
      rw [coeff_P_succ]
      push_cast
      ring
    rw [hRHS]
    have hS1 : ∑ k ∈ Finset.range (D + 1),
        ((P n).coeff k : ℝ) * Real.cos (((M' : ℝ) - (k : ℝ)) * θ) =
        ∑ j ∈ Finset.range ((n + 1) * (n + 2) + 1),
        ((P n).coeff j : ℝ) * Real.cos (((M' : ℝ) - (j : ℝ)) * θ) := by
      symm
      rw [hD', show D + 2 * d + 1 = (D + 1) + 2 * d by omega, sum_range_add]
      have hzero : ∑ x ∈ Finset.range (2 * d),
          ((P n).coeff (D + 1 + x) : ℝ) * Real.cos (((M' : ℝ) - ((D + 1 + x : ℕ) : ℝ)) * θ) = 0 := by
        apply sum_eq_zero
        intro x _
        rw [coeff_P_eq_zero_of_gt n (D + 1 + x) (by omega)]
        simp
      rw [hzero, add_zero]
    have hS2 : ∑ k ∈ Finset.range (D + 1),
        ((P n).coeff k : ℝ) * Real.cos (((M' : ℝ) - ((k + d : ℕ) : ℝ)) * θ) =
        ∑ j ∈ Finset.range ((n + 1) * (n + 2) + 1),
        ((if d ≤ j then (P n).coeff (j - d) else 0 : ℕ) : ℝ) *
          Real.cos (((M' : ℝ) - (j : ℝ)) * θ) := by
      symm
      rw [hD', show D + 2 * d + 1 = d + (D + 1 + d) by omega, sum_range_add]
      have hlo : ∑ x ∈ Finset.range d,
          ((if d ≤ x then (P n).coeff (x - d) else 0 : ℕ) : ℝ) *
            Real.cos (((M' : ℝ) - (x : ℝ)) * θ) = 0 := by
        apply sum_eq_zero
        intro x hx
        rw [mem_range] at hx
        rw [if_neg (by omega)]
        simp
      rw [hlo, zero_add, sum_range_add]
      have hhi : ∑ x ∈ Finset.range d,
          ((if d ≤ d + (D + 1 + x) then (P n).coeff (d + (D + 1 + x) - d) else 0 : ℕ) : ℝ) *
            Real.cos (((M' : ℝ) - ((d + (D + 1 + x) : ℕ) : ℝ)) * θ) = 0 := by
        apply sum_eq_zero
        intro x _
        rw [if_pos (by omega), show d + (D + 1 + x) - d = D + 1 + x by omega,
          coeff_P_eq_zero_of_gt n (D + 1 + x) (by omega)]
        simp
      rw [hhi, add_zero]
      apply sum_congr rfl
      intro k _
      rw [if_pos (by omega), show d + k - d = k by omega, add_comm d k]
    have hS3 : ∑ k ∈ Finset.range (D + 1),
        ((P n).coeff k : ℝ) * Real.cos (((M' : ℝ) - ((k + 2 * d : ℕ) : ℝ)) * θ) =
        ∑ j ∈ Finset.range ((n + 1) * (n + 2) + 1),
        ((if 2 * d ≤ j then (P n).coeff (j - 2 * d) else 0 : ℕ) : ℝ) *
          Real.cos (((M' : ℝ) - (j : ℝ)) * θ) := by
      symm
      rw [hD', show D + 2 * d + 1 = 2 * d + (D + 1) by omega, sum_range_add]
      have hlo : ∑ x ∈ Finset.range (2 * d),
          ((if 2 * d ≤ x then (P n).coeff (x - 2 * d) else 0 : ℕ) : ℝ) *
            Real.cos (((M' : ℝ) - (x : ℝ)) * θ) = 0 := by
        apply sum_eq_zero
        intro x hx
        rw [mem_range] at hx
        rw [if_neg (by omega)]
        simp
      rw [hlo, zero_add]
      apply sum_congr rfl
      intro k _
      rw [if_pos (by omega), show 2 * d + k - 2 * d = k by omega, add_comm (2 * d) k]
    rw [hS1, hS2, hS3]

private lemma integral_cos_int_mul (m : ℤ) :
    ∫ θ in (0 : ℝ)..Real.pi, Real.cos ((m : ℝ) * θ) = if m = 0 then Real.pi else 0 := by
  by_cases hm : m = 0
  · subst hm
    simp
  · rw [if_neg hm]
    have hmR : (m : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hm
    have hderiv : ∀ θ ∈ Set.uIcc (0 : ℝ) Real.pi,
        HasDerivAt (fun x => Real.sin ((m : ℝ) * x) / (m : ℝ)) (Real.cos ((m : ℝ) * θ)) θ := by
      intro θ _
      have h1 : HasDerivAt (fun x => (m : ℝ) * x) (m : ℝ) θ := by
        simpa using (hasDerivAt_id θ).const_mul (m : ℝ)
      have h2 : HasDerivAt (fun x => Real.sin ((m : ℝ) * x))
          (Real.cos ((m : ℝ) * θ) * (m : ℝ)) θ := h1.sin
      have h3 := h2.div_const (m : ℝ)
      rwa [mul_div_cancel_right₀ _ hmR] at h3
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      (Continuous.intervalIntegrable (by fun_prop) _ _)]
    simp [Real.sin_int_mul_pi]

private lemma integral_F_mul_cos (n r : ℕ) (hr : r ≤ n * (n + 1) / 2) :
    ∫ θ in (0 : ℝ)..Real.pi, F n θ * Real.cos ((r : ℝ) * θ) =
      Real.pi * ((P n).coeff (n * (n + 1) / 2 - r) : ℝ) := by
  set D := n * (n + 1)
  set M := n * (n + 1) / 2
  have h2M : 2 * M = D := two_mul_half n
  have hfun : (fun θ => F n θ * Real.cos ((r : ℝ) * θ)) =
      fun θ => ∑ k ∈ Finset.range (D + 1),
        ((P n).coeff k : ℝ) * (Real.cos (((M : ℝ) - (k : ℝ)) * θ) * Real.cos ((r : ℝ) * θ)) := by
    ext θ
    rw [F_eq_sum_cos, sum_mul]
    apply sum_congr rfl
    intro k _
    ring
  rw [hfun, intervalIntegral.integral_finsetSum]
  · have hterm : ∀ k ∈ Finset.range (D + 1),
        ∫ θ in (0 : ℝ)..Real.pi,
          ((P n).coeff k : ℝ) * (Real.cos (((M : ℝ) - (k : ℝ)) * θ) * Real.cos ((r : ℝ) * θ)) =
        (Real.pi / 2) * ((if k = M + r then ((P n).coeff k : ℝ) else 0) +
          (if k = M - r then ((P n).coeff k : ℝ) else 0)) := by
      intro k _
      rw [intervalIntegral.integral_const_mul]
      have hcos : (fun θ => Real.cos (((M : ℝ) - (k : ℝ)) * θ) * Real.cos ((r : ℝ) * θ)) =
          fun θ => (1 / 2 : ℝ) * (Real.cos ((((M : ℤ) - k + r : ℤ) : ℝ) * θ) +
            Real.cos ((((M : ℤ) - k - r : ℤ) : ℝ) * θ)) := by
        ext θ
        have hp := two_mul_cos_mul_cos (((M : ℝ) - (k : ℝ)) * θ) ((r : ℝ) * θ)
        have ha : (((M : ℝ) - (k : ℝ)) * θ) + ((r : ℝ) * θ) =
            ((((M : ℤ) - k + r : ℤ) : ℝ) * θ) := by push_cast; ring
        have hb : (((M : ℝ) - (k : ℝ)) * θ) - ((r : ℝ) * θ) =
            ((((M : ℤ) - k - r : ℤ) : ℝ) * θ) := by push_cast; ring
        rw [ha, hb] at hp
        linarith
      rw [hcos, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_add
          (Continuous.intervalIntegrable (by fun_prop) _ _)
          (Continuous.intervalIntegrable (by fun_prop) _ _),
        integral_cos_int_mul, integral_cos_int_mul]
      have heq1 : ((M : ℤ) - (k : ℤ) + (r : ℤ) = 0) ↔ k = M + r := by omega
      have heq2 : ((M : ℤ) - (k : ℤ) - (r : ℤ) = 0) ↔ k = M - r := by omega
      simp only [heq1, heq2]
      split_ifs <;> ring
    rw [sum_congr rfl hterm, ← mul_sum, sum_add_distrib]
    have hmem1 : M + r ∈ Finset.range (D + 1) := by rw [mem_range]; omega
    have hmem2 : M - r ∈ Finset.range (D + 1) := by rw [mem_range]; omega
    rw [sum_ite_eq' _ (M + r), if_pos hmem1, sum_ite_eq' _ (M - r), if_pos hmem2]
    have hsym : (P n).coeff (M + r) = (P n).coeff (M - r) := by
      have h := coeff_P_symm n (M - r) (by omega)
      have hsub : D - (M - r) = M + r := by omega
      rwa [hsub] at h
    rw [hsym]
    ring
  · intro k _
    exact Continuous.intervalIntegrable (by fun_prop) _ _

private lemma integral_F_diff (n r : ℕ) (hr : r < n * (n + 1) / 2) :
    Real.pi * (((P n).coeff (n * (n + 1) / 2 - r) : ℝ) -
      ((P n).coeff (n * (n + 1) / 2 - r - 1) : ℝ)) =
    2 * ∫ θ in (0 : ℝ)..Real.pi,
      F n θ * Real.sin (((r : ℝ) + 1 / 2) * θ) * Real.sin (θ / 2) := by
  have h1 := integral_F_mul_cos n r (by omega)
  have h2 := integral_F_mul_cos n (r + 1) (by omega)
  have hsub : n * (n + 1) / 2 - (r + 1) = n * (n + 1) / 2 - r - 1 := by omega
  rw [hsub] at h2
  have hi1 : IntervalIntegrable (fun θ => F n θ * Real.cos ((r : ℝ) * θ))
      MeasureTheory.volume 0 Real.pi :=
    ((continuous_F n).mul (by fun_prop)).intervalIntegrable 0 Real.pi
  have hi2 : IntervalIntegrable (fun θ => F n θ * Real.cos (((r + 1 : ℕ) : ℝ) * θ))
      MeasureTheory.volume 0 Real.pi :=
    ((continuous_F n).mul (by fun_prop)).intervalIntegrable 0 Real.pi
  rw [mul_sub, ← h1, ← h2, ← intervalIntegral.integral_sub hi1 hi2,
    ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro θ _
  have hc := cos_sub_cos_eq (((r : ℝ) + 1 / 2) * θ) (θ / 2)
  have ha : ((r : ℝ) + 1 / 2) * θ - θ / 2 = (r : ℝ) * θ := by ring
  have hb : ((r : ℝ) + 1 / 2) * θ + θ / 2 = ((r + 1 : ℕ) : ℝ) * θ := by push_cast; ring
  rw [ha, hb] at hc
  calc F n θ * Real.cos ((r : ℝ) * θ) - F n θ * Real.cos (((r + 1 : ℕ) : ℝ) * θ)
      = F n θ * (Real.cos ((r : ℝ) * θ) - Real.cos (((r + 1 : ℕ) : ℝ) * θ)) := by ring
    _ = F n θ * (2 * Real.sin (((r : ℝ) + 1 / 2) * θ) * Real.sin (θ / 2)) := by rw [hc]
    _ = 2 * (F n θ * Real.sin (((r : ℝ) + 1 / 2) * θ) * Real.sin (θ / 2)) := by ring

/-! ### Section 4: Elementary trigonometry, Bernoulli, AM-GM, and Dirichlet kernel -/

private lemma cos_ge_one_sub_sq_div_two {x : ℝ} (hx : 0 ≤ x) :
    1 - x ^ 2 / 2 ≤ Real.cos x := by
  have hmono : MonotoneOn (fun t => Real.cos t - (1 - t ^ 2 / 2)) (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact (by fun_prop : Continuous _).continuousOn
    · exact (by fun_prop : Differentiable ℝ _).differentiableOn
    · intro t ht
      have ht0 : 0 ≤ t := le_of_lt (by simpa [interior_Ici] using ht)
      have hd : HasDerivAt (fun s : ℝ => Real.cos s - (1 - s ^ 2 / 2)) (-Real.sin t + t) t := by
        have h1 : HasDerivAt (fun s : ℝ => Real.cos s) (-Real.sin t) t := Real.hasDerivAt_cos t
        have h2 : HasDerivAt (fun s : ℝ => (1 : ℝ)) 0 t := hasDerivAt_const t (1 : ℝ)
        have h3 : HasDerivAt (fun s : ℝ => s ^ 2 / 2) (↑(2 : ℕ) * t ^ (2 - 1) / 2) t :=
          (hasDerivAt_pow 2 t).div_const 2
        have h4 := h1.sub (h2.sub h3)
        have heq : -Real.sin t - (0 - ↑(2 : ℕ) * t ^ (2 - 1) / 2) = -Real.sin t + t := by
          norm_num
        rw [← heq]
        exact h4
      rw [hd.deriv]
      linarith [Real.sin_le ht0]
  have h := hmono (by simp : (0 : ℝ) ∈ Set.Ici 0) hx hx
  simp at h
  linarith

private lemma sin_ge_sub_cube_div_six {x : ℝ} (hx : 0 ≤ x) :
    x - x ^ 3 / 6 ≤ Real.sin x := by
  have hmono : MonotoneOn (fun t => Real.sin t - (t - t ^ 3 / 6)) (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact (by fun_prop : Continuous _).continuousOn
    · exact (by fun_prop : Differentiable ℝ _).differentiableOn
    · intro t ht
      have ht0 : 0 ≤ t := le_of_lt (by simpa [interior_Ici] using ht)
      have hd : HasDerivAt (fun s : ℝ => Real.sin s - (s - s ^ 3 / 6))
          (Real.cos t - (1 - t ^ 2 / 2)) t := by
        have h1 : HasDerivAt (fun s : ℝ => Real.sin s) (Real.cos t) t := Real.hasDerivAt_sin t
        have h2 : HasDerivAt (fun s : ℝ => s) 1 t := hasDerivAt_id' t
        have h3 : HasDerivAt (fun s : ℝ => s ^ 3 / 6) (↑(3 : ℕ) * t ^ (3 - 1) / 6) t :=
          (hasDerivAt_pow 3 t).div_const 6
        have h4 := h1.sub (h2.sub h3)
        have heq : Real.cos t - (1 - ↑(3 : ℕ) * t ^ (3 - 1) / 6) = Real.cos t - (1 - t ^ 2 / 2) := by
          norm_num; ring
        rw [← heq]
        exact h4
      rw [hd.deriv]
      linarith [cos_ge_one_sub_sq_div_two ht0]
  have h := hmono (by simp : (0 : ℝ) ∈ Set.Ici 0) hx hx
  simp at h
  linarith

private lemma sin_ge_23_24 {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    (23 / 24 : ℝ) * x ≤ Real.sin x := by
  have h := sin_ge_sub_cube_div_six hx0
  have hsq : x ^ 2 ≤ 1 / 4 := by nlinarith
  have hcube : x ^ 3 ≤ x / 4 := by nlinarith
  linarith

private lemma sin_ge_5_6 {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    (5 / 6 : ℝ) * x ≤ Real.sin x := by
  have h := sin_ge_sub_cube_div_six hx0
  have hsq : x ^ 2 ≤ 1 := by nlinarith
  have hcube : x ^ 3 ≤ x := by nlinarith
  linarith

private lemma bernoulli_prod {ι : Type*} [DecidableEq ι] (s : Finset ι) (a : ι → ℝ)
    (h0 : ∀ i ∈ s, 0 ≤ a i) (h1 : ∀ i ∈ s, a i ≤ 1) :
    1 - ∑ i ∈ s, a i ≤ ∏ i ∈ s, (1 - a i) := by
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih =>
    rw [sum_insert hi, prod_insert hi]
    have hai0 := h0 i (mem_insert_self i s)
    have hai1 := h1 i (mem_insert_self i s)
    have hprod_nonneg : 0 ≤ ∏ j ∈ s, (1 - a j) :=
      prod_nonneg fun j hj => by linarith [h1 j (mem_insert_of_mem hj)]
    have hih := ih (fun j hj => h0 j (mem_insert_of_mem hj))
      (fun j hj => h1 j (mem_insert_of_mem hj))
    have hsum_nonneg : 0 ≤ ∑ j ∈ s, a j :=
      sum_nonneg fun j hj => h0 j (mem_insert_of_mem hj)
    nlinarith

private lemma am_gm_prod {ι : Type*} (s : Finset ι) (f : ι → ℝ) {B : ℝ} (hB : 0 < B)
    (hf : ∀ i ∈ s, 0 ≤ f i) (hsum : ∑ i ∈ s, f i ≤ (s.card : ℝ) * B) :
    ∏ i ∈ s, f i ≤ B ^ s.card := by
  have h1 : ∏ i ∈ s, (f i / B) ≤ ∏ i ∈ s, Real.exp (f i / B - 1) := by
    apply prod_le_prod
    · intro i hi
      exact div_nonneg (hf i hi) hB.le
    · intro i _
      have := Real.add_one_le_exp (f i / B - 1)
      linarith
  rw [← Real.exp_sum] at h1
  have hsum' : ∑ i ∈ s, (f i / B - 1) ≤ 0 := by
    rw [sum_sub_distrib, ← sum_div, sum_const, nsmul_eq_mul, mul_one]
    have : (∑ i ∈ s, f i) / B ≤ (s.card : ℝ) := (div_le_iff₀ hB).mpr hsum
    linarith
  have h2 : ∏ i ∈ s, (f i / B) ≤ 1 := h1.trans ((Real.exp_le_one_iff).mpr hsum')
  rw [prod_div_distrib, prod_const] at h2
  exact (div_le_one (pow_pos hB s.card)).mp h2

private lemma sum_sq_Icc (n : ℕ) :
    (∑ j ∈ Finset.Icc 1 n, (j : ℝ) ^ 2) = (n : ℝ) * (n + 1) * (2 * n + 1) / 6 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hIcc : Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
      ext x
      simp only [mem_Icc, mem_insert]
      omega
    rw [hIcc, sum_insert (by simp), ih]
    push_cast
    ring

private lemma sum_cos_le (n : ℕ) {u : ℝ} (hu : 0 < Real.sin (u / 2)) :
    ∑ j ∈ Finset.Icc 1 n, Real.cos ((j : ℝ) * u) ≤ 1 / (2 * Real.sin (u / 2)) := by
  have htele : 2 * Real.sin (u / 2) * ∑ j ∈ Finset.Icc 1 n, Real.cos ((j : ℝ) * u) =
      Real.sin (((n : ℝ) + 1 / 2) * u) - Real.sin (u / 2) := by
    induction n with
    | zero => simp [div_eq_inv_mul]
    | succ n ih =>
      have hIcc : Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
        ext x
        simp only [mem_Icc, mem_insert]
        omega
      rw [hIcc, sum_insert (by simp), mul_add, ih]
      have htr := two_mul_sin_mul_cos (((n + 1 : ℕ) : ℝ) * u) (u / 2)
      have ha : ((n + 1 : ℕ) : ℝ) * u + u / 2 = (((n + 1 : ℕ) : ℝ) + 1 / 2) * u := by ring
      have hb : ((n + 1 : ℕ) : ℝ) * u - u / 2 = ((n : ℝ) + 1 / 2) * u := by push_cast; ring
      rw [ha, hb] at htr
      linarith
  have h2pos : 0 < 2 * Real.sin (u / 2) := by linarith
  rw [le_div_iff₀' h2pos, htele]
  linarith [Real.sin_le_one (((n : ℝ) + 1 / 2) * u)]

private lemma abs_one_add_two_cos_le (t : ℝ) :
    |1 + 2 * Real.cos t| ≤ 5 / 3 + (10 / 9) * Real.cos t + (4 / 9) * Real.cos (2 * t) := by
  rw [Real.cos_two_mul]
  have hc1 : -1 ≤ Real.cos t := Real.neg_one_le_cos t
  rw [abs_le]
  constructor
  · nlinarith [sq_nonneg (Real.cos t + 1)]
  · nlinarith [sq_nonneg (Real.cos t - 1 / 2)]

private lemma cos_three_pi_div_eight_le : Real.cos (3 * Real.pi / 8) ≤ 2 / 5 := by
  have hnonneg : 0 ≤ Real.cos (3 * Real.pi / 8) := by
    apply Real.cos_nonneg_of_mem_Icc
    constructor <;> linarith [Real.pi_pos]
  have h2 : Real.cos (2 * (3 * Real.pi / 8)) = -(Real.sqrt 2 / 2) := by
    have heq : 2 * (3 * Real.pi / 8) = Real.pi - Real.pi / 4 := by ring
    rw [heq, Real.cos_pi_sub, Real.cos_pi_div_four]
  rw [Real.cos_two_mul] at h2
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hsqrt_gt : (34 / 25 : ℝ) < Real.sqrt 2 := by nlinarith
  nlinarith

private lemma pair_bound {θ : ℝ} (h1 : 3 * Real.pi / 4 ≤ θ) (h2 : θ ≤ Real.pi) (x : ℝ) :
    |(1 + 2 * Real.cos x) * (1 + 2 * Real.cos (x + θ))| ≤ (9 / 5 : ℝ) ^ 2 := by
  set y := x + θ / 2
  set u := θ / 2
  have hx : x = y - u := by dsimp [y, u]; ring
  have hxt : x + θ = y + u := by dsimp [y, u]; ring
  rw [hxt, hx]
  have halg : (1 + 2 * Real.cos (y - u)) * (1 + 2 * Real.cos (y + u)) =
      4 * Real.cos y ^ 2 + 4 * Real.cos u * Real.cos y + 4 * Real.cos u ^ 2 - 3 := by
    rw [Real.cos_sub y u, Real.cos_add y u]
    have hs1 : Real.sin y ^ 2 = 1 - Real.cos y ^ 2 := Real.sin_sq y
    have hs2 : Real.sin u ^ 2 = 1 - Real.cos u ^ 2 := Real.sin_sq u
    nlinarith
  rw [halg]
  have hu0 : 0 ≤ Real.cos u := by
    apply Real.cos_nonneg_of_mem_Icc
    constructor <;> linarith [Real.pi_pos]
  have hu1 : Real.cos u ≤ 2 / 5 := by
    have hcos_le : Real.cos u ≤ Real.cos (3 * Real.pi / 8) := by
      apply Real.cos_le_cos_of_nonneg_of_le_pi
      · linarith [Real.pi_pos]
      · linarith [Real.pi_pos]
      · linarith
    exact hcos_le.trans cos_three_pi_div_eight_le
  have hy1 : -1 ≤ Real.cos y := Real.neg_one_le_cos y
  have hy2 : Real.cos y ≤ 1 := Real.cos_le_one y
  rw [abs_le]
  constructor <;> nlinarith

private lemma integral_sin_half (a b : ℝ) :
    ∫ θ in a..b, Real.sin (θ / 2) = 2 * Real.cos (a / 2) - 2 * Real.cos (b / 2) := by
  have hd : ∀ θ ∈ Set.uIcc a b,
      HasDerivAt (fun t : ℝ => -2 * Real.cos (t / 2)) (Real.sin (θ / 2)) θ := by
    intro θ _
    have h1 : HasDerivAt (fun t : ℝ => t / 2) (1 / 2) θ :=
      (hasDerivAt_id' θ).div_const 2
    have h2 : HasDerivAt (fun t : ℝ => -2 * Real.cos (t / 2))
        (-2 * (-Real.sin (θ / 2) * (1 / 2))) θ :=
      (h1.cos).const_mul (-2 : ℝ)
    have heq : (-2 : ℝ) * (-Real.sin (θ / 2) * (1 / 2)) = Real.sin (θ / 2) := by ring
    rw [← heq]
    exact h2
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  ring

private lemma integral_sin_half_le_sq {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ∫ θ in a..b, Real.sin (θ / 2) ≤ b ^ 2 / 4 := by
  have h1 : ∫ θ in a..b, Real.sin (θ / 2) ≤ ∫ θ in a..b, θ / 2 := by
    apply intervalIntegral.integral_mono_on hab
      (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _)
    intro θ hθ
    exact Real.sin_le (by linarith [hθ.1])
  have h2 : ∫ θ in a..b, θ / 2 = (b ^ 2 - a ^ 2) / 4 := by
    have hd : ∀ θ ∈ Set.uIcc a b, HasDerivAt (fun t : ℝ => t ^ 2 / 4) (θ / 2) θ := by
      intro θ _
      have h1 : HasDerivAt (fun t : ℝ => t ^ 2 / 4) (↑(2 : ℕ) * θ ^ (2 - 1) / 4) θ :=
        (hasDerivAt_pow 2 θ).div_const 4
      have heq : ↑(2 : ℕ) * θ ^ (2 - 1) / 4 = θ / 2 := by norm_num; ring
      rw [← heq]
      exact h1
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
      (Continuous.intervalIntegrable (by fun_prop) _ _)]
    ring
  rw [h2] at h1
  nlinarith

/-! ### Section 5: Main integral lower bound and piecewise tail upper bounds for n ≥ 37 -/

private lemma main_integral_lb (n r : ℕ) (hn : 37 ≤ n) (hr : r < n) :
    (2 / 3 : ℝ) * (3 : ℝ) ^ n / ((n : ℝ) ^ 4 * Real.sqrt n) ≤
      ∫ θ in (0 : ℝ)..(2 * Real.pi / (3 * (n : ℝ))),
        F n θ * Real.sin (((r : ℝ) + 1 / 2) * θ) * Real.sin (θ / 2) := by
  have hnR : (37 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hpi3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hpi4 : Real.pi < (3.15 : ℝ) := Real.pi_lt_d2
  set S2 : ℝ := (n : ℝ) * (n + 1) * (2 * n + 1) / 6
  have hS2_pos : 0 < S2 := by dsimp [S2]; positivity
  have hS2_ub : S2 ≤ (108 / 289 : ℝ) * (n : ℝ) ^ 3 := by
    have hq : ((n : ℝ) + 1) * (2 * (n : ℝ) + 1) ≤ (648 / 289 : ℝ) * (n : ℝ) ^ 2 := by nlinarith
    have hc : (n : ℝ) * (((n : ℝ) + 1) * (2 * (n : ℝ) + 1)) ≤
        (n : ℝ) * ((648 / 289 : ℝ) * (n : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hq hn0.le
    dsimp [S2]
    linarith [show (n : ℝ) * ((648 / 289 : ℝ) * (n : ℝ) ^ 2) = (648 / 289 : ℝ) * (n : ℝ) ^ 3 by ring,
      show (n : ℝ) * ((n : ℝ) + 1) * (2 * (n : ℝ) + 1) =
        (n : ℝ) * (((n : ℝ) + 1) * (2 * (n : ℝ) + 1)) by ring]
  set δ : ℝ := Real.sqrt (3 / S2)
  have hδ_pos : 0 < δ := Real.sqrt_pos.mpr (by positivity)
  have hδ_sq : δ ^ 2 = 3 / S2 := Real.sq_sqrt (by positivity)
  have hδ_le_half : δ ≤ Real.pi / (2 * (n : ℝ)) := by
    have hsq : δ ^ 2 ≤ (Real.pi / (2 * (n : ℝ))) ^ 2 := by
      rw [hδ_sq, div_pow, div_le_div_iff₀ hS2_pos (by positivity)]
      have hpi_sq : (9 : ℝ) ≤ Real.pi ^ 2 := by nlinarith
      have h1 : 2 * (n : ℝ) ^ 2 ≤ ((n : ℝ) + 1) * (2 * (n : ℝ) + 1) := by nlinarith
      have h2 : 74 * (n : ℝ) ^ 2 ≤ (n : ℝ) * (2 * (n : ℝ) ^ 2) := by
        nlinarith [sq_nonneg (n : ℝ)]
      have h3 : (n : ℝ) * (2 * (n : ℝ) ^ 2) ≤ (n : ℝ) * (((n : ℝ) + 1) * (2 * (n : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left h1 hn0.le
      have hS2_lb : 12 * (n : ℝ) ^ 2 ≤ S2 := by
        dsimp [S2]
        linarith [show (n : ℝ) * ((n : ℝ) + 1) * (2 * (n : ℝ) + 1) =
          (n : ℝ) * (((n : ℝ) + 1) * (2 * (n : ℝ) + 1)) by ring]
      nlinarith [sq_nonneg (n : ℝ)]
    have hnonneg : 0 ≤ Real.pi / (2 * (n : ℝ)) := by positivity
    nlinarith
  have hδ_le_a : δ ≤ 2 * Real.pi / (3 * (n : ℝ)) := by
    calc δ ≤ Real.pi / (2 * (n : ℝ)) := hδ_le_half
      _ ≤ 2 * Real.pi / (3 * (n : ℝ)) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
  set g : ℝ → ℝ := fun θ => F n θ * Real.sin (((r : ℝ) + 1 / 2) * θ) * Real.sin (θ / 2)
  have hg_cont : Continuous g := by
    dsimp [g]
    exact ((continuous_F n).mul (by fun_prop)).mul (by fun_prop)
  -- Step 1: g ≥ 0 on [δ, 2π/(3n)]
  have htail_nonneg : 0 ≤ ∫ θ in δ..(2 * Real.pi / (3 * (n : ℝ))), g θ := by
    apply intervalIntegral.integral_nonneg hδ_le_a
    intro θ hθ
    have hθ0 : 0 ≤ θ := le_trans hδ_pos.le hθ.1
    have hθa : θ ≤ 2 * Real.pi / (3 * (n : ℝ)) := hθ.2
    have hF_nn : 0 ≤ F n θ := by
      apply prod_nonneg
      intro j hj
      rw [mem_Icc] at hj
      have hjR : (j : ℝ) ≤ (n : ℝ) := by exact_mod_cast hj.2
      have hjt1 : 0 ≤ (j : ℝ) * θ := by positivity
      have hjt2 : (j : ℝ) * θ ≤ 2 * Real.pi / 3 := by
        calc (j : ℝ) * θ ≤ (n : ℝ) * (2 * Real.pi / (3 * (n : ℝ))) :=
              mul_le_mul hjR hθa hθ0 (by positivity)
          _ = 2 * Real.pi / 3 := by field_simp
      have hcos : -(1 / 2 : ℝ) ≤ Real.cos ((j : ℝ) * θ) := by
        have hpi23 : Real.cos (2 * Real.pi / 3) = -(1 / 2 : ℝ) := by
          have : 2 * Real.pi / 3 = Real.pi - Real.pi / 3 := by ring
          rw [this, Real.cos_pi_sub, Real.cos_pi_div_three]
        rw [← hpi23]
        exact Real.cos_le_cos_of_nonneg_of_le_pi hjt1 (by linarith) hjt2
      linarith
    have hrR : ((r : ℝ) + 1 / 2) ≤ (n : ℝ) := by
      have : (r : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hr
      linarith
    have hsin1 : 0 ≤ Real.sin (((r : ℝ) + 1 / 2) * θ) := by
      apply Real.sin_nonneg_of_nonneg_of_le_pi (by positivity)
      calc ((r : ℝ) + 1 / 2) * θ ≤ (n : ℝ) * (2 * Real.pi / (3 * (n : ℝ))) :=
            mul_le_mul hrR hθa hθ0 (by positivity)
        _ = 2 * Real.pi / 3 := by field_simp
        _ ≤ Real.pi := by linarith
    have hsin2 : 0 ≤ Real.sin (θ / 2) := by
      apply Real.sin_nonneg_of_nonneg_of_le_pi (by linarith)
      have : θ ≤ 2 * Real.pi / 3 := by
        calc θ ≤ 2 * Real.pi / (3 * (n : ℝ)) := hθa
          _ ≤ 2 * Real.pi / 3 := by
            rw [div_le_div_iff₀ (by positivity) (by norm_num)]
            nlinarith
      linarith
    dsimp [g]
    positivity
  have hsplit : ∫ θ in (0 : ℝ)..(2 * Real.pi / (3 * (n : ℝ))), g θ =
      (∫ θ in (0 : ℝ)..δ, g θ) + ∫ θ in δ..(2 * Real.pi / (3 * (n : ℝ))), g θ :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hg_cont.intervalIntegrable 0 δ)
      (hg_cont.intervalIntegrable δ (2 * Real.pi / (3 * (n : ℝ))))).symm
  -- Step 2: Lower bound on [0, δ]
  have hmain_sub : (3 : ℝ) ^ n * (529 / 2304 : ℝ) *
      ∫ θ in (0 : ℝ)..δ, (θ ^ 2 - (S2 / 3) * θ ^ 4) ≤ ∫ θ in (0 : ℝ)..δ, g θ := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hδ_pos.le
      (Continuous.intervalIntegrable (by fun_prop) _ _)
      (hg_cont.intervalIntegrable _ _)
    intro θ hθ
    have hθ0 : 0 ≤ θ := hθ.1
    have hθδ : θ ≤ δ := hθ.2
    have hθ_half : θ / 2 ≤ 1 / 2 := by
      have : δ ≤ 1 := by
        calc δ ≤ Real.pi / (2 * (n : ℝ)) := hδ_le_half
          _ ≤ 1 := by rw [div_le_one (by positivity)]; linarith
      linarith
    have hsin_half : (23 / 48 : ℝ) * θ ≤ Real.sin (θ / 2) := by
      have h := sin_ge_23_24 (by linarith : 0 ≤ θ / 2) hθ_half
      linarith
    have hrR : ((r : ℝ) + 1 / 2) ≤ (n : ℝ) := by
      have : (r : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hr
      linarith
    have hsin_r : Real.sin (θ / 2) ≤ Real.sin (((r : ℝ) + 1 / 2) * θ) := by
      apply Real.sin_le_sin_of_le_of_le_pi_div_two
      · linarith
      · calc ((r : ℝ) + 1 / 2) * θ ≤ (n : ℝ) * (Real.pi / (2 * (n : ℝ))) :=
              mul_le_mul hrR (hθδ.trans hδ_le_half) hθ0 (by positivity)
          _ = Real.pi / 2 := by field_simp
      · have : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
        nlinarith
    have hsin_prod : (529 / 2304 : ℝ) * θ ^ 2 ≤
        Real.sin (((r : ℝ) + 1 / 2) * θ) * Real.sin (θ / 2) := by
      have h0 : 0 ≤ (23 / 48 : ℝ) * θ := by positivity
      have h1 : 0 ≤ Real.sin (θ / 2) := le_trans h0 hsin_half
      nlinarith
    have hF_lb : (3 : ℝ) ^ n * (1 - (S2 / 3) * θ ^ 2) ≤ F n θ := by
      have hbern : 1 - (S2 / 3) * θ ^ 2 ≤
          ∏ j ∈ Finset.Icc 1 n, (1 - ((j : ℝ) * θ) ^ 2 / 3) := by
        have hsum_eq : (S2 / 3) * θ ^ 2 =
            ∑ j ∈ Finset.Icc 1 n, ((j : ℝ) * θ) ^ 2 / 3 := by
          have : ∑ j ∈ Finset.Icc 1 n, ((j : ℝ) * θ) ^ 2 / 3 =
              (∑ j ∈ Finset.Icc 1 n, (j : ℝ) ^ 2) * (θ ^ 2 / 3) := by
            rw [sum_mul]
            apply sum_congr rfl
            intro j _
            ring
          rw [this, sum_sq_Icc]
          dsimp [S2]
          ring
        rw [hsum_eq]
        apply bernoulli_prod
        · intro j _; positivity
        · intro j hj
          rw [mem_Icc] at hj
          have hjR : (j : ℝ) ≤ (n : ℝ) := by exact_mod_cast hj.2
          have hjt : (j : ℝ) * θ ≤ Real.pi / 2 := by
            calc (j : ℝ) * θ ≤ (n : ℝ) * (Real.pi / (2 * (n : ℝ))) :=
                  mul_le_mul hjR (hθδ.trans hδ_le_half) hθ0 (by positivity)
              _ = Real.pi / 2 := by field_simp
          have hjt0 : 0 ≤ (j : ℝ) * θ := by positivity
          nlinarith
      have hprod_le : ∏ j ∈ Finset.Icc 1 n, (1 - ((j : ℝ) * θ) ^ 2 / 3) ≤
          ∏ j ∈ Finset.Icc 1 n, ((1 + 2 * Real.cos ((j : ℝ) * θ)) / 3) := by
        apply prod_le_prod
        · intro j hj
          rw [mem_Icc] at hj
          have hjR : (j : ℝ) ≤ (n : ℝ) := by exact_mod_cast hj.2
          have hjt : (j : ℝ) * θ ≤ Real.pi / 2 := by
            calc (j : ℝ) * θ ≤ (n : ℝ) * (Real.pi / (2 * (n : ℝ))) :=
                  mul_le_mul hjR (hθδ.trans hδ_le_half) hθ0 (by positivity)
              _ = Real.pi / 2 := by field_simp
          have hjt0 : 0 ≤ (j : ℝ) * θ := by positivity
          nlinarith
        · intro j _
          have hc := cos_ge_one_sub_sq_div_two (show 0 ≤ (j : ℝ) * θ by positivity)
          linarith
      have hF_div : ∏ j ∈ Finset.Icc 1 n, ((1 + 2 * Real.cos ((j : ℝ) * θ)) / 3) =
          F n θ / (3 : ℝ) ^ n := by
        unfold F
        rw [prod_div_distrib, prod_const]
        simp
      have hcomb := hbern.trans hprod_le
      rw [hF_div, le_div_iff₀ (by positivity)] at hcomb
      linarith
    have h1_nonneg : 0 ≤ 1 - (S2 / 3) * θ ^ 2 := by
      have : θ ^ 2 ≤ δ ^ 2 := by nlinarith
      rw [hδ_sq] at this
      have : (S2 / 3) * θ ^ 2 ≤ (S2 / 3) * (3 / S2) :=
        mul_le_mul_of_nonneg_left this (by positivity)
      have hcancel : (S2 / 3) * (3 / S2) = 1 := by field_simp
      linarith
    have hF_nn : 0 ≤ F n θ := le_trans (by positivity) hF_lb
    dsimp [g]
    calc (3 : ℝ) ^ n * (529 / 2304 : ℝ) * (θ ^ 2 - S2 / 3 * θ ^ 4)
        = ((3 : ℝ) ^ n * (1 - (S2 / 3) * θ ^ 2)) * ((529 / 2304 : ℝ) * θ ^ 2) := by ring
      _ ≤ F n θ * (Real.sin (((r : ℝ) + 1 / 2) * θ) * Real.sin (θ / 2)) :=
          mul_le_mul hF_lb hsin_prod (by positivity) hF_nn
      _ = F n θ * Real.sin (((r : ℝ) + 1 / 2) * θ) * Real.sin (θ / 2) := by ring
  -- Step 3: Evaluate polynomial integral on [0, δ]
  have hint_eval : ∫ θ in (0 : ℝ)..δ, (θ ^ 2 - (S2 / 3) * θ ^ 4) = (2 / 15 : ℝ) * δ ^ 3 := by
    rw [intervalIntegral.integral_sub
        (Continuous.intervalIntegrable (by fun_prop) _ _)
        (Continuous.intervalIntegrable (by fun_prop) _ _),
      intervalIntegral.integral_const_mul, integral_pow, integral_pow]
    have hS2δ : (S2 / 3) * δ ^ 2 = 1 := by rw [hδ_sq]; field_simp
    have : δ ^ 5 = δ ^ 2 * δ ^ 3 := by ring
    rw [this]
    have h1 : (S2 / 3) * (δ ^ 2 * δ ^ 3) = δ ^ 3 := by
      calc (S2 / 3) * (δ ^ 2 * δ ^ 3) = ((S2 / 3) * δ ^ 2) * δ ^ 3 := by ring
        _ = 1 * δ ^ 3 := by rw [hS2δ]
        _ = δ ^ 3 := one_mul _
    norm_num
    linarith
  -- Step 4: Lower bound δ^3 using S2 ≤ (108/289) * n^3
  have hδ_lb : (17 / 6 : ℝ) / ((n : ℝ) * Real.sqrt n) ≤ δ := by
    have hsq : ((17 / 6 : ℝ) / ((n : ℝ) * Real.sqrt n)) ^ 2 ≤ δ ^ 2 := by
      rw [hδ_sq, div_pow, mul_pow, Real.sq_sqrt hn0.le]
      rw [div_le_div_iff₀ (by positivity) hS2_pos]
      have hcube : (n : ℝ) ^ 2 * (n : ℝ) = (n : ℝ) ^ 3 := by ring
      rw [hcube]
      linarith
    have hnn : 0 ≤ (17 / 6 : ℝ) / ((n : ℝ) * Real.sqrt n) := by positivity
    nlinarith
  have hδ3_lb : (4913 / 216 : ℝ) / ((n : ℝ) ^ 4 * Real.sqrt n) ≤ δ ^ 3 := by
    have hpow : ((17 / 6 : ℝ) / ((n : ℝ) * Real.sqrt n)) ^ 3 ≤ δ ^ 3 :=
      pow_le_pow_left₀ (by positivity) hδ_lb 3
    have hsimp : ((17 / 6 : ℝ) / ((n : ℝ) * Real.sqrt n)) ^ 3 =
        (4913 / 216 : ℝ) / ((n : ℝ) ^ 4 * Real.sqrt n) := by
      rw [div_pow, mul_pow]
      have h3 : Real.sqrt (n : ℝ) ^ 3 = (n : ℝ) * Real.sqrt n := by
        rw [pow_succ, Real.sq_sqrt hn0.le]
      rw [h3]
      ring
    rwa [hsimp] at hpow
  rw [hint_eval] at hmain_sub
  have hconst : (2 / 3 : ℝ) ≤ (529 / 2304 : ℝ) * (2 / 15 : ℝ) * (4913 / 216 : ℝ) := by norm_num
  have hfinal : (2 / 3 : ℝ) * (3 : ℝ) ^ n / ((n : ℝ) ^ 4 * Real.sqrt n) ≤
      (3 : ℝ) ^ n * (529 / 2304 : ℝ) * ((2 / 15 : ℝ) * δ ^ 3) := by
    calc (2 / 3 : ℝ) * (3 : ℝ) ^ n / ((n : ℝ) ^ 4 * Real.sqrt n)
        = (2 / 3 : ℝ) * ((3 : ℝ) ^ n / ((n : ℝ) ^ 4 * Real.sqrt n)) := by ring
      _ ≤ ((529 / 2304 : ℝ) * (2 / 15 : ℝ) * (4913 / 216 : ℝ)) *
            ((3 : ℝ) ^ n / ((n : ℝ) ^ 4 * Real.sqrt n)) :=
          mul_le_mul_of_nonneg_right hconst (by positivity)
      _ = (3 : ℝ) ^ n * (529 / 2304 : ℝ) * ((2 / 15 : ℝ) *
            ((4913 / 216 : ℝ) / ((n : ℝ) ^ 4 * Real.sqrt n))) := by ring
      _ ≤ (3 : ℝ) ^ n * (529 / 2304 : ℝ) * ((2 / 15 : ℝ) * δ ^ 3) := by
          gcongr
  linarith

private lemma abs_F_le_piece1 (n : ℕ) (hn : 1 ≤ n) {θ : ℝ}
    (h1 : 2 * Real.pi / (3 * (n : ℝ)) ≤ θ) (h2 : θ ≤ Real.pi / (n : ℝ)) :
    |F n θ| ≤ (31 / 15 : ℝ) ^ n := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by positivity
  have hθ0 : 0 ≤ θ := le_trans (by positivity) h1
  unfold F
  rw [Finset.abs_prod]
  set s := Finset.Icc 1 n
  set A := s.filter (fun j => 2 * j < n)
  set B := s.filter (fun j => n ≤ 2 * j ∧ 4 * j < 3 * n)
  set C := s.filter (fun j => 3 * n ≤ 4 * j)
  have hpart : ∀ j ∈ s, |1 + 2 * Real.cos ((j : ℝ) * θ)| ≤
      if 2 * j < n then (3 : ℝ) else if 4 * j < 3 * n then 2 else 1 := by
    intro j hj
    rw [mem_Icc] at hj
    have hjR : (j : ℝ) ≤ (n : ℝ) := by exact_mod_cast hj.2
    have hjt_le : (j : ℝ) * θ ≤ Real.pi := by
      calc (j : ℝ) * θ ≤ (n : ℝ) * (Real.pi / (n : ℝ)) :=
            mul_le_mul hjR h2 hθ0 (by positivity)
        _ = Real.pi := by field_simp
    have hjt0 : 0 ≤ (j : ℝ) * θ := mul_nonneg (Nat.cast_nonneg j) hθ0
    split_ifs with ha hb
    · rw [abs_le]
      constructor <;> linarith [Real.neg_one_le_cos ((j : ℝ) * θ), Real.cos_le_one ((j : ℝ) * θ)]
    · have hj_ge : (n : ℝ) / 2 ≤ (j : ℝ) := by
        have : n ≤ 2 * j := by omega
        have : (n : ℝ) ≤ 2 * (j : ℝ) := by exact_mod_cast this
        linarith
      have hjt_ge : Real.pi / 3 ≤ (j : ℝ) * θ := by
        calc Real.pi / 3 = ((n : ℝ) / 2) * (2 * Real.pi / (3 * (n : ℝ))) := by field_simp
          _ ≤ (j : ℝ) * θ := mul_le_mul hj_ge h1 (by positivity) (by positivity)
      have hcos : Real.cos ((j : ℝ) * θ) ≤ 1 / 2 := by
        rw [← Real.cos_pi_div_three]
        exact Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) hjt_le hjt_ge
      rw [abs_le]
      constructor <;> linarith [Real.neg_one_le_cos ((j : ℝ) * θ)]
    · have hj_ge : 3 * (n : ℝ) / 4 ≤ (j : ℝ) := by
        have : 3 * n ≤ 4 * j := by omega
        have : 3 * (n : ℝ) ≤ 4 * (j : ℝ) := by exact_mod_cast this
        linarith
      have hjt_ge : Real.pi / 2 ≤ (j : ℝ) * θ := by
        calc Real.pi / 2 = (3 * (n : ℝ) / 4) * (2 * Real.pi / (3 * (n : ℝ))) := by
              field_simp; ring
          _ ≤ (j : ℝ) * θ := mul_le_mul hj_ge h1 (by positivity) (by positivity)
      have hcos : Real.cos ((j : ℝ) * θ) ≤ 0 := by
        rw [← Real.cos_pi_div_two]
        exact Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) hjt_le hjt_ge
      rw [abs_le]
      constructor <;> linarith [Real.neg_one_le_cos ((j : ℝ) * θ)]
  have hprod1 : ∏ j ∈ s, |1 + 2 * Real.cos ((j : ℝ) * θ)| ≤
      ∏ j ∈ s, (if 2 * j < n then (3 : ℝ) else if 4 * j < 3 * n then 2 else 1) :=
    prod_le_prod (fun _ _ => abs_nonneg _) hpart
  have hprod_eq : ∏ j ∈ s, (if 2 * j < n then (3 : ℝ) else if 4 * j < 3 * n then 2 else 1) =
      (3 : ℝ) ^ A.card * (2 : ℝ) ^ B.card := by
    have hdisjAB : Disjoint A B := by
      rw [Finset.disjoint_filter]
      intro j _ h1 h2; omega
    have hdisjABC : Disjoint (A ∪ B) C := by
      rw [Finset.disjoint_left]
      intro j hj1 hj2
      simp only [A, B, C, mem_union, mem_filter] at hj1 hj2
      omega
    have hunion : s = (A ∪ B) ∪ C := by
      ext j
      simp only [A, B, C, mem_union, mem_filter]
      constructor
      · intro hj; by_cases h1 : 2 * j < n
        · exact Or.inl (Or.inl ⟨hj, h1⟩)
        · by_cases h2 : 4 * j < 3 * n
          · exact Or.inl (Or.inr ⟨hj, by omega, h2⟩)
          · exact Or.inr ⟨hj, by omega⟩
      · rintro ((⟨hj, _⟩ | ⟨hj, _⟩) | ⟨hj, _⟩) <;> exact hj
    rw [hunion, prod_union hdisjABC, prod_union hdisjAB]
    have hA : ∏ j ∈ A, (if 2 * j < n then (3 : ℝ) else if 4 * j < 3 * n then 2 else 1) =
        (3 : ℝ) ^ A.card := by
      rw [← prod_const]
      apply prod_congr rfl
      intro j hj
      simp only [A, mem_filter] at hj
      rw [if_pos hj.2]
    have hB : ∏ j ∈ B, (if 2 * j < n then (3 : ℝ) else if 4 * j < 3 * n then 2 else 1) =
        (2 : ℝ) ^ B.card := by
      rw [← prod_const]
      apply prod_congr rfl
      intro j hj
      simp only [B, mem_filter] at hj
      rw [if_neg (by omega), if_pos hj.2.2]
    have hC : ∏ j ∈ C, (if 2 * j < n then (3 : ℝ) else if 4 * j < 3 * n then 2 else 1) = 1 := by
      apply prod_eq_one
      intro j hj
      simp only [C, mem_filter] at hj
      rw [if_neg (by omega), if_neg (by omega)]
    rw [hA, hB, hC, mul_one]
  have hA_card : 2 * A.card ≤ n := by
    have hsub : A ⊆ Finset.Icc 1 ((n - 1) / 2) := by
      intro j hj
      simp only [A, s, mem_filter, mem_Icc] at hj ⊢
      omega
    have hc := card_le_card hsub
    simp at hc
    omega
  have hAB_card : 4 * (A.card + B.card) ≤ 3 * n := by
    have hdisjAB : Disjoint A B := by
      rw [Finset.disjoint_filter]
      intro j _ h1 h2; omega
    have hsub : A ∪ B ⊆ Finset.Icc 1 ((3 * n - 1) / 4) := by
      intro j hj
      simp only [A, B, s, mem_union, mem_filter, mem_Icc] at hj ⊢
      omega
    have hc := card_le_card hsub
    rw [card_union_of_disjoint hdisjAB] at hc
    simp at hc
    omega
  have hpow4 : ((3 : ℝ) ^ A.card * (2 : ℝ) ^ B.card) ^ 4 ≤ ((31 / 15 : ℝ) ^ n) ^ 4 := by
    have hrewrite : ((3 : ℝ) ^ A.card * (2 : ℝ) ^ B.card) ^ 4 =
        (3 / 2 : ℝ) ^ (4 * A.card) * (2 : ℝ) ^ (4 * (A.card + B.card)) := by
      rw [mul_pow, ← pow_mul, ← pow_mul, div_pow, mul_comm A.card 4, mul_comm B.card 4,
        mul_add, pow_add]
      field_simp
    rw [hrewrite]
    have hstep1 : (3 / 2 : ℝ) ^ (4 * A.card) ≤ (3 / 2 : ℝ) ^ (2 * n) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have hstep2 : (2 : ℝ) ^ (4 * (A.card + B.card)) ≤ (2 : ℝ) ^ (3 * n) :=
      pow_le_pow_right₀ (by norm_num) hAB_card
    have hstep3 : (3 / 2 : ℝ) ^ (2 * n) * (2 : ℝ) ^ (3 * n) = (18 : ℝ) ^ n := by
      rw [pow_mul, pow_mul, ← mul_pow]
      norm_num
    have hstep4 : (18 : ℝ) ^ n ≤ ((31 / 15 : ℝ) ^ n) ^ 4 := by
      rw [← pow_mul, mul_comm n 4, pow_mul]
      exact pow_le_pow_left₀ (by norm_num) (by norm_num) n
    exact (mul_le_mul hstep1 hstep2 (by positivity) (by positivity)).trans (by rw [hstep3]; exact hstep4)
  have hle : (3 : ℝ) ^ A.card * (2 : ℝ) ^ B.card ≤ (31 / 15 : ℝ) ^ n := by
    by_contra hlt
    push Not at hlt
    have : ((31 / 15 : ℝ) ^ n) ^ 4 < ((3 : ℝ) ^ A.card * (2 : ℝ) ^ B.card) ^ 4 :=
      pow_lt_pow_left₀ hlt (by positivity) (by norm_num)
    linarith
  exact hprod1.trans (hprod_eq ▸ hle)

private lemma abs_F_le_amgm (n : ℕ) (hn : 1 ≤ n) {θ B : ℝ} (hB : 0 < B)
    (h1 : 0 < Real.sin (θ / 2)) (h2 : 0 < Real.sin θ)
    (hbound : 5 / 3 + (10 / 9) / (2 * (n : ℝ) * Real.sin (θ / 2)) +
      (4 / 9) / (2 * (n : ℝ) * Real.sin θ) ≤ B) :
    |F n θ| ≤ B ^ n := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by positivity
  unfold F
  rw [Finset.abs_prod]
  have hcard : (Finset.Icc 1 n).card = n := by simp
  suffices h : ∏ j ∈ Finset.Icc 1 n, |1 + 2 * Real.cos ((j : ℝ) * θ)| ≤ B ^ (Finset.Icc 1 n).card by
    rwa [hcard] at h
  apply am_gm_prod _ _ hB (fun _ _ => abs_nonneg _)
  rw [hcard]
  have hmaj : ∑ j ∈ Finset.Icc 1 n, |1 + 2 * Real.cos ((j : ℝ) * θ)| ≤
      ∑ j ∈ Finset.Icc 1 n, (5 / 3 + (10 / 9) * Real.cos ((j : ℝ) * θ) +
        (4 / 9) * Real.cos ((j : ℝ) * (2 * θ))) := by
    apply sum_le_sum
    intro j _
    have h := abs_one_add_two_cos_le ((j : ℝ) * θ)
    have heq : 2 * ((j : ℝ) * θ) = (j : ℝ) * (2 * θ) := by ring
    rwa [heq] at h
  rw [sum_add_distrib, sum_add_distrib, sum_const, hcard, nsmul_eq_mul,
    ← mul_sum, ← mul_sum] at hmaj
  have hs1 := sum_cos_le n h1
  have h2t : 2 * θ / 2 = θ := by ring
  have hs2 := sum_cos_le n (by rwa [h2t] : 0 < Real.sin (2 * θ / 2))
  rw [h2t] at hs2
  have hcomb : (n : ℝ) * (5 / 3) + (10 / 9) * ∑ j ∈ Finset.Icc 1 n, Real.cos ((j : ℝ) * θ) +
      (4 / 9) * ∑ j ∈ Finset.Icc 1 n, Real.cos ((j : ℝ) * (2 * θ)) ≤
      (n : ℝ) * (5 / 3 + (10 / 9) / (2 * (n : ℝ) * Real.sin (θ / 2)) +
        (4 / 9) / (2 * (n : ℝ) * Real.sin θ)) := by
    have h1' : (10 / 9 : ℝ) * (1 / (2 * Real.sin (θ / 2))) =
        (n : ℝ) * ((10 / 9) / (2 * (n : ℝ) * Real.sin (θ / 2))) := by field_simp
    have h2' : (4 / 9 : ℝ) * (1 / (2 * Real.sin θ)) =
        (n : ℝ) * ((4 / 9) / (2 * (n : ℝ) * Real.sin θ)) := by field_simp
    have m1 := mul_le_mul_of_nonneg_left hs1 (by norm_num : (0 : ℝ) ≤ 10 / 9)
    have m2 := mul_le_mul_of_nonneg_left hs2 (by norm_num : (0 : ℝ) ≤ 4 / 9)
    linarith
  exact (hmaj.trans hcomb).trans (mul_le_mul_of_nonneg_left hbound hn0.le)

private lemma abs_F_le_piece2a (n : ℕ) (hn : 37 ≤ n) {θ : ℝ}
    (h1 : Real.pi / (n : ℝ) ≤ θ) (h2 : θ ≤ 2 * Real.pi / (n : ℝ)) :
    |F n θ| ≤ (213 / 100 : ℝ) ^ n := by
  have hnR : (37 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hpi1 : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
  have hpi2 : Real.pi < (3.15 : ℝ) := Real.pi_lt_d2
  have hθ0 : 0 ≤ θ := le_trans (by positivity) h1
  have hθ1 : θ ≤ 1 := by
    calc θ ≤ 2 * Real.pi / (n : ℝ) := h2
      _ ≤ 1 := by rw [div_le_one hn0]; linarith
  have hθh : θ / 2 ≤ 1 / 2 := by linarith
  have hs1 : 3 / (n : ℝ) ≤ 2 * Real.sin (θ / 2) := by
    have h := sin_ge_23_24 (by linarith : 0 ≤ θ / 2) hθh
    have : 3 / (n : ℝ) ≤ (23 / 24 : ℝ) * θ := by
      calc 3 / (n : ℝ) ≤ (23 / 24 : ℝ) * (Real.pi / (n : ℝ)) := by
            rw [div_le_iff₀ hn0]
            have : (23 / 24 : ℝ) * (Real.pi / (n : ℝ)) * (n : ℝ) = (23 / 24 : ℝ) * Real.pi := by
              field_simp
            rw [this]; linarith
        _ ≤ (23 / 24 : ℝ) * θ := mul_le_mul_of_nonneg_left h1 (by norm_num)
    linarith
  have hs2 : (26 / 5 : ℝ) / (n : ℝ) ≤ 2 * Real.sin θ := by
    have h := sin_ge_5_6 hθ0 hθ1
    have : (26 / 5 : ℝ) / (n : ℝ) ≤ (5 / 3 : ℝ) * θ := by
      calc (26 / 5 : ℝ) / (n : ℝ) ≤ (5 / 3 : ℝ) * (Real.pi / (n : ℝ)) := by
            rw [div_le_iff₀ hn0]
            have : (5 / 3 : ℝ) * (Real.pi / (n : ℝ)) * (n : ℝ) = (5 / 3 : ℝ) * Real.pi := by
              field_simp
            rw [this]; linarith
        _ ≤ (5 / 3 : ℝ) * θ := mul_le_mul_of_nonneg_left h1 (by norm_num)
    linarith
  have hsin1_pos : 0 < Real.sin (θ / 2) := by
    have : 0 < 3 / (n : ℝ) := by positivity
    linarith
  have hsin2_pos : 0 < Real.sin θ := by
    have : 0 < (26 / 5 : ℝ) / (n : ℝ) := by positivity
    linarith
  apply abs_F_le_amgm n (by omega) (by norm_num) hsin1_pos hsin2_pos
  have hb1 : (10 / 9 : ℝ) / (2 * (n : ℝ) * Real.sin (θ / 2)) ≤ 10 / 27 := by
    have hden : 3 ≤ 2 * (n : ℝ) * Real.sin (θ / 2) := by
      have := mul_le_mul_of_nonneg_left hs1 hn0.le
      have hmul : (n : ℝ) * (3 / (n : ℝ)) = 3 := by field_simp
      linarith
    rw [div_le_iff₀ (by positivity)]
    linarith
  have hb2 : (4 / 9 : ℝ) / (2 * (n : ℝ) * Real.sin θ) ≤ 1 / 11 := by
    have hden : (26 / 5 : ℝ) ≤ 2 * (n : ℝ) * Real.sin θ := by
      have := mul_le_mul_of_nonneg_left hs2 hn0.le
      have hmul : (n : ℝ) * ((26 / 5 : ℝ) / (n : ℝ)) = 26 / 5 := by field_simp
      linarith
    rw [div_le_iff₀ (by positivity)]
    linarith
  linarith

private lemma abs_F_le_piece2b (n : ℕ) (hn : 37 ≤ n) {θ : ℝ}
    (h1 : 2 * Real.pi / (n : ℝ) ≤ θ) (h2 : θ ≤ 5 * Real.pi / (n : ℝ)) :
    |F n θ| ≤ (19 / 10 : ℝ) ^ n := by
  have hnR : (37 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hpi1 : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
  have hpi2 : Real.pi < (3.15 : ℝ) := Real.pi_lt_d2
  have hθ0 : 0 ≤ θ := le_trans (by positivity) h1
  have hθ1 : θ ≤ 1 := by
    calc θ ≤ 5 * Real.pi / (n : ℝ) := h2
      _ ≤ 1 := by rw [div_le_one hn0]; linarith
  have hθh : θ / 2 ≤ 1 / 2 := by linarith
  have hs1 : 6 / (n : ℝ) ≤ 2 * Real.sin (θ / 2) := by
    have h := sin_ge_23_24 (by linarith : 0 ≤ θ / 2) hθh
    have : 6 / (n : ℝ) ≤ (23 / 24 : ℝ) * θ := by
      calc 6 / (n : ℝ) ≤ (23 / 24 : ℝ) * (2 * Real.pi / (n : ℝ)) := by
            rw [div_le_iff₀ hn0]
            have : (23 / 24 : ℝ) * (2 * Real.pi / (n : ℝ)) * (n : ℝ) =
                (23 / 12 : ℝ) * Real.pi := by field_simp; ring
            rw [this]; linarith
        _ ≤ (23 / 24 : ℝ) * θ := mul_le_mul_of_nonneg_left h1 (by norm_num)
    linarith
  have hs2 : 10 / (n : ℝ) ≤ 2 * Real.sin θ := by
    have h := sin_ge_5_6 hθ0 hθ1
    have : 10 / (n : ℝ) ≤ (5 / 3 : ℝ) * θ := by
      calc 10 / (n : ℝ) ≤ (5 / 3 : ℝ) * (2 * Real.pi / (n : ℝ)) := by
            rw [div_le_iff₀ hn0]
            have : (5 / 3 : ℝ) * (2 * Real.pi / (n : ℝ)) * (n : ℝ) =
                (10 / 3 : ℝ) * Real.pi := by field_simp; ring
            rw [this]; linarith
        _ ≤ (5 / 3 : ℝ) * θ := mul_le_mul_of_nonneg_left h1 (by norm_num)
    linarith
  have hsin1_pos : 0 < Real.sin (θ / 2) := by
    have : 0 < 6 / (n : ℝ) := by positivity
    linarith
  have hsin2_pos : 0 < Real.sin θ := by
    have : 0 < 10 / (n : ℝ) := by positivity
    linarith
  apply abs_F_le_amgm n (by omega) (by norm_num) hsin1_pos hsin2_pos
  have hb1 : (10 / 9 : ℝ) / (2 * (n : ℝ) * Real.sin (θ / 2)) ≤ 5 / 27 := by
    have hden : 6 ≤ 2 * (n : ℝ) * Real.sin (θ / 2) := by
      have := mul_le_mul_of_nonneg_left hs1 hn0.le
      have hmul : (n : ℝ) * (6 / (n : ℝ)) = 6 := by field_simp
      linarith
    rw [div_le_iff₀ (by positivity)]
    linarith
  have hb2 : (4 / 9 : ℝ) / (2 * (n : ℝ) * Real.sin θ) ≤ 2 / 45 := by
    have hden : 10 ≤ 2 * (n : ℝ) * Real.sin θ := by
      have := mul_le_mul_of_nonneg_left hs2 hn0.le
      have hmul : (n : ℝ) * (10 / (n : ℝ)) = 10 := by field_simp
      linarith
    rw [div_le_iff₀ (by positivity)]
    linarith
  linarith

private lemma abs_F_le_piece3 (n : ℕ) (hn : 37 ≤ n) {θ : ℝ}
    (h1 : 5 * Real.pi / (n : ℝ) ≤ θ) (h2 : θ ≤ 3 * Real.pi / 4) :
    |F n θ| ≤ (9 / 5 : ℝ) ^ n := by
  have hnR : (37 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hpi0 : 0 < Real.pi := Real.pi_pos
  have hθ0 : 0 ≤ θ := le_trans (by positivity) h1
  have hs1 : 10 / (n : ℝ) ≤ 2 * Real.sin (θ / 2) := by
    have hj := Real.mul_le_sin (by linarith : 0 ≤ θ / 2) (by linarith : θ / 2 ≤ Real.pi / 2)
    have : 10 / (n : ℝ) ≤ 2 * (2 / Real.pi * (θ / 2)) := by
      calc 10 / (n : ℝ) = 2 / Real.pi * (5 * Real.pi / (n : ℝ)) := by field_simp; ring
        _ ≤ 2 / Real.pi * θ := mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = 2 * (2 / Real.pi * (θ / 2)) := by ring
    linarith
  have hden2 : 20 ≤ 2 * (n : ℝ) * Real.sin θ := by
    by_cases hmid : θ ≤ Real.pi / 2
    · have hj := Real.mul_le_sin hθ0 hmid
      have : 20 / (n : ℝ) ≤ 2 * Real.sin θ := by
        calc 20 / (n : ℝ) = 2 * (2 / Real.pi * (5 * Real.pi / (n : ℝ))) := by field_simp; ring
          _ ≤ 2 * (2 / Real.pi * θ) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 (by positivity)) (by norm_num)
          _ ≤ 2 * Real.sin θ := by linarith
      have := mul_le_mul_of_nonneg_left this hn0.le
      have hmul : (n : ℝ) * (20 / (n : ℝ)) = 20 := by field_simp
      linarith
    · push Not at hmid
      have hsin_ge : Real.sqrt 2 / 2 ≤ Real.sin θ := by
        rw [← Real.sin_pi_sub, ← Real.sin_pi_div_four]
        apply Real.sin_le_sin_of_le_of_le_pi_div_two
        · linarith
        · linarith
        · linarith
      have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      have hsqrt_ge : (1 : ℝ) ≤ Real.sqrt 2 := by nlinarith [Real.sqrt_nonneg 2]
      have : (1 : ℝ) ≤ 2 * Real.sin θ := by linarith
      nlinarith
  have hsin1_pos : 0 < Real.sin (θ / 2) := by
    have : 0 < 10 / (n : ℝ) := by positivity
    linarith
  have hsin2_pos : 0 < Real.sin θ := by
    nlinarith
  apply abs_F_le_amgm n (by omega) (by norm_num) hsin1_pos hsin2_pos
  have hb1 : (10 / 9 : ℝ) / (2 * (n : ℝ) * Real.sin (θ / 2)) ≤ 1 / 9 := by
    have hden : 10 ≤ 2 * (n : ℝ) * Real.sin (θ / 2) := by
      have := mul_le_mul_of_nonneg_left hs1 hn0.le
      have hmul : (n : ℝ) * (10 / (n : ℝ)) = 10 := by field_simp
      linarith
    rw [div_le_iff₀ (by positivity)]
    linarith
  have hb2 : (4 / 9 : ℝ) / (2 * (n : ℝ) * Real.sin θ) ≤ 1 / 45 := by
    rw [div_le_iff₀ (by positivity)]
    linarith
  linarith

private lemma abs_F_le_piece4 (n : ℕ) {θ : ℝ}
    (h1 : 3 * Real.pi / 4 ≤ θ) (h2 : θ ≤ Real.pi) :
    |F n θ| ≤ (5 / 3 : ℝ) * (9 / 5 : ℝ) ^ n := by
  have haux : ∀ k : ℕ, |F (2 * k) θ| ≤ (9 / 5 : ℝ) ^ (2 * k) := by
    intro k
    induction k with
    | zero => simp [F_zero]
    | succ k ih =>
      have hstep : F (2 * (k + 1)) θ =
          F (2 * k) θ * ((1 + 2 * Real.cos (((2 * k + 1 : ℕ) : ℝ) * θ)) *
            (1 + 2 * Real.cos (((2 * k + 1 : ℕ) : ℝ) * θ + θ))) := by
        rw [show 2 * (k + 1) = (2 * k + 1) + 1 by omega, F_succ, F_succ, mul_assoc]
        congr 2
        have : (((2 * k + 1 + 1 : ℕ) : ℝ) * θ) = ((2 * k + 1 : ℕ) : ℝ) * θ + θ := by
          push_cast; ring
        rw [this]
      rw [hstep, abs_mul]
      have hp := pair_bound h1 h2 (((2 * k + 1 : ℕ) : ℝ) * θ)
      calc |F (2 * k) θ| * |(1 + 2 * Real.cos (((2 * k + 1 : ℕ) : ℝ) * θ)) *
            (1 + 2 * Real.cos (((2 * k + 1 : ℕ) : ℝ) * θ + θ))|
          ≤ (9 / 5 : ℝ) ^ (2 * k) * (9 / 5 : ℝ) ^ 2 :=
            mul_le_mul ih hp (abs_nonneg _) (by positivity)
        _ = (9 / 5 : ℝ) ^ (2 * (k + 1)) := by rw [← pow_add]; congr 1
  rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · rw [← two_mul]
    have h := haux k
    nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 9 / 5) (2 * k)]
  · rw [F_succ, abs_mul]
    have hfac : |1 + 2 * Real.cos (((2 * k + 1 : ℕ) : ℝ) * θ)| ≤ 3 := by
      rw [abs_le]
      constructor <;> linarith [Real.neg_one_le_cos (((2 * k + 1 : ℕ) : ℝ) * θ),
        Real.cos_le_one (((2 * k + 1 : ℕ) : ℝ) * θ)]
    calc |F (2 * k) θ| * |1 + 2 * Real.cos (((2 * k + 1 : ℕ) : ℝ) * θ)|
        ≤ (9 / 5 : ℝ) ^ (2 * k) * 3 := mul_le_mul (haux k) hfac (abs_nonneg _) (by positivity)
      _ = (5 / 3 : ℝ) * (9 / 5 : ℝ) ^ (2 * k + 1) := by rw [pow_succ]; ring

private lemma abs_integral_piece_le {f : ℝ → ℝ} {a b M : ℝ} (hab : a ≤ b)
    (ha : 0 ≤ a) (hb : b ≤ Real.pi) (hf : Continuous f) (hM : 0 ≤ M)
    (hbound : ∀ θ ∈ Set.Icc a b, |f θ| ≤ M) (r : ℕ) :
    |∫ θ in a..b, f θ * Real.sin (((r : ℝ) + 1 / 2) * θ) * Real.sin (θ / 2)| ≤
      M * ∫ θ in a..b, Real.sin (θ / 2) := by
  have h1 : |∫ θ in a..b, f θ * Real.sin (((r : ℝ) + 1 / 2) * θ) * Real.sin (θ / 2)| ≤
      ∫ θ in a..b, |f θ * Real.sin (((r : ℝ) + 1 / 2) * θ) * Real.sin (θ / 2)| :=
    intervalIntegral.abs_integral_le_integral_abs hab
  have h2 : ∫ θ in a..b, |f θ * Real.sin (((r : ℝ) + 1 / 2) * θ) * Real.sin (θ / 2)| ≤
      ∫ θ in a..b, M * Real.sin (θ / 2) := by
    have hi1 : IntervalIntegrable
        (fun θ => |f θ * Real.sin (((r : ℝ) + 1 / 2) * θ) * Real.sin (θ / 2)|)
        MeasureTheory.volume a b :=
      (((hf.mul (by fun_prop)).mul (by fun_prop)).abs).intervalIntegrable a b
    have hi2 : IntervalIntegrable (fun θ => M * Real.sin (θ / 2)) MeasureTheory.volume a b :=
      (continuous_const.mul (by fun_prop)).intervalIntegrable a b
    apply intervalIntegral.integral_mono_on hab hi1 hi2
    intro θ hθ
    rw [abs_mul, abs_mul]
    have hs_nn : 0 ≤ Real.sin (θ / 2) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2])
    rw [abs_of_nonneg hs_nn]
    have hsin1 : |Real.sin (((r : ℝ) + 1 / 2) * θ)| ≤ 1 := Real.abs_sin_le_one _
    have hfM := hbound θ hθ
    calc |f θ| * |Real.sin (((r : ℝ) + 1 / 2) * θ)| * Real.sin (θ / 2)
        ≤ M * 1 * Real.sin (θ / 2) := by
          apply mul_le_mul_of_nonneg_right _ hs_nn
          exact mul_le_mul hfM hsin1 (abs_nonneg _) hM
      _ = M * Real.sin (θ / 2) := by ring
  rw [intervalIntegral.integral_const_mul] at h2
  exact h1.trans h2

private lemma tail_integral_ub (n r : ℕ) (hn : 37 ≤ n) :
    |∫ θ in (2 * Real.pi / (3 * (n : ℝ)))..Real.pi,
        F n θ * Real.sin (((r : ℝ) + 1 / 2) * θ) * Real.sin (θ / 2)| ≤
      3 / (n : ℝ) ^ 2 * (31 / 15 : ℝ) ^ n +
      10 / (n : ℝ) ^ 2 * (213 / 100 : ℝ) ^ n +
      63 / (n : ℝ) ^ 2 * (19 / 10 : ℝ) ^ n +
      (10 / 3 : ℝ) * (9 / 5 : ℝ) ^ n := by
  have hnR : (37 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hpi0 : 0 < Real.pi := Real.pi_pos
  have hpi2 : Real.pi < (3.15 : ℝ) := Real.pi_lt_d2
  have hpi_sq : Real.pi ^ 2 < 10 := by nlinarith
  set g : ℝ → ℝ := fun θ => F n θ * Real.sin (((r : ℝ) + 1 / 2) * θ) * Real.sin (θ / 2)
  have hg : Continuous g := ((continuous_F n).mul (by fun_prop)).mul (by fun_prop)
  set x0 := 2 * Real.pi / (3 * (n : ℝ))
  set x1 := Real.pi / (n : ℝ)
  set x2 := 2 * Real.pi / (n : ℝ)
  set x3 := 5 * Real.pi / (n : ℝ)
  set x4 := 3 * Real.pi / 4
  set x5 := Real.pi
  have hx0 : 0 ≤ x0 := by positivity
  have h01 : x0 ≤ x1 := by
    dsimp [x0, x1]; rw [div_le_div_iff₀ (by positivity) hn0]; nlinarith
  have h12 : x1 ≤ x2 := by
    dsimp [x1, x2]; rw [div_le_div_iff₀ hn0 hn0]; nlinarith
  have h23 : x2 ≤ x3 := by
    dsimp [x2, x3]; rw [div_le_div_iff₀ hn0 hn0]; nlinarith
  have h34 : x3 ≤ x4 := by
    dsimp [x3, x4]; rw [div_le_div_iff₀ hn0 (by norm_num)]; nlinarith
  have h45 : x4 ≤ x5 := by dsimp [x4, x5]; linarith
  have hsplit : ∫ θ in x0..x5, g θ =
      (∫ θ in x0..x1, g θ) + (∫ θ in x1..x2, g θ) + (∫ θ in x2..x3, g θ) +
      (∫ θ in x3..x4, g θ) + (∫ θ in x4..x5, g θ) := by
    have s1 : ∫ θ in x0..x5, g θ = (∫ θ in x0..x1, g θ) + ∫ θ in x1..x5, g θ :=
      (intervalIntegral.integral_add_adjacent_intervals
        (hg.intervalIntegrable x0 x1) (hg.intervalIntegrable x1 x5)).symm
    have s2 : ∫ θ in x1..x5, g θ = (∫ θ in x1..x2, g θ) + ∫ θ in x2..x5, g θ :=
      (intervalIntegral.integral_add_adjacent_intervals
        (hg.intervalIntegrable x1 x2) (hg.intervalIntegrable x2 x5)).symm
    have s3 : ∫ θ in x2..x5, g θ = (∫ θ in x2..x3, g θ) + ∫ θ in x3..x5, g θ :=
      (intervalIntegral.integral_add_adjacent_intervals
        (hg.intervalIntegrable x2 x3) (hg.intervalIntegrable x3 x5)).symm
    have s4 : ∫ θ in x3..x5, g θ = (∫ θ in x3..x4, g θ) + ∫ θ in x4..x5, g θ :=
      (intervalIntegral.integral_add_adjacent_intervals
        (hg.intervalIntegrable x3 x4) (hg.intervalIntegrable x4 x5)).symm
    linarith
  have hp1 : |∫ θ in x0..x1, g θ| ≤ 3 / (n : ℝ) ^ 2 * (31 / 15 : ℝ) ^ n := by
    have ha := abs_integral_piece_le h01 hx0 (h12.trans (h23.trans (h34.trans h45)))
      (continuous_F n) (by positivity)
      (fun θ hθ => abs_F_le_piece1 n (by omega) hθ.1 hθ.2) r
    have hi := integral_sin_half_le_sq hx0 h01
    have hsq : x1 ^ 2 / 4 ≤ 3 / (n : ℝ) ^ 2 := by
      dsimp [x1]; rw [div_pow, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [sq_nonneg (n : ℝ)]
    have hcomb := ha.trans (mul_le_mul_of_nonneg_left (hi.trans hsq) (by positivity))
    linarith
  have hp2a : |∫ θ in x1..x2, g θ| ≤ 10 / (n : ℝ) ^ 2 * (213 / 100 : ℝ) ^ n := by
    have ha := abs_integral_piece_le h12 (hx0.trans h01) (h23.trans (h34.trans h45))
      (continuous_F n) (by positivity)
      (fun θ hθ => abs_F_le_piece2a n hn hθ.1 hθ.2) r
    have hi := integral_sin_half_le_sq (hx0.trans h01) h12
    have hsq : x2 ^ 2 / 4 ≤ 10 / (n : ℝ) ^ 2 := by
      dsimp [x2]; rw [div_pow, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [sq_nonneg (n : ℝ)]
    have hcomb := ha.trans (mul_le_mul_of_nonneg_left (hi.trans hsq) (by positivity))
    linarith
  have hp2b : |∫ θ in x2..x3, g θ| ≤ 63 / (n : ℝ) ^ 2 * (19 / 10 : ℝ) ^ n := by
    have ha := abs_integral_piece_le h23 (hx0.trans (h01.trans h12)) (h34.trans h45)
      (continuous_F n) (by positivity)
      (fun θ hθ => abs_F_le_piece2b n hn hθ.1 hθ.2) r
    have hi := integral_sin_half_le_sq (hx0.trans (h01.trans h12)) h23
    have hsq : x3 ^ 2 / 4 ≤ 63 / (n : ℝ) ^ 2 := by
      dsimp [x3]; rw [div_pow, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [sq_nonneg (n : ℝ)]
    have hcomb := ha.trans (mul_le_mul_of_nonneg_left (hi.trans hsq) (by positivity))
    linarith
  have hp3 : |∫ θ in x3..x4, g θ| ≤ 2 * (9 / 5 : ℝ) ^ n := by
    have ha := abs_integral_piece_le h34 (hx0.trans (h01.trans (h12.trans h23))) h45
      (continuous_F n) (by positivity)
      (fun θ hθ => abs_F_le_piece3 n hn hθ.1 hθ.2) r
    have hi : ∫ θ in x3..x4, Real.sin (θ / 2) ≤ 2 := by
      rw [integral_sin_half]
      have hc1 : Real.cos (x3 / 2) ≤ 1 := Real.cos_le_one _
      have hc2 : 0 ≤ Real.cos (x4 / 2) := by
        apply Real.cos_nonneg_of_mem_Icc
        constructor <;> linarith
      linarith
    have hcomb := ha.trans (mul_le_mul_of_nonneg_left hi (by positivity))
    linarith
  have hp4 : |∫ θ in x4..x5, g θ| ≤ (4 / 3 : ℝ) * (9 / 5 : ℝ) ^ n := by
    have ha := abs_integral_piece_le h45 (by dsimp [x4]; positivity) le_rfl
      (continuous_F n) (by positivity)
      (fun θ hθ => abs_F_le_piece4 n hθ.1 hθ.2) r
    have hi : ∫ θ in x4..x5, Real.sin (θ / 2) ≤ 4 / 5 := by
      rw [integral_sin_half]
      have hx4 : x4 / 2 = 3 * Real.pi / 8 := by dsimp [x4]; ring
      have hx5 : x5 / 2 = Real.pi / 2 := rfl
      rw [hx4, hx5, Real.cos_pi_div_two]
      linarith [cos_three_pi_div_eight_le]
    have hcomb := ha.trans (mul_le_mul_of_nonneg_left hi (by positivity))
    linarith
  rw [hsplit]
  have htri1 := abs_add_le
    ((((∫ θ in x0..x1, g θ) + ∫ θ in x1..x2, g θ) + ∫ θ in x2..x3, g θ) + ∫ θ in x3..x4, g θ)
    (∫ θ in x4..x5, g θ)
  have htri2 := abs_add_le
    (((∫ θ in x0..x1, g θ) + ∫ θ in x1..x2, g θ) + ∫ θ in x2..x3, g θ)
    (∫ θ in x3..x4, g θ)
  have htri3 := abs_add_le
    ((∫ θ in x0..x1, g θ) + ∫ θ in x1..x2, g θ)
    (∫ θ in x2..x3, g θ)
  have htri4 := abs_add_le (∫ θ in x0..x1, g θ) (∫ θ in x1..x2, g θ)
  linarith

private lemma pow_mul_lt_pow {K a b : ℝ} {k N : ℕ} (hN : 1 ≤ N) (hK : 0 < K) (ha : 0 ≤ a)
    (hb : 0 < b) (hstep : ((N + 1 : ℝ) / (N : ℝ)) ^ k * a ≤ b)
    (hbase : K * (N : ℝ) ^ k * a ^ N < b ^ N) :
    ∀ n ≥ N, K * (n : ℝ) ^ k * a ^ n < b ^ n := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => exact hbase
  | succ m hm ih =>
    have hm0 : (0 : ℝ) < (m : ℝ) := by
      have : 1 ≤ m := le_trans hN hm
      positivity
    have hN0 : (0 : ℝ) < (N : ℝ) := by positivity
    have hratio : ((m + 1 : ℕ) : ℝ) / (m : ℝ) ≤ (N + 1 : ℝ) / (N : ℝ) := by
      push_cast
      rw [div_le_div_iff₀ hm0 hN0]
      have hmN : (N : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      linarith
    have hstep_m : (((m + 1 : ℕ) : ℝ) / (m : ℝ)) ^ k * a ≤ b := by
      have hpow : (((m + 1 : ℕ) : ℝ) / (m : ℝ)) ^ k ≤ ((N + 1 : ℝ) / (N : ℝ)) ^ k :=
        pow_le_pow_left₀ (by positivity) hratio k
      exact (mul_le_mul_of_nonneg_right hpow ha).trans hstep
    have hrew : K * ((m + 1 : ℕ) : ℝ) ^ k * a ^ (m + 1) =
        (K * (m : ℝ) ^ k * a ^ m) * ((((m + 1 : ℕ) : ℝ) / (m : ℝ)) ^ k * a) := by
      rw [pow_succ, div_pow]
      field_simp
    rw [hrew, pow_succ]
    calc (K * (m : ℝ) ^ k * a ^ m) * ((((m + 1 : ℕ) : ℝ) / (m : ℝ)) ^ k * a)
        ≤ (K * (m : ℝ) ^ k * a ^ m) * b :=
          mul_le_mul_of_nonneg_left hstep_m (by positivity)
      _ < b ^ m * b := mul_lt_mul_of_pos_right ih hb

private lemma tail_lt_main (n : ℕ) (hn : 37 ≤ n) :
    3 / (n : ℝ) ^ 2 * (31 / 15 : ℝ) ^ n +
    10 / (n : ℝ) ^ 2 * (213 / 100 : ℝ) ^ n +
    63 / (n : ℝ) ^ 2 * (19 / 10 : ℝ) ^ n +
    (10 / 3 : ℝ) * (9 / 5 : ℝ) ^ n <
    (2 / 3 : ℝ) * (3 : ℝ) ^ n / ((n : ℝ) ^ 4 * Real.sqrt n) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by positivity
  have hsqrt_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
  have hsq_n : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt hn0.le
  have hden_pos : 0 < (n : ℝ) ^ 4 * Real.sqrt n := by positivity
  have h9 : ((3 : ℝ) ^ n) ^ 2 = (9 : ℝ) ^ n := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  set M : ℝ := (2 / 3 : ℝ) * (3 : ℝ) ^ n / ((n : ℝ) ^ 4 * Real.sqrt n)
  have h1 : 3 / (n : ℝ) ^ 2 * (31 / 15 : ℝ) ^ n < (1 / 10 : ℝ) * M := by
    have hsq := pow_mul_lt_pow (K := 2025) (a := 961 / 225) (b := 9) (k := 5) (N := 37)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) n hn
    dsimp [M]
    rw [← mul_div_assoc, lt_div_iff₀ hden_pos]
    have hrew : 3 / (n : ℝ) ^ 2 * (31 / 15 : ℝ) ^ n * ((n : ℝ) ^ 4 * Real.sqrt n) =
        3 * (n : ℝ) ^ 2 * Real.sqrt n * (31 / 15 : ℝ) ^ n := by field_simp
    rw [hrew]
    have hsq_lt : (3 * (n : ℝ) ^ 2 * Real.sqrt n * (31 / 15 : ℝ) ^ n) ^ 2 <
        ((1 / 10 : ℝ) * ((2 / 3 : ℝ) * (3 : ℝ) ^ n)) ^ 2 := by
      have ha : ((31 / 15 : ℝ) ^ n) ^ 2 = (961 / 225 : ℝ) ^ n := by
        rw [← pow_mul, mul_comm, pow_mul]; norm_num
      simp only [mul_pow, hsq_n, h9, ha]
      have hl : (3 : ℝ) ^ 2 * ((n : ℝ) ^ 2) ^ 2 * (n : ℝ) * (961 / 225 : ℝ) ^ n =
          (1 / 225 : ℝ) * (2025 * (n : ℝ) ^ 5 * (961 / 225 : ℝ) ^ n) := by ring
      have hr : (1 / 10 : ℝ) ^ 2 * ((2 / 3 : ℝ) ^ 2 * (9 : ℝ) ^ n) =
          (1 / 225 : ℝ) * (9 : ℝ) ^ n := by ring
      linarith
    nlinarith [show 0 ≤ 3 * (n : ℝ) ^ 2 * Real.sqrt n * (31 / 15 : ℝ) ^ n by positivity,
      show 0 ≤ (1 / 10 : ℝ) * ((2 / 3 : ℝ) * (3 : ℝ) ^ n) by positivity]
  have h2a : 10 / (n : ℝ) ^ 2 * (213 / 100 : ℝ) ^ n < (2 / 5 : ℝ) * M := by
    have hsq := pow_mul_lt_pow (K := 5625 / 4) (a := 45369 / 10000) (b := 9) (k := 5) (N := 37)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) n hn
    dsimp [M]
    rw [← mul_div_assoc, lt_div_iff₀ hden_pos]
    have hrew : 10 / (n : ℝ) ^ 2 * (213 / 100 : ℝ) ^ n * ((n : ℝ) ^ 4 * Real.sqrt n) =
        10 * (n : ℝ) ^ 2 * Real.sqrt n * (213 / 100 : ℝ) ^ n := by field_simp
    rw [hrew]
    have hsq_lt : (10 * (n : ℝ) ^ 2 * Real.sqrt n * (213 / 100 : ℝ) ^ n) ^ 2 <
        ((2 / 5 : ℝ) * ((2 / 3 : ℝ) * (3 : ℝ) ^ n)) ^ 2 := by
      have ha : ((213 / 100 : ℝ) ^ n) ^ 2 = (45369 / 10000 : ℝ) ^ n := by
        rw [← pow_mul, mul_comm, pow_mul]; norm_num
      simp only [mul_pow, hsq_n, h9, ha]
      have hl : (10 : ℝ) ^ 2 * ((n : ℝ) ^ 2) ^ 2 * (n : ℝ) * (45369 / 10000 : ℝ) ^ n =
          (16 / 225 : ℝ) * (5625 / 4 * (n : ℝ) ^ 5 * (45369 / 10000 : ℝ) ^ n) := by ring
      have hr : (2 / 5 : ℝ) ^ 2 * ((2 / 3 : ℝ) ^ 2 * (9 : ℝ) ^ n) =
          (16 / 225 : ℝ) * (9 : ℝ) ^ n := by ring
      linarith
    nlinarith [show 0 ≤ 10 * (n : ℝ) ^ 2 * Real.sqrt n * (213 / 100 : ℝ) ^ n by positivity,
      show 0 ≤ (2 / 5 : ℝ) * ((2 / 3 : ℝ) * (3 : ℝ) ^ n) by positivity]
  have h2b : 63 / (n : ℝ) ^ 2 * (19 / 10 : ℝ) ^ n < (1 / 10 : ℝ) * M := by
    have hsq := pow_mul_lt_pow (K := 893025) (a := 361 / 100) (b := 9) (k := 5) (N := 37)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) n hn
    dsimp [M]
    rw [← mul_div_assoc, lt_div_iff₀ hden_pos]
    have hrew : 63 / (n : ℝ) ^ 2 * (19 / 10 : ℝ) ^ n * ((n : ℝ) ^ 4 * Real.sqrt n) =
        63 * (n : ℝ) ^ 2 * Real.sqrt n * (19 / 10 : ℝ) ^ n := by field_simp
    rw [hrew]
    have hsq_lt : (63 * (n : ℝ) ^ 2 * Real.sqrt n * (19 / 10 : ℝ) ^ n) ^ 2 <
        ((1 / 10 : ℝ) * ((2 / 3 : ℝ) * (3 : ℝ) ^ n)) ^ 2 := by
      have ha : ((19 / 10 : ℝ) ^ n) ^ 2 = (361 / 100 : ℝ) ^ n := by
        rw [← pow_mul, mul_comm, pow_mul]; norm_num
      simp only [mul_pow, hsq_n, h9, ha]
      have hl : (63 : ℝ) ^ 2 * ((n : ℝ) ^ 2) ^ 2 * (n : ℝ) * (361 / 100 : ℝ) ^ n =
          (1 / 225 : ℝ) * (893025 * (n : ℝ) ^ 5 * (361 / 100 : ℝ) ^ n) := by ring
      have hr : (1 / 10 : ℝ) ^ 2 * ((2 / 3 : ℝ) ^ 2 * (9 : ℝ) ^ n) =
          (1 / 225 : ℝ) * (9 : ℝ) ^ n := by ring
      linarith
    nlinarith [show 0 ≤ 63 * (n : ℝ) ^ 2 * Real.sqrt n * (19 / 10 : ℝ) ^ n by positivity,
      show 0 ≤ (1 / 10 : ℝ) * ((2 / 3 : ℝ) * (3 : ℝ) ^ n) by positivity]
  have h34 : (10 / 3 : ℝ) * (9 / 5 : ℝ) ^ n < (2 / 5 : ℝ) * M := by
    have hsq := pow_mul_lt_pow (K := 625 / 4) (a := 81 / 25) (b := 9) (k := 9) (N := 37)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) n hn
    dsimp [M]
    rw [← mul_div_assoc, lt_div_iff₀ hden_pos]
    have hsq_lt : ((10 / 3 : ℝ) * (9 / 5 : ℝ) ^ n * ((n : ℝ) ^ 4 * Real.sqrt n)) ^ 2 <
        ((2 / 5 : ℝ) * ((2 / 3 : ℝ) * (3 : ℝ) ^ n)) ^ 2 := by
      have ha : ((9 / 5 : ℝ) ^ n) ^ 2 = (81 / 25 : ℝ) ^ n := by
        rw [← pow_mul, mul_comm, pow_mul]; norm_num
      simp only [mul_pow, hsq_n, h9, ha]
      have hl : (10 / 3 : ℝ) ^ 2 * (81 / 25 : ℝ) ^ n * (((n : ℝ) ^ 4) ^ 2 * (n : ℝ)) =
          (16 / 225 : ℝ) * (625 / 4 * (n : ℝ) ^ 9 * (81 / 25 : ℝ) ^ n) := by ring
      have hr : (2 / 5 : ℝ) ^ 2 * ((2 / 3 : ℝ) ^ 2 * (9 : ℝ) ^ n) =
          (16 / 225 : ℝ) * (9 : ℝ) ^ n := by ring
      linarith
    nlinarith [show 0 ≤ (10 / 3 : ℝ) * (9 / 5 : ℝ) ^ n * ((n : ℝ) ^ 4 * Real.sqrt n) by positivity,
      show 0 ≤ (2 / 5 : ℝ) * ((2 / 3 : ℝ) * (3 : ℝ) ^ n) by positivity]
  linarith

private lemma peak_inc_large (n : ℕ) (hn : 37 ≤ n) :
    ∀ k, (n - 1) * n / 2 ≤ k → k < n * (n + 1) / 2 →
      (P n).coeff k < (P n).coeff (k + 1) := by
  intro k hk1 hk2
  set r := n * (n + 1) / 2 - 1 - k
  have hr_lt_n : r < n := by
    have h1 := two_mul_half (n - 1)
    have h2 := two_mul_half n
    have h3 : (n - 1) * n + 2 * n = n * (n + 1) := by
      cases n with
      | zero => omega
      | succ m => simp; ring
    omega
  have hr_lt_M : r < n * (n + 1) / 2 := by omega
  have hdiff := integral_F_diff n r hr_lt_M
  set g : ℝ → ℝ := fun θ => F n θ * Real.sin (((r : ℝ) + 1 / 2) * θ) * Real.sin (θ / 2)
  have hg : Continuous g := ((continuous_F n).mul (by fun_prop)).mul (by fun_prop)
  have hsplit : ∫ θ in (0 : ℝ)..Real.pi, g θ =
      (∫ θ in (0 : ℝ)..(2 * Real.pi / (3 * (n : ℝ))), g θ) +
      (∫ θ in (2 * Real.pi / (3 * (n : ℝ)))..Real.pi, g θ) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hg.intervalIntegrable 0 (2 * Real.pi / (3 * (n : ℝ))))
      (hg.intervalIntegrable (2 * Real.pi / (3 * (n : ℝ))) Real.pi)).symm
  have hlb := main_integral_lb n r hn hr_lt_n
  have hub := tail_integral_ub n r hn
  have hcmp := tail_lt_main n hn
  have hneg : -(∫ θ in (2 * Real.pi / (3 * (n : ℝ)))..Real.pi, g θ) ≤
      |∫ θ in (2 * Real.pi / (3 * (n : ℝ)))..Real.pi, g θ| := neg_le_abs _
  have hpos : 0 < ∫ θ in (0 : ℝ)..Real.pi, g θ := by linarith
  have hpi_diff : 0 < Real.pi * (((P n).coeff (n * (n + 1) / 2 - r) : ℝ) -
      ((P n).coeff (n * (n + 1) / 2 - r - 1) : ℝ)) := by
    rw [hdiff]
    linarith
  have hreal_lt : ((P n).coeff (n * (n + 1) / 2 - r - 1) : ℝ) <
      ((P n).coeff (n * (n + 1) / 2 - r) : ℝ) := by
    nlinarith [Real.pi_pos]
  have hnat_lt : (P n).coeff (n * (n + 1) / 2 - r - 1) < (P n).coeff (n * (n + 1) / 2 - r) :=
    Nat.cast_lt.mp hreal_lt
  have heq1 : n * (n + 1) / 2 - r - 1 = k := by omega
  have heq2 : n * (n + 1) / 2 - r = k + 1 := by omega
  rwa [heq1, heq2] at hnat_lt

/-! ### Section 6: Global strict monotonicity and Wu's three conjectures -/

private lemma strict_inc_all (n : ℕ) (hn : 11 ≤ n) :
    ∀ k, 3 ≤ k → k < n * (n + 1) / 2 → (P n).coeff k < (P n).coeff (k + 1) := by
  induction n, hn using Nat.le_induction with
  | base => exact strict_inc_P11
  | succ n hn ih =>
    have hweak : ∀ j, j < n * (n + 1) / 2 → (P n).coeff j ≤ (P n).coeff (j + 1) := by
      intro j hj
      by_cases h3 : 3 ≤ j
      · exact le_of_lt (ih j h3 hj)
      · rcases coeff_P_small n (by omega) with ⟨h0, h1, h2, h3'⟩
        interval_cases j <;> simp only [Nat.reduceAdd, h0, h1, h2, h3'] <;> omega
    intro k hk1 hk2
    by_cases hlow : k < n * (n + 1) / 2
    · rw [coeff_P_succ, coeff_P_succ]
      have h0 : (P n).coeff k < (P n).coeff (k + 1) := ih k hk1 hlow
      have h1 : (if n + 1 ≤ k then (P n).coeff (k - (n + 1)) else 0) ≤
          (if n + 1 ≤ k + 1 then (P n).coeff (k + 1 - (n + 1)) else 0) := by
        split_ifs with ha hb hb
        · have hsub : k + 1 - (n + 1) = k - (n + 1) + 1 := by omega
          rw [hsub]
          exact hweak (k - (n + 1)) (by omega)
        · omega
        · exact Nat.zero_le _
        · exact le_rfl
      have h2 : (if 2 * (n + 1) ≤ k then (P n).coeff (k - 2 * (n + 1)) else 0) ≤
          (if 2 * (n + 1) ≤ k + 1 then (P n).coeff (k + 1 - 2 * (n + 1)) else 0) := by
        split_ifs with ha hb hb
        · have hsub : k + 1 - 2 * (n + 1) = k - 2 * (n + 1) + 1 := by omega
          rw [hsub]
          exact hweak (k - 2 * (n + 1)) (by omega)
        · omega
        · exact Nat.zero_le _
        · exact le_rfl
      omega
    · push Not at hlow
      by_cases hsmall : n + 1 ≤ 36
      · exact peak_inc_small (n + 1) (by omega) hsmall k (by simpa using hlow) hk2
      · exact peak_inc_large (n + 1) (by omega) k (by simpa using hlow) hk2

private lemma a_eq_formula_ge11 (n : ℕ) (hn : 11 ≤ n) :
    a n = n * (n + 1) / 2 - 1 := by
  unfold a
  set M := n * (n + 1) / 2
  have h2M : 2 * M = n * (n + 1) := two_mul_half n
  have hM3 : 3 ≤ M := by
    have : 11 * 12 ≤ n * (n + 1) := Nat.mul_le_mul hn (by omega)
    omega
  rcases coeff_P_small n (by omega) with ⟨hc0, hc1, hc2, hc3⟩
  have hstrict := strict_inc_all n hn
  have hstrict_lt : ∀ i j, 3 ≤ i → i < j → j ≤ M → (P n).coeff i < (P n).coeff j := by
    intro i j hi hij hj
    induction j with
    | zero => omega
    | succ j ih =>
      by_cases heq : i = j
      · subst heq
        exact hstrict i hi (by omega)
      · exact lt_trans (ih (by omega) (by omega)) (hstrict j (by omega) (by omega))
  set T : Finset ℕ := insert 1 (Finset.Icc 3 M)
  have himg : ((Finset.range ((P n).natDegree + 1)).image (P n).coeff) = T.image (P n).coeff := by
    ext v
    simp only [mem_image, mem_range, T, mem_insert, mem_Icc, natDegree_P]
    constructor
    · rintro ⟨k, hk, rfl⟩
      have hk' : k ≤ n * (n + 1) := by omega
      have hred : ∃ j ≤ M, (P n).coeff j = (P n).coeff k := by
        by_cases hkm : k ≤ M
        · exact ⟨k, hkm, rfl⟩
        · exact ⟨n * (n + 1) - k, by omega, coeff_P_symm n k hk'⟩
      rcases hred with ⟨j, hjM, hj⟩
      by_cases hj3 : 3 ≤ j
      · exact ⟨j, Or.inr ⟨hj3, hjM⟩, hj⟩
      · interval_cases j
        · exact ⟨1, Or.inl rfl, by omega⟩
        · exact ⟨1, Or.inl rfl, hj⟩
        · exact ⟨3, Or.inr ⟨le_rfl, hM3⟩, by omega⟩
    · rintro ⟨j, hj, rfl⟩
      refine ⟨j, ?_, rfl⟩
      rcases hj with rfl | ⟨_, hjM⟩ <;> omega
  have hinj : Set.InjOn (P n).coeff (T : Set ℕ) := by
    intro x hx y hy hxy
    simp only [T, Finset.mem_coe, mem_insert, mem_Icc] at hx hy
    rcases hx with rfl | ⟨hx3, hxM⟩ <;> rcases hy with rfl | ⟨hy3, hyM⟩
    · rfl
    · exfalso
      have hgt : (P n).coeff 3 ≤ (P n).coeff y := by
        by_cases h3y : 3 = y
        · rw [h3y]
        · exact le_of_lt (hstrict_lt 3 y le_rfl (by omega) hyM)
      omega
    · exfalso
      have hgt : (P n).coeff 3 ≤ (P n).coeff x := by
        by_cases h3x : 3 = x
        · rw [h3x]
        · exact le_of_lt (hstrict_lt 3 x le_rfl (by omega) hxM)
      omega
    · by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact ne_of_lt (hstrict_lt x y hx3 hlt hyM) hxy
      · exact ne_of_gt (hstrict_lt y x hy3 hgt hxM) hxy
  rw [himg, Finset.card_image_of_injOn hinj]
  have h1not : (1 : ℕ) ∉ Finset.Icc 3 M := by simp
  rw [card_insert_of_notMem h1not, Nat.card_Icc]
  omega

private lemma a_eq_formula (n : ℕ) (hn : 9 ≤ n) :
    a n = n * (n + 1) / 2 - 1 := by
  by_cases h11 : 11 ≤ n
  · exact a_eq_formula_ge11 n h11
  · interval_cases n
    · rw [a_9]
    · rw [a_10]

private lemma a_recurrence (n : ℕ) (hn : 12 ≤ n) :
    (a n : ℤ) = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  have hsub1 : 12 + m - 1 = 11 + m := by omega
  have hsub2 : 12 + m - 2 = 10 + m := by omega
  have hsub3 : 12 + m - 3 = 9 + m := by omega
  rw [hsub1, hsub2, hsub3]
  have hform : ∀ k ≥ 9, (2 : ℤ) * (a k : ℤ) = (k : ℤ) * ((k : ℤ) + 1) - 2 := by
    intro k hk
    have hf := a_eq_formula k hk
    have he := two_mul_half k
    have hpos : 1 ≤ k * (k + 1) / 2 := by
      have : 9 * 10 ≤ k * (k + 1) := Nat.mul_le_mul hk (by omega)
      omega
    have hnat : 2 * a k + 2 = k * (k + 1) := by omega
    have hint : (2 : ℤ) * (a k : ℤ) + 2 = (k : ℤ) * ((k : ℤ) + 1) := by exact_mod_cast hnat
    linarith
  have q0 := hform (12 + m) (by omega)
  have q1 := hform (11 + m) (by omega)
  have q2 := hform (10 + m) (by omega)
  have q3 := hform (9 + m) (by omega)
  push_cast at q0 q1 q2 q3
  linarith

private lemma a_gf :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (PowerSeries.X - 1) ^ 3 =
      PowerSeries.X * (-PowerSeries.X ^ 10 + 2 * PowerSeries.X ^ 9 - PowerSeries.X ^ 8 -
        2 * PowerSeries.X ^ 7 + 4 * PowerSeries.X ^ 6 - PowerSeries.X ^ 5 -
        2 * PowerSeries.X ^ 3 + PowerSeries.X - 1) := by
  set f : ℕ → ℚ := fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)
  have hLHS : PowerSeries.mk f * (PowerSeries.X - 1) ^ 3 =
      PowerSeries.mk f * PowerSeries.X ^ 3 -
      (3 : ℚ) • (PowerSeries.mk f * PowerSeries.X ^ 2) +
      (3 : ℚ) • (PowerSeries.mk f * PowerSeries.X ^ 1) -
      PowerSeries.mk f := by
    simp only [Algebra.smul_def, PowerSeries.algebraMap_eq, map_ofNat]
    ring
  have hRHS : PowerSeries.X * (-PowerSeries.X ^ 10 + 2 * PowerSeries.X ^ 9 - PowerSeries.X ^ 8 -
        2 * PowerSeries.X ^ 7 + 4 * PowerSeries.X ^ 6 - PowerSeries.X ^ 5 -
        2 * PowerSeries.X ^ 3 + PowerSeries.X - 1) =
      -(PowerSeries.X : PowerSeries ℚ) ^ 11 +
      (2 : ℚ) • (PowerSeries.X : PowerSeries ℚ) ^ 10 -
      (PowerSeries.X : PowerSeries ℚ) ^ 9 -
      (2 : ℚ) • (PowerSeries.X : PowerSeries ℚ) ^ 8 +
      (4 : ℚ) • (PowerSeries.X : PowerSeries ℚ) ^ 7 -
      (PowerSeries.X : PowerSeries ℚ) ^ 6 -
      (2 : ℚ) • (PowerSeries.X : PowerSeries ℚ) ^ 4 +
      (PowerSeries.X : PowerSeries ℚ) ^ 2 -
      (PowerSeries.X : PowerSeries ℚ) ^ 1 := by
    simp only [Algebra.smul_def, PowerSeries.algebraMap_eq, map_ofNat]
    ring
  rw [hLHS, hRHS]
  ext k
  simp only [map_sub, map_add, map_neg, map_smul, smul_eq_mul, PowerSeries.coeff_mul_X_pow',
    PowerSeries.coeff_mk, PowerSeries.coeff_X_pow]
  have ha11 : a 11 = 65 := by rw [a_eq_formula 11 (by omega)]
  by_cases hk12 : 12 ≤ k
  · have hrec := a_recurrence k hk12
    have hrecQ : (a k : ℚ) = 3 * (a (k - 1) : ℚ) - 3 * (a (k - 2) : ℚ) + (a (k - 3) : ℚ) := by
      exact_mod_cast hrec
    simp only [if_pos (show 3 ≤ k by omega), if_pos (show 2 ≤ k by omega),
      if_pos (show 1 ≤ k by omega),
      if_neg (show k ≠ 11 by omega), if_neg (show k ≠ 10 by omega),
      if_neg (show k ≠ 9 by omega), if_neg (show k ≠ 8 by omega),
      if_neg (show k ≠ 7 by omega), if_neg (show k ≠ 6 by omega),
      if_neg (show k ≠ 4 by omega), if_neg (show k ≠ 2 by omega),
      if_neg (show k ≠ 1 by omega)]
    dsimp [f]
    simp only [if_neg (show k - 3 ≠ 0 by omega), if_neg (show k - 2 ≠ 0 by omega),
      if_neg (show k - 1 ≠ 0 by omega), if_neg (show k ≠ 0 by omega)]
    linarith
  · interval_cases k <;>
      simp [f, a_1, a_2, a_3, a_4, a_5, a_6, a_7, a_8, a_9, a_10, ha11] <;>
      norm_num

end OMA_A039827

theorem OMA.solution : type_of% @OMA.S_oeis_a039827.main :=
  ⟨OMA_A039827.a_eq_formula, OMA_A039827.a_recurrence, OMA_A039827.a_gf⟩
