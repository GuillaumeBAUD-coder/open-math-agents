import OMAStatements.S_oeis_a177118

open PowerSeries Finset

namespace OMA.S_oeis_a177118.Proof

private lemma aList_length (n : ℕ) : (aList n).length = n + 1 := by
  induction n with
  | zero => rfl
  | succ k ih =>
    cases k with
    | zero => rfl
    | succ m =>
      simp only [aList, List.length_append, List.length_singleton]
      exact congrArg (· + 1) ih

private lemma aList_getD_eq (m n : ℕ) (h : m ≤ n) : (aList n).getD m 0 = a m := by
  induction n with
  | zero =>
    have hm : m = 0 := Nat.eq_zero_of_le_zero h
    subst hm; rfl
  | succ k ih =>
    by_cases hmk : m = k + 1
    · subst hmk; rfl
    · have hle : m ≤ k := Nat.le_of_lt_succ (lt_of_le_of_ne h hmk)
      cases k with
      | zero =>
        have hm : m = 0 := Nat.eq_zero_of_le_zero hle
        subst hm; rfl
      | succ r =>
        change (aList (r + 1) ++ [_]).getD m 0 = a m
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_left]
        · rw [← List.getD_eq_getElem?_getD]
          exact ih hle
        · rw [aList_length]; omega

private lemma a_zero : a 0 = 1 := rfl
private lemma a_one : a 1 = 5 := rfl

private lemma a_rec (n : ℕ) :
    a (n + 2) = (∑ p ∈ Finset.range (n + 2), a p * a (n + 1 - p)) - 2 * ((n : ℤ) + 2) := by
  unfold a
  change (aList (n + 1) ++ [(∑ p ∈ Finset.range (n + 2),
    (aList (n + 1)).getD p 0 * (aList (n + 1)).getD (n + 1 - p) 0) - 2 * ((n : ℤ) + 2)]).getD (n + 2) 0 = _
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right]
  · rw [aList_length]
    simp only [Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
    congr 1
    refine Finset.sum_congr rfl fun p hp => ?_
    have hp' : p ≤ n + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hp)
    rw [aList_getD_eq p (n + 1) hp', aList_getD_eq (n + 1 - p) (n + 1) (Nat.sub_le _ _)]; rfl
  · rw [aList_length]

private noncomputable def D (f : ℤ⟦X⟧) : ℤ⟦X⟧ :=
  PowerSeries.mk fun n => ((n : ℤ) + 1) * coeff (n + 1) f

private lemma coeff_D (f : ℤ⟦X⟧) (n : ℕ) :
    coeff n (D f) = ((n : ℤ) + 1) * coeff (n + 1) f :=
  coeff_mk n _

private lemma D_add (f g : ℤ⟦X⟧) : D (f + g) = D f + D g := by
  ext n; simp only [coeff_D, map_add]; ring

private lemma D_sub (f g : ℤ⟦X⟧) : D (f - g) = D f - D g := by
  ext n; simp only [coeff_D, map_sub]; ring

private lemma D_C (c : ℤ) : D (C c) = 0 := by
  ext n; rw [coeff_D, coeff_C]; simp

private lemma D_one : D (1 : ℤ⟦X⟧) = 0 := by
  simpa using D_C 1

private lemma D_X : D (X : ℤ⟦X⟧) = 1 := by
  ext n
  rw [coeff_D, coeff_X, coeff_one]
  cases n with
  | zero => simp
  | succ k => simp

private lemma D_mul (f g : ℤ⟦X⟧) : D (f * g) = D f * g + f * D g := by
  ext n
  rw [coeff_D, map_add, coeff_mul, coeff_mul, coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun u v => coeff u f * coeff v g)]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun u v => coeff u (D f) * coeff v g)]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun u v => coeff u f * coeff v (D g))]
  simp only [coeff_D]
  have h1 : ∑ k ∈ Finset.range (n + 1), ((k : ℤ) + 1) * coeff (k + 1) f * coeff (n - k) g
      = ∑ k ∈ Finset.range (n + 2), (k : ℤ) * coeff k f * coeff (n + 1 - k) g := by
    symm
    rw [Finset.sum_range_succ']
    simp only [Nat.cast_zero, zero_mul, add_zero]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Nat.succ_sub_succ_eq_sub]; push_cast; rfl
  have h2 : ∑ k ∈ Finset.range (n + 1), coeff k f * ((((n - k : ℕ) : ℤ) + 1) * coeff (n - k + 1) g)
      = ∑ k ∈ Finset.range (n + 2), coeff k f * ((n + 1 - k : ℕ) : ℤ) * coeff (n + 1 - k) g := by
    symm
    rw [Finset.sum_range_succ]
    simp only [Nat.sub_self, Nat.cast_zero, mul_zero, zero_mul, add_zero]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hsub : n + 1 - k = n - k + 1 := by omega
    rw [hsub]; push_cast; ring
  rw [h1, h2, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ n + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hcast : ((n + 1 - k : ℕ) : ℤ) = (n : ℤ) + 1 - (k : ℤ) := by omega
  rw [hcast]; ring

private lemma D_sq (f : ℤ⟦X⟧) : D (f ^ 2) = 2 * f * D f := by
  rw [sq, D_mul]; ring

private lemma coeff_X_pow_mul (k : ℕ) (f : ℤ⟦X⟧) (n : ℕ) (h : k ≤ n) :
    coeff n (X ^ k * f) = coeff (n - k) f := by
  induction k generalizing n with
  | zero => simp
  | succ k ih =>
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [pow_succ', mul_assoc, coeff_succ_X_mul, ih m (by omega), Nat.succ_sub_succ_eq_sub]

private lemma coeff_X_pow_mul_D (k : ℕ) (f : ℤ⟦X⟧) (n : ℕ) (h : k ≤ n) :
    coeff n (X ^ k * (X * D f)) = ((n - k : ℕ) : ℤ) * coeff (n - k) f := by
  rw [coeff_X_pow_mul k (X * D f) n h]
  cases hnk : n - k with
  | zero => simp
  | succ m =>
    rw [coeff_succ_X_mul, coeff_D]
    push_cast; ring

private lemma A_quad :
    let A : ℤ⟦X⟧ := PowerSeries.mk a
    (1 - X) ^ 2 * (X * A ^ 2 - A + 1 + C (4) * X) + X ^ 2 * (C (-4) + C (2) * X) = 0 := by
  intro A
  have hconv : ∀ m : ℕ, coeff m (A ^ 2) = ∑ p ∈ Finset.range (m + 1), a p * a (m - p) := by
    intro m
    rw [sq, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun u v => coeff u A * coeff v A)]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp [A]
  set S : ℤ⟦X⟧ := X * A ^ 2 - A + 1 + C (4) * X
  have hS : ∀ m : ℕ, coeff m S = if m ≤ 1 then 0 else -(-2 * (m : ℤ) + 0) := by
    intro m
    dsimp only [S]
    cases m with
    | zero =>
      simp [A, a_zero]
    | succ m =>
      cases m with
      | zero =>
        simp only [map_add, map_sub, coeff_succ_X_mul, coeff_one, coeff_C_mul, coeff_X,
          Nat.succ_ne_zero, ↓reduceIte, add_zero, hconv 0]
        simp [A, a_zero, a_one]
      | succ r =>
        simp only [map_add, map_sub, coeff_succ_X_mul, coeff_one, coeff_C_mul, coeff_X,
          Nat.succ_ne_zero, ↓reduceIte, add_zero, hconv (r + 1)]
        have hAr : coeff (r + 2) A = a (r + 2) := coeff_mk _ _
        have hne1 : r + 2 ≠ 1 := by omega
        rw [if_neg hne1, mul_zero, add_zero, hAr, a_rec r]
        have hnot : ¬ (r + 2 ≤ 1) := by omega
        rw [if_neg hnot]; push_cast; ring
  have hrew : (1 - X) ^ 2 * S + X ^ 2 * (C (-4) + C (2) * X)
      = S - C 2 * (X * S) + X ^ 2 * S + C (-4) * (X ^ 2 * 1) + C (2) * (X ^ 3 * 1) := by
    simp only [map_neg, map_ofNat, map_one, map_zero]; ring
  change (1 - X) ^ 2 * S + X ^ 2 * (C (-4) + C (2) * X) = 0
  rw [hrew]
  ext m
  simp only [map_add, map_sub, coeff_C_mul, map_zero]
  cases m with
  | zero =>
    rw [hS 0]
    simp [sq, pow_succ]
  | succ m =>
    cases m with
    | zero =>
      rw [coeff_succ_X_mul, hS 1, hS 0]
      have h1S : coeff 1 (X ^ 2 * S) = 0 := by rw [sq, mul_assoc, coeff_succ_X_mul]; simp
      have h11 : coeff 1 (X ^ 2 * 1 : ℤ⟦X⟧) = 0 := by rw [sq, mul_assoc, coeff_succ_X_mul]; simp
      have h13 : coeff 1 (X ^ 3 * 1 : ℤ⟦X⟧) = 0 := by rw [pow_succ', mul_assoc, coeff_succ_X_mul]; simp
      rw [h1S, h11, h13]; simp
    | succ m =>
      cases m with
      | zero =>
        rw [coeff_succ_X_mul, coeff_X_pow_mul 2 S 2 (by omega), coeff_X_pow_mul 2 1 2 (by omega),
            hS 2, hS 1, hS 0]
        have hx3 : coeff 2 (X ^ 3 * 1 : ℤ⟦X⟧) = 0 := by
          rw [mul_one, pow_succ', coeff_succ_X_mul, sq, coeff_succ_X_mul, coeff_X]; simp
        rw [hx3, Nat.sub_self, coeff_one]; norm_num
      | succ m =>
        cases m with
        | zero =>
          rw [coeff_succ_X_mul, coeff_X_pow_mul 2 S 3 (by omega), coeff_X_pow_mul 2 1 3 (by omega),
              coeff_X_pow_mul 3 1 3 (by omega), hS 3, hS 2, hS 1]
          simp [coeff_one]
        | succ k =>
          rw [coeff_succ_X_mul, coeff_X_pow_mul 2 S (k + 4) (by omega),
              coeff_X_pow_mul 2 1 (k + 4) (by omega), coeff_X_pow_mul 3 1 (k + 4) (by omega)]
          have hc2 : coeff (k + 4 - 2) (1 : ℤ⟦X⟧) = 0 := by rw [coeff_one]; simp [show k + 4 - 2 ≠ 0 by omega]
          have hc3 : coeff (k + 4 - 3) (1 : ℤ⟦X⟧) = 0 := by rw [coeff_one]; simp [show k + 4 - 3 ≠ 0 by omega]
          rw [hc2, hc3, hS (k + 4), hS (k + 3), show k + 4 - 2 = k + 2 by omega, hS (k + 2)]
          rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
          push_cast; ring

theorem main_proof :
    ∀ n : ℕ, 5 ≤ n →
      ((n : ℤ) + 1) * a n
      - (7 * (n : ℤ) - 2) * a (n - 1)
      - ((n : ℤ) - 11) * a (n - 2)
      + 3 * (17 * (n : ℤ) - 56) * a (n - 3)
      - 2 * (34 * (n : ℤ) - 137) * a (n - 4)
      + 24 * ((n : ℤ) - 5) * a (n - 5) = 0 := by
  let A : ℤ⟦X⟧ := PowerSeries.mk a
  let B : ℤ⟦X⟧ := 2 * X * A - 1
  let Q : ℤ⟦X⟧ := 1 - 6 * X - 7 * X ^ 2 + 44 * X ^ 3 - 24 * X ^ 4
  have hB : (1 - X) ^ 2 * B ^ 2 = Q := by
    have hq := A_quad
    dsimp only [A, B, Q] at hq ⊢
    simp only [map_neg, map_ofNat, map_one, map_zero] at hq
    linear_combination 4 * X * hq
  have hDQ : D Q = -6 - 14 * X + 132 * X ^ 2 - 96 * X ^ 3 := by
    dsimp only [Q]
    have hD2 : D (X ^ 2 : ℤ⟦X⟧) = 2 * X := by
      rw [sq, D_mul, D_X]; ring
    have hD3 : D (X ^ 3 : ℤ⟦X⟧) = 3 * X ^ 2 := by
      rw [pow_succ, D_mul, hD2, D_X]; ring
    have hD4 : D (X ^ 4 : ℤ⟦X⟧) = 4 * X ^ 3 := by
      rw [pow_succ, D_mul, hD3, D_X]; ring
    have hDC : ∀ (c : ℤ) (f : ℤ⟦X⟧), D (C c * f) = C c * D f := fun c f => by
      rw [D_mul, D_C, zero_mul, zero_add]
    have hrew : (1 - 6 * X - 7 * X ^ 2 + 44 * X ^ 3 - 24 * X ^ 4 : ℤ⟦X⟧) = 1 + C (-6) * X + C (-7) * X ^ 2 + C (44) * X ^ 3 + C (-24) * X ^ 4 := by
      simp only [map_neg, map_ofNat, map_one, map_zero]; ring
    rw [hrew, D_add, D_add, D_add, D_add, D_one, hDC, hDC, hDC, hDC, D_X, hD2, hD3, hD4]
    simp only [map_neg, map_ofNat, map_one, map_zero]
    ring
  have hDB : D B = 2 * A + 2 * X * D A := by
    dsimp only [B]
    have h2 : (2 : ℤ⟦X⟧) = C 2 := by simp
    rw [D_sub, D_one, sub_zero, mul_assoc, h2, D_mul, D_C, zero_mul, zero_add, D_mul, D_X]
    simp only [map_ofNat]; ring
  have hdiff : -2 * (1 - X) * B ^ 2 + 2 * (1 - X) ^ 2 * B * D B = D Q := by
    have h1 : D ((1 - X) ^ 2 * B ^ 2) = D Q := congrArg D hB
    rw [D_mul, D_sq, D_sq, D_sub, D_one, D_X] at h1
    linear_combination h1
  have hode_B2 : 2 * (1 - X) * Q * D B - (2 * Q + (1 - X) * D Q) * B = 0 := by
    linear_combination (1 - X) * B * hdiff + (2 * B - 2 * (1 - X) * D B) * hB
  have hode_A :
      2 * ((1 - 7 * X - X ^ 2 + 51 * X ^ 3 - 68 * X ^ 4 + 24 * X ^ 5) * (X * D A) + (1 - 5 * X + 9 * X ^ 2 - 15 * X ^ 3 + 2 * X ^ 4) * A) + (-2 - 10 * X + 66 * X ^ 2 - 70 * X ^ 3 + 24 * X ^ 4) = 0 := by
    have hcheck :
        2 * (1 - X) * Q * D B - (2 * Q + (1 - X) * D Q) * B
        = C 2 * (2 * ((1 - 7 * X - X ^ 2 + 51 * X ^ 3 - 68 * X ^ 4 + 24 * X ^ 5) * (X * D A) + (1 - 5 * X + 9 * X ^ 2 - 15 * X ^ 3 + 2 * X ^ 4) * A) + (-2 - 10 * X + 66 * X ^ 2 - 70 * X ^ 3 + 24 * X ^ 4)) := by
      rw [hDB, hDQ]
      dsimp only [B, Q]
      simp only [map_ofNat]
      ring
    rw [hcheck] at hode_B2
    ext m
    have hm := congrArg (coeff m) hode_B2
    rw [coeff_C_mul, map_zero] at hm
    rw [map_zero]
    omega
  intro n hn
  have hm := congrArg (coeff n) hode_A
  have hRHS : coeff n (-2 - 10 * X + 66 * X ^ 2 - 70 * X ^ 3 + 24 * X ^ 4 : ℤ⟦X⟧) = 0 := by
    have h0 : coeff n (1 : ℤ⟦X⟧) = 0 := by rw [coeff_one]; simp [show n ≠ 0 by omega]
    have h1 : coeff n (X : ℤ⟦X⟧) = 0 := by rw [coeff_X]; simp [show n ≠ 1 by omega]
    have h2 : coeff n (X ^ 2 : ℤ⟦X⟧) = 0 := by
      rw [show (X ^ 2 : ℤ⟦X⟧) = X ^ 2 * 1 by ring, coeff_X_pow_mul 2 1 n (by omega), coeff_one]
      simp [show n - 2 ≠ 0 by omega]
    have h3 : coeff n (X ^ 3 : ℤ⟦X⟧) = 0 := by
      rw [show (X ^ 3 : ℤ⟦X⟧) = X ^ 3 * 1 by ring, coeff_X_pow_mul 3 1 n (by omega), coeff_one]
      simp [show n - 3 ≠ 0 by omega]
    have h4 : coeff n (X ^ 4 : ℤ⟦X⟧) = 0 := by
      rw [show (X ^ 4 : ℤ⟦X⟧) = X ^ 4 * 1 by ring, coeff_X_pow_mul 4 1 n (by omega), coeff_one]
      simp [show n - 4 ≠ 0 by omega]
    have hc : coeff n (-2 - 10 * X + 66 * X ^ 2 - 70 * X ^ 3 + 24 * X ^ 4 : ℤ⟦X⟧) = (-2) * coeff n (1 : ℤ⟦X⟧) + (-10) * coeff n (X : ℤ⟦X⟧) + (66) * coeff n (X ^ 2 : ℤ⟦X⟧) + (-70) * coeff n (X ^ 3 : ℤ⟦X⟧) + (24) * coeff n (X ^ 4 : ℤ⟦X⟧) := by
      have : (-2 - 10 * X + 66 * X ^ 2 - 70 * X ^ 3 + 24 * X ^ 4 : ℤ⟦X⟧) = C (-2) * 1 + C (-10) * X + C (66) * X ^ 2 + C (-70) * X ^ 3 + C (24) * X ^ 4 := by
        simp only [map_neg, map_ofNat, map_one, map_zero]; ring
      rw [this]
      simp only [map_add, coeff_C_mul]
    rw [hc, h0, h1, h2, h3, h4]; ring
  rw [map_add, hRHS, add_zero, map_zero] at hm
  have hLHS : coeff n ((1 - 7 * X - X ^ 2 + 51 * X ^ 3 - 68 * X ^ 4 + 24 * X ^ 5) * (X * D A) + (1 - 5 * X + 9 * X ^ 2 - 15 * X ^ 3 + 2 * X ^ 4) * A) = 0 := by
    have h2 : ∀ f : ℤ⟦X⟧, coeff n (2 * f) = 2 * coeff n f := fun f => by
      have : (2 : ℤ⟦X⟧) = C 2 := by simp
      rw [this, coeff_C_mul]
    rw [h2] at hm
    omega
  have hexpand : (1 - 7 * X - X ^ 2 + 51 * X ^ 3 - 68 * X ^ 4 + 24 * X ^ 5) * (X * D A) + (1 - 5 * X + 9 * X ^ 2 - 15 * X ^ 3 + 2 * X ^ 4) * A = X ^ 0 * (X * D A) - C 7 * (X ^ 1 * (X * D A)) - X ^ 2 * (X * D A) + C 51 * (X ^ 3 * (X * D A)) - C 68 * (X ^ 4 * (X * D A)) + C 24 * (X ^ 5 * (X * D A)) + X ^ 0 * A - C 5 * (X ^ 1 * A) + C 9 * (X ^ 2 * A) - C 15 * (X ^ 3 * A) + C 2 * (X ^ 4 * A) := by
    simp only [map_ofNat]; ring
  rw [hexpand] at hLHS
  simp only [map_add, map_sub, coeff_C_mul] at hLHS
  rw [coeff_X_pow_mul_D 0 A n (by omega), coeff_X_pow_mul_D 1 A n (by omega), coeff_X_pow_mul_D 2 A n (by omega), coeff_X_pow_mul_D 3 A n (by omega), coeff_X_pow_mul_D 4 A n (by omega), coeff_X_pow_mul_D 5 A n (by omega), coeff_X_pow_mul 0 A n (by omega), coeff_X_pow_mul 1 A n (by omega), coeff_X_pow_mul 2 A n (by omega), coeff_X_pow_mul 3 A n (by omega), coeff_X_pow_mul 4 A n (by omega)] at hLHS
  have hA : ∀ k, coeff k A = a k := fun k => coeff_mk k a
  simp only [Nat.sub_zero, hA] at hLHS
  have hc1 : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
  have hc2 : ((n - 2 : ℕ) : ℤ) = (n : ℤ) - 2 := by omega
  have hc3 : ((n - 3 : ℕ) : ℤ) = (n : ℤ) - 3 := by omega
  have hc4 : ((n - 4 : ℕ) : ℤ) = (n : ℤ) - 4 := by omega
  have hc5 : ((n - 5 : ℕ) : ℤ) = (n : ℤ) - 5 := by omega
  rw [hc1, hc2, hc3, hc4, hc5] at hLHS
  linarith

end OMA.S_oeis_a177118.Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a177118.main :=
  OMA.S_oeis_a177118.Proof.main_proof
