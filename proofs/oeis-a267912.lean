import OMAStatements.S_oeis_a267912

-- Proof of Barker's conjectures for OEIS A267912.
-- Idea: count the continuations of a row from a scan state (r, p, k). Once k >= 2 every value
-- is allowed, so by symmetry the count depends only on whether r is none and whether p = r;
-- this gives a small linear system, hence a(n+6) = 3 a(n+5) + 2 a(n+4) - 8 a(n+3), which yields
-- both the generating function (coefficientwise) and the closed form (by induction).

namespace A267912Proof

open PowerSeries OMA.S_oeis_a267912

/-- Pair (S, T): continuations from a repeat state with p = r, resp. p /= r (k >= 2). -/
def ST : ℕ → ℕ × ℕ
  | 0 => (1, 1)
  | m + 1 => (2 * (ST m).2, 2 * (ST m).1 + (ST m).2)

def S (m : ℕ) : ℕ := (ST m).1
def T (m : ℕ) : ℕ := (ST m).2

/-- Continuations from a state without a repeat yet (k >= 2). -/
def F : ℕ → ℕ
  | 0 => 1
  | m + 1 => 2 * F m + S m

/-- Continuations from the state (some 0, 0, 1). -/
def S1 : ℕ → ℕ
  | 0 => 1
  | m + 1 => T m

/-- Continuations from the state (none, 0, 1). -/
def E1 : ℕ → ℕ
  | 0 => 1
  | m + 1 => S1 m + F m

theorem S_succ (m : ℕ) : S (m + 1) = 2 * T m := rfl
theorem T_succ (m : ℕ) : T (m + 1) = 2 * S m + T m := rfl
theorem F_succ (m : ℕ) : F (m + 1) = 2 * F m + S m := rfl
theorem S1_succ (m : ℕ) : S1 (m + 1) = T m := rfl
theorem E1_succ (m : ℕ) : E1 (m + 1) = S1 m + F m := rfl

/-- Number of continuations of length m from the scan state (r, p, k). -/
def Cc (m : ℕ) (r : Option (Fin 3)) (p : Fin 3) (k : ℕ) : ℕ :=
  ∑ y : Fin m → Fin 3, if ok r p k (List.ofFn y) = true then 1 else 0

theorem sum_succ_words {n : ℕ} (f : (Fin (n + 1) → Fin 3) → ℕ) :
    ∑ u, f u = ∑ c : Fin 3, ∑ u : Fin n → Fin 3, f (Fin.cons c u) := by
  rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => Fin 3)).sum_comp f]
  exact Fintype.sum_prod_type _

theorem ofFn_cons' {n : ℕ} (c : Fin 3) (y : Fin n → Fin 3) :
    List.ofFn (Fin.cons c y : Fin (n + 1) → Fin 3) = c :: List.ofFn y := by
  simp [List.ofFn_succ]

theorem Cc_zero (r : Option (Fin 3)) (p : Fin 3) (k : ℕ) : Cc 0 r p k = 1 := by
  rw [Cc, Fintype.sum_unique]
  simp [ok]

theorem Cc_succ (m : ℕ) (r : Option (Fin 3)) (p : Fin 3) (k : ℕ) :
    Cc (m + 1) r p k = ∑ c : Fin 3, (if c.val ≤ k then (if c = p then
      (if r.all (fun v => decide (c ≠ v)) = true then Cc m (some c) c k else 0)
      else Cc m r c (max k (c.val + 1))) else 0) := by
  unfold Cc
  rw [sum_succ_words]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [ofFn_cons']
  by_cases hk : c.val ≤ k
  · rw [if_pos hk]
    by_cases h : c = p
    · simp only [ok, if_pos h]
      cases hb : r.all (fun v => decide (c ≠ v)) <;> simp [hk]
    · simp only [ok, if_neg h]
      simp [hk]
  · rw [if_neg hk]
    simp [ok, hk]

theorem Cc_big (m : ℕ) :
    (∀ k, 2 ≤ k → ∀ p, Cc m none p k = F m) ∧
    (∀ k, 2 ≤ k → ∀ r p, Cc m (some r) p k = if p = r then S m else T m) := by
  induction m with
  | zero =>
    refine ⟨fun k _ p => by simp [Cc_zero, F], fun k _ r p => ?_⟩
    rw [Cc_zero]
    split_ifs <;> rfl
  | succ m ih =>
    obtain ⟨h1, h2⟩ := ih
    constructor
    · intro k hk p
      have hk1 : (1 : ℕ) ≤ k := by omega
      rw [Cc_succ, Fin.sum_univ_three, F_succ]
      fin_cases p <;> simp [h1, h2, hk, hk1, le_max_iff] <;> omega
    · intro k hk r p
      have hk1 : (1 : ℕ) ≤ k := by omega
      rw [Cc_succ, Fin.sum_univ_three, S_succ, T_succ]
      fin_cases r <;> fin_cases p <;> simp [h1, h2, hk, hk1, le_max_iff] <;> omega

theorem Cc_one (m : ℕ) : Cc m none 0 1 = E1 m ∧ Cc m (some 0) 0 1 = S1 m := by
  induction m with
  | zero => exact ⟨by simp [Cc_zero, E1], by simp [Cc_zero, S1]⟩
  | succ m ih =>
    obtain ⟨h1, h2⟩ := Cc_big m
    constructor
    · rw [Cc_succ, Fin.sum_univ_three, E1_succ]
      simp [h1, h2, ih.2, le_max_iff]
    · rw [Cc_succ, Fin.sum_univ_three, S1_succ]
      simp [h1, h2, le_max_iff]

theorem a_succ (n : ℕ) : a (n + 1) = E1 n := by
  rw [a, Finset.card_filter, sum_succ_words, Fin.sum_univ_three]
  simp only [ofFn_cons', valid]
  rw [← (Cc_one n).1]
  simp [Cc]

theorem E1_rec (j : ℕ) : E1 (j + 5) + 8 * E1 (j + 2) = 3 * E1 (j + 4) + 2 * E1 (j + 3) := by
  have e2 : E1 (j + 2) = S1 (j + 1) + F (j + 1) := rfl
  have e3 : E1 (j + 3) = S1 (j + 2) + F (j + 2) := rfl
  have e4 : E1 (j + 4) = S1 (j + 3) + F (j + 3) := rfl
  have e5 : E1 (j + 5) = S1 (j + 4) + F (j + 4) := rfl
  have s1 : S1 (j + 1) = T j := rfl
  have s2 : S1 (j + 2) = T (j + 1) := rfl
  have s3 : S1 (j + 3) = T (j + 2) := rfl
  have s4 : S1 (j + 4) = T (j + 3) := rfl
  have f1 : F (j + 1) = 2 * F j + S j := rfl
  have f2 : F (j + 2) = 2 * F (j + 1) + S (j + 1) := rfl
  have f3 : F (j + 3) = 2 * F (j + 2) + S (j + 2) := rfl
  have f4 : F (j + 4) = 2 * F (j + 3) + S (j + 3) := rfl
  have t1 : S (j + 1) = 2 * T j := rfl
  have t2 : S (j + 2) = 2 * T (j + 1) := rfl
  have t3 : S (j + 3) = 2 * T (j + 2) := rfl
  have u1 : T (j + 1) = 2 * S j + T j := rfl
  have u2 : T (j + 2) = 2 * S (j + 1) + T (j + 1) := rfl
  have u3 : T (j + 3) = 2 * S (j + 2) + T (j + 2) := rfl
  omega

theorem aN (k : ℕ) : a (k + 6) + 8 * a (k + 3) = 3 * a (k + 5) + 2 * a (k + 4) := by
  have e1 : a (k + 3) = E1 (k + 2) := a_succ (k + 2)
  have e2 : a (k + 4) = E1 (k + 3) := a_succ (k + 3)
  have e3 : a (k + 5) = E1 (k + 4) := a_succ (k + 4)
  have e4 : a (k + 6) = E1 (k + 5) := a_succ (k + 5)
  have := E1_rec k
  omega

theorem ha1 : a 1 = 1 := by
  rw [a_succ 0]; decide

theorem ha2 : a 2 = 2 := by
  rw [a_succ 1]; decide

theorem ha3 : a 3 = 4 := by
  rw [a_succ 2]; decide

theorem ha4 : a 4 = 11 := by
  rw [a_succ 3]; decide

theorem ha5 : a 5 = 29 := by
  rw [a_succ 4]; decide

theorem key : gf * ((1 - 2 * X) * (1 - X - 4 * X ^ 2)) =
    X * (1 - X - 4 * X ^ 2 + 3 * X ^ 3 + 4 * X ^ 4) := by
  have e1 : gf * ((1 - 2 * X) * (1 - X - 4 * X ^ 2)) =
      gf - C (3 : ℚ) * (gf * X ^ 1) - C (2 : ℚ) * (gf * X ^ 2) + C (8 : ℚ) * (gf * X ^ 3) := by
    rw [map_ofNat C 3, map_ofNat C 2, map_ofNat C 8]
    ring
  have e2 : (X * (1 - X - 4 * X ^ 2 + 3 * X ^ 3 + 4 * X ^ 4) : ℚ⟦X⟧) =
      X ^ 1 - X ^ 2 - C (4 : ℚ) * X ^ 3 + C (3 : ℚ) * X ^ 4 + C (4 : ℚ) * X ^ 5 := by
    rw [map_ofNat C 4, map_ofNat C 3]
    ring
  rw [e1, e2]
  ext n
  match n with
  | 0 =>
    simp only [gf, map_add, map_sub, coeff_C_mul, coeff_mk, coeff_mul_X_pow', coeff_X_pow]
    norm_num
  | 1 =>
    simp only [gf, map_add, map_sub, coeff_C_mul, coeff_mk, coeff_mul_X_pow', coeff_X_pow]
    norm_num [ha1]
  | 2 =>
    simp only [gf, map_add, map_sub, coeff_C_mul, coeff_mk, coeff_mul_X_pow', coeff_X_pow]
    norm_num [ha1, ha2]
  | 3 =>
    simp only [gf, map_add, map_sub, coeff_C_mul, coeff_mk, coeff_mul_X_pow', coeff_X_pow]
    norm_num [ha1, ha2, ha3]
  | 4 =>
    simp only [gf, map_add, map_sub, coeff_C_mul, coeff_mk, coeff_mul_X_pow', coeff_X_pow]
    norm_num [ha1, ha2, ha3, ha4]
  | 5 =>
    simp only [gf, map_add, map_sub, coeff_C_mul, coeff_mk, coeff_mul_X_pow', coeff_X_pow]
    norm_num [ha2, ha3, ha4, ha5]
  | k + 6 =>
    have hr : (a (k + 6) : ℚ) + 8 * a (k + 3) = 3 * a (k + 5) + 2 * a (k + 4) := by
      exact_mod_cast aN k
    simp only [gf, map_add, map_sub, coeff_C_mul, coeff_mk, coeff_mul_X_pow', coeff_X_pow,
      show 3 ≤ k + 6 by omega, show 2 ≤ k + 6 by omega, show 1 ≤ k + 6 by omega,
      show k + 6 - 3 = k + 3 by omega, show k + 6 - 2 = k + 4 by omega,
      show k + 6 - 1 = k + 5 by omega, if_true,
      show ¬ (k + 6 = 0) by omega, show ¬ (k + 3 = 0) by omega, show ¬ (k + 4 = 0) by omega,
      show ¬ (k + 5 = 0) by omega, show ¬ (k + 6 = 1) by omega, show ¬ (k + 6 = 2) by omega,
      show 4 ≤ k + 6 by omega, show 5 ≤ k + 6 by omega,
      show k + 6 - 4 = k + 2 by omega, show k + 6 - 5 = k + 1 by omega, coeff_C,
      show ¬ (k + 2 = 0) by omega, show ¬ (k + 1 = 0) by omega, if_false]
    linarith

noncomputable def Q (n : ℕ) : ℝ :=
  -17 * 4 ^ (1 + n) + (85 - 19 * Real.sqrt 17) * (1 - Real.sqrt 17) ^ n +
    (1 + Real.sqrt 17) ^ n * (85 + 19 * Real.sqrt 17)

noncomputable def G (n : ℕ) : ℝ := 1 / 17 * (2 : ℝ) ^ (-5 - (n : ℤ)) * Q n

theorem hs : Real.sqrt 17 ^ 2 = 17 := Real.sq_sqrt (by norm_num)

theorem Q_rec (n : ℕ) : Q (n + 3) = 6 * Q (n + 2) + 8 * Q (n + 1) - 64 * Q n := by
  unfold Q
  linear_combination ((85 - 19 * Real.sqrt 17) * (1 - Real.sqrt 17) ^ n * (-3 - Real.sqrt 17) +
    (1 + Real.sqrt 17) ^ n * (85 + 19 * Real.sqrt 17) * (Real.sqrt 17 - 3)) * hs

theorem hu (n m : ℕ) (h : m = n + 1) :
    (2 : ℝ) ^ (-5 - (m : ℤ)) * 2 = (2 : ℝ) ^ (-5 - (n : ℤ)) := by
  rw [show (-5 - (n : ℤ)) = (-5 - (m : ℤ)) + 1 by rw [h]; push_cast; ring,
    zpow_add_one₀ two_ne_zero]

theorem G_rec (n : ℕ) : G (n + 3) = 3 * G (n + 2) + 2 * G (n + 1) - 8 * G n := by
  unfold G
  rw [← hu n (n + 1) rfl, ← hu (n + 1) (n + 2) rfl, ← hu (n + 2) (n + 3) rfl]
  linear_combination ((2 : ℝ) ^ (-5 - ((n + 3 : ℕ) : ℤ)) / 17) * Q_rec n

theorem G_rec6 (n : ℕ) : G (n + 6) = 3 * G (n + 5) + 2 * G (n + 4) - 8 * G (n + 3) :=
  G_rec (n + 3)

theorem hQ3 : Q 3 = 17408 := by
  unfold Q
  linear_combination (1270 + 38 * Real.sqrt 17 ^ 2) * hs

theorem hQ4 : Q 4 = 95744 := by
  unfold Q
  linear_combination (6646 + 322 * Real.sqrt 17 ^ 2) * hs

theorem hQ5 : Q 5 = 504832 := by
  unfold Q
  linear_combination (33782 + 1876 * Real.sqrt 17 ^ 2 + 38 * Real.sqrt 17 ^ 4) * hs

theorem closed (k : ℕ) :
    (a (k + 3) : ℝ) = G (k + 3) ∧ (a (k + 4) : ℝ) = G (k + 4) ∧
      (a (k + 5) : ℝ) = G (k + 5) := by
  induction k with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · show (a 3 : ℝ) = G 3
      rw [ha3]
      unfold G
      rw [hQ3]
      norm_num
    · show (a 4 : ℝ) = G 4
      rw [ha4]
      unfold G
      rw [hQ4]
      norm_num
    · show (a 5 : ℝ) = G 5
      rw [ha5]
      unfold G
      rw [hQ5]
      norm_num
  | succ k ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    refine ⟨h2, h3, ?_⟩
    have hr : (a (k + 6) : ℝ) + 8 * a (k + 3) = 3 * a (k + 5) + 2 * a (k + 4) := by
      exact_mod_cast aN k
    show (a (k + 6) : ℝ) = G (k + 6)
    rw [G_rec6]
    linarith

end A267912Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a267912.main := by
  refine ⟨?_, fun n hn => ?_⟩
  · rw [PowerSeries.eq_mul_inv_iff_mul_eq (by simp)]
    exact A267912Proof.key
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
    exact (A267912Proof.closed k).1
