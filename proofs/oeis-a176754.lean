import OMAStatements.S_oeis_a176754

/-!
# OEIS A176754: Mathar's P-recurrence from the algebraic generating function

`a(0) = 1`, `a(1) = 2` and `a(n+2) = ∑_{p ≤ n+1} a(p) a(n+1-p) - 2`.

Let `A = ∑ a(n) xⁿ` and `F = (1-x)(xA² - A)`.  The defining rule gives the quadratic
equation `(1-x)F + N = 0` with `N = 1 - x - 3x² + 3x³`, i.e. `U A² - V A + N = 0` for
`U = x(1-x)²`, `V = (1-x)²`.

Differentiating and eliminating `A²` with the quadratic gives the first order linear
differential equation

`(x - 6x² + 5x³ + 12x⁴ - 12x⁵) A' + (1 - 4x + 5x² - 6x³) A = 1 - 9x² + 6x³`,

whose coefficient comparison at `xⁿ` is exactly Mathar's recurrence.
-/

namespace A176754Proof

open OMA.S_oeis_a176754 PowerSeries

private theorem prefix_length (n : ℕ) : (aList n).length = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    cases n with
    | zero => rfl
    | succ n => simp [aList, ih]

private theorem prefix_value (n k : ℕ) (hk : k ≤ n) : (aList n).getD k 0 = a k := by
  induction n with
  | zero =>
    have : k = 0 := by omega
    subst k
    rfl
  | succ n ih =>
    rcases eq_or_lt_of_le hk with rfl | h
    · rfl
    cases n with
    | zero =>
      have : k = 0 := by omega
      subst k
      rfl
    | succ n =>
      rw [aList, List.getD_append]
      · exact ih (by omega)
      · rw [prefix_length]
        omega

private theorem convolution (n : ℕ) :
    a (n + 2) = (∑ k ∈ Finset.range (n + 2), a k * a (n + 1 - k)) - 2 := by
  unfold a at ⊢
  rw [aList, List.getD_append_right _ _ _ _ (by rw [prefix_length])]
  rw [prefix_length]
  simp only [Nat.sub_self]
  change _ - 2 = _ - 2
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  have hk' := Finset.mem_range.mp hk
  change (aList (n + 1)).getD k 0 * (aList (n + 1)).getD (n + 1 - k) 0 =
    a k * a (n + 1 - k)
  rw [prefix_value _ _ (by omega), prefix_value _ _ (by omega)]

private noncomputable def series : ℚ⟦X⟧ := mk fun n => (a n : ℚ)

private lemma coeff_series (n : ℕ) : coeff n series = (a n : ℚ) := coeff_mk n _

private lemma a_zero : a 0 = 1 := rfl

private lemma a_one : a 1 = 2 := rfl

private lemma a_two : a 2 = 2 := rfl

private lemma a_zero_c : (a 0 : ℚ) = 1 := by norm_num [a_zero]

private lemma a_one_c : (a 1 : ℚ) = 2 := by norm_num [a_one]

private lemma a_two_c : (a 2 : ℚ) = 2 := by norm_num [a_two]

/-- `coeff n (c * X^k)`. -/
private lemma coeff_three (k n : ℕ) :
    coeff n ((3 : ℚ⟦X⟧) * X ^ k) = if n = k then (3 : ℚ) else 0 := by
  rw [show (3 : ℚ⟦X⟧) = C (3 : ℚ) from (map_natCast C 3).symm, coeff_C_mul, coeff_X_pow]
  split <;> simp

private lemma coeff_N_zero :
    coeff 0 (1 - X - 3 * X ^ 2 + 3 * X ^ 3 : ℚ⟦X⟧) = 1 := by
  simp only [map_add, map_sub, coeff_three, coeff_one, coeff_X]
  norm_num

private lemma coeff_N_one :
    coeff 1 (1 - X - 3 * X ^ 2 + 3 * X ^ 3 : ℚ⟦X⟧) = -1 := by
  simp only [map_add, map_sub, coeff_three, coeff_one, coeff_X]
  norm_num

private lemma coeff_N_two :
    coeff 2 (1 - X - 3 * X ^ 2 + 3 * X ^ 3 : ℚ⟦X⟧) = -3 := by
  simp only [map_add, map_sub, coeff_three, coeff_one, coeff_X]
  norm_num

private lemma coeff_N_three :
    coeff 3 (1 - X - 3 * X ^ 2 + 3 * X ^ 3 : ℚ⟦X⟧) = 3 := by
  simp only [map_add, map_sub, coeff_three, coeff_one, coeff_X]
  norm_num

private lemma coeff_N_ge (m : ℕ) :
    coeff (m + 4) (1 - X - 3 * X ^ 2 + 3 * X ^ 3 : ℚ⟦X⟧) = 0 := by
  have h1 : m + 4 ≠ 0 := by omega
  have h2 : m + 4 ≠ 1 := by omega
  have h3 : m + 4 ≠ 2 := by omega
  have h4 : m + 4 ≠ 3 := by omega
  simp only [map_add, map_sub, coeff_three, coeff_one, coeff_X, if_neg h1, if_neg h2,
    if_neg h3, if_neg h4]
  norm_num

private lemma coeff_X_zero (g : ℚ⟦X⟧) : coeff 0 (X * g) = 0 := by
  rw [show (X : ℚ⟦X⟧) = X ^ 1 by ring, coeff_X_pow_mul', if_neg (by omega)]

/-- `coeff k (A²) = a(k+1) + 2` for `k ≥ 1`. -/
private lemma coeff_sq (k : ℕ) (hk : 1 ≤ k) : coeff k (series ^ 2) = (a (k + 1) : ℚ) + 2 := by
  rw [pow_two, coeff_mul]
  simp only [coeff_series]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => (a i : ℚ) * a j)]
  have h := convolution (k - 1)
  rw [show k - 1 + 2 = k + 1 by omega, show k - 1 + 1 = k by omega] at h
  have hcast : ((∑ x ∈ Finset.range (k + 1), a x * a (k - x) : ℤ) : ℚ) =
      ∑ x ∈ Finset.range (k + 1), (a x : ℚ) * (a (k - x) : ℚ) := by
    push_cast
    rfl
  rw [← hcast, h]
  push_cast
  ring

private lemma coeff_zero_sq : coeff 0 (series ^ 2) = 1 := by
  rw [pow_two, coeff_mul]
  simp only [coeff_series]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => (a i : ℚ) * a j)]
  simp [Finset.sum_range_succ, a_zero]

private lemma coeff_one_sq : coeff 1 (series ^ 2) = 4 := by
  rw [pow_two, coeff_mul]
  simp only [coeff_series]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => (a i : ℚ) * a j)]
  simp [Finset.sum_range_succ, a_zero, a_one]
  norm_num

/-- `F = (1-x)(xA² - A)`. -/
private noncomputable def F : ℚ⟦X⟧ := (1 - X) * (X * series ^ 2 - series)

private lemma coeff_one_sub_X (n : ℕ) (g : ℚ⟦X⟧) :
    coeff (n + 1) ((1 - X) * g) = coeff (n + 1) g - coeff n g := by
  rw [sub_mul, one_mul, map_sub, coeff_succ_X_mul]

private lemma coeff_one_sub_X_zero (g : ℚ⟦X⟧) : coeff 0 ((1 - X) * g) = coeff 0 g := by
  rw [sub_mul, one_mul, map_sub, coeff_X_zero, sub_zero]

private lemma coeff_F_zero : coeff 0 F = -1 := by
  rw [F, coeff_one_sub_X_zero]
  simp only [map_sub, coeff_X_zero, coeff_series, a_zero_c]
  norm_num

private lemma coeff_F_one : coeff 1 F = 0 := by
  rw [F, coeff_one_sub_X 0]
  have e1 : coeff 1 (X * series ^ 2) = coeff 0 (series ^ 2) := coeff_succ_X_mul ..
  have e2 : coeff 1 (X * series) = coeff 0 series := coeff_succ_X_mul ..
  have e3 : coeff 0 (X * series ^ 2) = 0 := coeff_X_zero _
  have e4 : coeff 0 (X * series) = 0 := coeff_X_zero _
  simp only [map_sub, e1, e2, e3, e4, coeff_zero_sq, coeff_series]
  norm_num [a_zero, a_one]

private lemma coeff_F_two : coeff 2 F = 3 := by
  rw [F, coeff_one_sub_X 1]
  have e1 : coeff 2 (X * series ^ 2) = coeff 1 (series ^ 2) := coeff_succ_X_mul ..
  have e2 : coeff 1 (X * series ^ 2) = coeff 0 (series ^ 2) := coeff_succ_X_mul ..
  have e3 : coeff 2 (X * series) = coeff 1 series := coeff_succ_X_mul ..
  have e4 : coeff 1 (X * series) = coeff 0 series := coeff_succ_X_mul ..
  simp only [map_sub, e1, e2, e3, e4, coeff_one_sq, coeff_zero_sq, coeff_series]
  norm_num [a_one, a_two]

private lemma coeff_F_ge (k : ℕ) : coeff (k + 3) F = 0 := by
  have e1 := coeff_sq (k + 2) (by omega)
  have e2 := coeff_sq (k + 1) (by omega)
  rw [F, coeff_one_sub_X (k + 2)]
  have h1 : coeff (k + 3) (X * series ^ 2) = coeff (k + 2) (series ^ 2) := by
    rw [show k + 3 = k + 2 + 1 by omega, coeff_succ_X_mul]
  have h2 : coeff (k + 2) (X * series ^ 2) = coeff (k + 1) (series ^ 2) := by
    rw [show k + 2 = k + 1 + 1 by omega, coeff_succ_X_mul]
  have h3 : coeff (k + 3) (X * series) = (a (k + 2) : ℚ) := by
    rw [show k + 3 = k + 2 + 1 by omega, coeff_succ_X_mul, coeff_series]
  have h4 : coeff (k + 2) (X * series) = (a (k + 1) : ℚ) := by
    rw [show k + 2 = k + 1 + 1 by omega, coeff_succ_X_mul, coeff_series]
  simp only [map_sub, h1, h2, h3, h4, coeff_series, e1, e2]
  ring

/-- The quadratic equation `(1-x)F + N = 0`, `N = 1 - x - 3x² + 3x³`. -/
private theorem quad_F : (1 - X : ℚ⟦X⟧) * F + (1 - X - 3 * X ^ 2 + 3 * X ^ 3) = 0 := by
  ext m
  rcases m with _ | _ | _ | _ | m
  · rw [map_add, map_zero, coeff_one_sub_X_zero, coeff_F_zero, coeff_N_zero]
    norm_num
  · rw [map_add, map_zero, coeff_one_sub_X 0, coeff_F_zero, coeff_F_one, coeff_N_one]
    norm_num
  · rw [map_add, map_zero, coeff_one_sub_X 1, coeff_F_one, coeff_F_two, coeff_N_two]
    norm_num
  · rw [map_add, map_zero, coeff_one_sub_X 2, coeff_F_two, coeff_F_ge 0, coeff_N_three]
    norm_num
  · rw [map_add, map_zero, coeff_one_sub_X (m + 3), coeff_F_ge (m + 1), coeff_F_ge m,
      coeff_N_ge m]
    norm_num

private theorem quadratic :
    (X * (1 - X) ^ 2) * series ^ 2 - (1 - X) ^ 2 * series + (1 - X - 3 * X ^ 2 + 3 * X ^ 3) = 0 := by
  have h := quad_F
  rw [show (X * (1 - X) ^ 2) * series ^ 2 - (1 - X) ^ 2 * series
      = (1 - X) * F by rw [F]; ring] 
  exact h

/-! ### From the quadratic to a first order linear ODE -/

private lemma derivative_series_sq :
    derivative ℚ (series ^ 2) = 2 * series * derivative ℚ series := by
  rw [pow_two, Derivation.leibniz]
  simp only [smul_eq_mul]
  ring

private lemma derivative_one_sub_X_sq :
    derivative ℚ ((1 - X) ^ 2 : ℚ⟦X⟧) = -2 + 2 * X := by
  rw [pow_two, Derivation.leibniz]
  simp only [smul_eq_mul]
  simp
  ring

/-- The differential equation `p A' + q A = r`. -/
private theorem differential :
    (1 - 6 * X + 5 * X ^ 2 + 12 * X ^ 3 - 12 * X ^ 4) * (X * derivative ℚ series)
      + (1 - 4 * X + 5 * X ^ 2 - 6 * X ^ 3) * series = 1 - 9 * X ^ 2 + 6 * X ^ 3 := by
  have hd3 : derivative ℚ (3 : ℚ⟦X⟧) = 0 := (derivative ℚ).map_natCast 3
  have hdX : derivative ℚ (X : ℚ⟦X⟧) = 1 := PowerSeries.derivative_X
  have hdA : derivative ℚ (1 - X - 3 * X ^ 2 + 3 * X ^ 3 : ℚ⟦X⟧) = -1 - 6 * X + 9 * X ^ 2 := by
    simp only [map_sub, map_add, Derivation.leibniz, smul_eq_mul, Derivation.leibniz_pow,
      Derivation.map_one_eq_zero, hd3, PowerSeries.derivative_X]
    ring
  have hE1 : (1 - 4 * X + 3 * X ^ 2) * series ^ 2
      + (X * (1 - X) ^ 2) * (2 * series * derivative ℚ series)
      - (-2 + 2 * X) * series - (1 - X) ^ 2 * derivative ℚ series
      + (-1 - 6 * X + 9 * X ^ 2) = 0 := by
    have h := congrArg (derivative ℚ) quadratic
    rw [map_zero] at h
    simp only [map_add, map_sub, Derivation.leibniz, smul_eq_mul, derivative_series_sq,
      derivative_one_sub_X_sq, hdA, hdX, Derivation.map_one_eq_zero] at h
    linear_combination (norm := ring) h
  have hT : (1 - X : ℚ⟦X⟧) ^ 4 *
      ((X - 6 * X ^ 2 + 5 * X ^ 3 + 12 * X ^ 4 - 12 * X ^ 5) * derivative ℚ series
        + (1 - 4 * X + 5 * X ^ 2 - 6 * X ^ 3) * series - (1 - 9 * X ^ 2 + 6 * X ^ 3)) = 0 := by
    linear_combination (norm := ring)
      ((X * (1 - X) ^ 2) * (2 * (X * (1 - X) ^ 2) * series - (1 - X) ^ 2)) * hE1
      + (-((1 - 4 * X + 3 * X ^ 2) * (2 * (X * (1 - X) ^ 2) * series - (1 - X) ^ 2)
          + 2 * ((1 - 4 * X + 3 * X ^ 2) * (1 - X) ^ 2
            - (X * (1 - X) ^ 2) * (-2 + 2 * X)))
        - 4 * (X * (1 - X) ^ 2) ^ 2 * derivative ℚ series) * quadratic
  have hg : (1 - X : ℚ⟦X⟧) ^ 4 ≠ 0 := by
    intro h
    have h0 := congrArg (coeff 0) h
    simp only [coeff_pow, map_sub, coeff_one, coeff_X] at h0
    norm_num at h0
  have hW := (mul_eq_zero.mp hT).resolve_left hg
  linear_combination hW

/-! ### Reading off the recurrence -/

private theorem euler_coeff (n : ℕ) :
    coeff n (X * derivative ℚ series) = (n : ℚ) * a n := by
  cases n with
  | zero => simp
  | succ n => simp [coeff_succ_X_mul, coeff_derivative, coeff_series, mul_comm]

theorem recurrence : type_of% @OMA.S_oeis_a176754.main := by
  intro n hn
  let E : ℚ⟦X⟧ := X * derivative ℚ series
  have hC (k : ℕ) : C (k : ℚ) = (k : ℚ⟦X⟧) := map_natCast C k
  have hC4 : C (4 : ℚ) = (4 : ℚ⟦X⟧) := hC 4
  have hC5 : C (5 : ℚ) = (5 : ℚ⟦X⟧) := hC 5
  have hC6 : C (6 : ℚ) = (6 : ℚ⟦X⟧) := hC 6
  have hC9 : C (9 : ℚ) = (9 : ℚ⟦X⟧) := hC 9
  have hC12 : C (12 : ℚ) = (12 : ℚ⟦X⟧) := hC 12
  have h : E - C 6 * (X * E) + C 5 * (X ^ 2 * E) + C 12 * (X ^ 3 * E) - C 12 * (X ^ 4 * E) +
      (series - C 4 * (X * series) + C 5 * (X ^ 2 * series) - C 6 * (X ^ 3 * series)) =
      1 - C 9 * X ^ 2 + C 6 * X ^ 3 := by
    calc
      _ = (1 - 6 * X + 5 * X ^ 2 + 12 * X ^ 3 - 12 * X ^ 4) * E +
          (1 - 4 * X + 5 * X ^ 2 - 6 * X ^ 3) * series := by
            rw [hC4, hC5, hC6, hC12]; ring
      _ = _ := by rw [hC6, hC9]; exact differential
  have hₙ := congrArg (coeff n) h
  have h₁ : 1 ≤ n := by omega
  have h₂ : 2 ≤ n := by omega
  have h₃ : 3 ≤ n := by omega
  have hn₀ : n ≠ 0 := by omega
  have hn₁ : n ≠ 1 := by omega
  have hn₂ : n ≠ 2 := by omega
  have hn₃ : n ≠ 3 := by omega
  have hshift (f : ℚ⟦X⟧) : coeff n (X * f) = coeff (n - 1) f := by
    simpa using (coeff_X_pow_mul' f 1 n).trans (if_pos h₁)
  simp only [map_add, map_sub, coeff_C_mul, hshift,
    coeff_X_pow_mul', if_pos h₂, if_pos h₃, if_pos hn,
    coeff_one, coeff_X_pow, if_neg hn₀, if_neg hn₁, if_neg hn₂, if_neg hn₃,
    mul_zero, add_zero, sub_zero] at hₙ
  simp only [E, euler_coeff] at hₙ
  simp only [series, coeff_mk] at hₙ
  rw [Nat.cast_sub h₁, Nat.cast_sub h₂, Nat.cast_sub h₃, Nat.cast_sub hn] at hₙ
  have hq : ((n : ℚ) + 1) * a n + 2 * (-3 * (n : ℚ) + 1) * a (n - 1) +
      5 * ((n : ℚ) - 1) * a (n - 2) + 6 * (2 * (n : ℚ) - 7) * a (n - 3) +
      12 * (-(n : ℚ) + 4) * a (n - 4) = 0 := by
    linear_combination hₙ
  exact_mod_cast hq

end A176754Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a176754.main := A176754Proof.recurrence
