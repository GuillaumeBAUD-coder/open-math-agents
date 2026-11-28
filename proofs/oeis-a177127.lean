import OMAStatements.S_oeis_a177127
import Mathlib

/-!
# OEIS A177127: Mathar's recurrence, from the algebraic generating function

The sequence is `a(0) = 1`, `a(1) = 6` and `a(n+2) = ∑_{p ≤ n+1} a(p) a(n+1-p) + 1`, so the
generating function `F` satisfies `F = 1 + 6X + X F² - X + X²/(1-X)`, i.e.
`(1 - X) (F - X F²) = 1 + 4X - 4X²`. Writing `S = (1-X)(1-2XF)` one gets
`S² = 1 - 6X - 11X² + 32X³ - 16X⁴ =: P`, hence `2 P S' = S P'`; substituting
`S' = -1 + (4X-2) F - 2X(1-X) F'` turns this into a linear differential equation for `F`,
whose coefficient extraction is Mathar's recurrence.

Source: https://oeis.org/A177127
-/

namespace A177127Proof

open OMA.S_oeis_a177127 PowerSeries

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
    a (n + 2) = (∑ k ∈ Finset.range (n + 2), a k * a (n + 1 - k)) + 1 := by
  unfold a at ⊢
  rw [aList, List.getD_append_right _ _ _ _ (by rw [prefix_length])]
  rw [prefix_length]
  simp only [Nat.sub_self]
  change _ + 1 = _ + 1
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  have hk' := Finset.mem_range.mp hk
  change (aList (n + 1)).getD k 0 * (aList (n + 1)).getD (n + 1 - k) 0 =
    a k * a (n + 1 - k)
  rw [prefix_value _ _ (by omega), prefix_value _ _ (by omega)]

private noncomputable def series : ℚ⟦X⟧ := mk fun n => (a n : ℚ)

private theorem quadratic :
    (1 - X) * (series - X * series ^ 2) = 1 + 4 * X - 4 * X ^ 2 := by
  let F := series - X * series ^ 2
  have hF (n : ℕ) : coeff (n + 2) F = 1 := by
    change coeff (n + 1).succ (series - X * series ^ 2) = 1
    rw [map_sub, coeff_succ_X_mul]
    simp only [series, coeff_mk, pow_two, coeff_mul]
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => (a i : ℚ) * a j)]
    have h := congrArg (fun z : ℤ => (z : ℚ)) (convolution n)
    push_cast at h
    linarith
  have hF₀ : coeff 0 F = 1 := by
    simp [F, series, a, aList]
  have hF₁ : coeff 1 F = 5 := by
    change coeff (Nat.succ 0) (series - X * series ^ 2) = 5
    rw [map_sub, coeff_succ_X_mul]
    norm_num [series, a, aList]
  have h4X : (4 : ℚ⟦X⟧) = C (4 : ℚ) := (map_natCast C 4).symm
  change (1 - X) * F = 1 + 4 * X - 4 * X ^ 2
  rw [h4X, sub_mul, one_mul]
  ext n
  rcases n with _ | _ | _ | n
  · simp [coeff_X, coeff_C_mul]
    exact (coeff_zero_eq_constantCoeff_apply F) ▸ hF₀
  · simp [hF₀, hF₁, coeff_X, coeff_X_pow, coeff_C_mul, coeff_succ_X_mul]
    norm_num
  · simp [hF₁, hF 0, coeff_X, coeff_X_pow, coeff_C_mul, coeff_succ_X_mul]
    norm_num
  · have hn₂ : n + 3 ≠ 2 := by omega
    change coeff (n + 3) (F - X * F) = _
    simp [hF (n + 1), hF n, hn₂, coeff_one, coeff_X, coeff_X_pow]

private theorem differential :
    (1 - 6 * X - 11 * X ^ 2 + 32 * X ^ 3 - 16 * X ^ 4) * (X * derivative ℚ series) +
      (1 - 4 * X + 5 * X ^ 2) * series = 1 + 8 * X - 16 * X ^ 2 + 8 * X ^ 3 := by
  let S : ℚ⟦X⟧ := (1 - X) * (1 - 2 * X * series)
  let P : ℚ⟦X⟧ := 1 - 6 * X - 11 * X ^ 2 + 32 * X ^ 3 - 16 * X ^ 4
  let Q : ℚ⟦X⟧ := 1 - 5 * X - 16 * X ^ 2 + 16 * X ^ 3
  have hS : S ^ 2 = P := calc
    S ^ 2 = (1 - X) ^ 2 - 4 * X * (1 - X) * ((1 - X) * (series - X * series ^ 2)) := by
      dsimp [S]
      ring
    _ = P := by rw [quadratic]; dsimp [P]; ring
  have hP : P = (1 - X) * Q := by dsimp [P, Q]; ring
  have dh : 2 * S * derivative ℚ S = derivative ℚ P := by
    have h := congrArg (derivative ℚ) hS
    simpa [derivative_pow, mul_assoc] using h
  have hd : 2 * P * derivative ℚ S = S * derivative ℚ P := calc
    2 * P * derivative ℚ S = S * (2 * S * derivative ℚ S) := by rw [← hS]; ring
    _ = _ := by rw [dh]
  have dNat (k : ℕ) : derivative ℚ (k : ℚ⟦X⟧) = 0 := (derivative ℚ).map_natCast k
  have d₂ : derivative ℚ (2 : ℚ⟦X⟧) = 0 := dNat 2
  have d₄ : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dNat 4
  have d₆ : derivative ℚ (6 : ℚ⟦X⟧) = 0 := dNat 6
  have d₁₁ : derivative ℚ (11 : ℚ⟦X⟧) = 0 := dNat 11
  have d₁₆ : derivative ℚ (16 : ℚ⟦X⟧) = 0 := dNat 16
  have d₃₂ : derivative ℚ (32 : ℚ⟦X⟧) = 0 := dNat 32
  have hdS : derivative ℚ S = -1 + (4 * X - 2) * series -
      2 * X * (1 - X) * derivative ℚ series := by
    simp [S, Derivation.leibniz, smul_eq_mul, d₂]
    ring
  have hdP : derivative ℚ P = -6 - 22 * X + 96 * X ^ 2 - 64 * X ^ 3 := by
    simp [P, Derivation.leibniz, smul_eq_mul, d₆, d₁₁, d₁₆, d₃₂]
    ring
  have hx : (1 - X : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have h₀ := congrArg (coeff 0) h
    simp at h₀
  have h₄ : (4 : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have h' := congrArg (constantCoeff (R := ℚ)) h
    change constantCoeff ((4 : ℕ) : ℚ⟦X⟧) = 0 at h'
    rw [map_natCast] at h'
    norm_num at h'
  apply mul_left_cancel₀ (a := (4 : ℚ⟦X⟧) * (1 - X)) (mul_ne_zero h₄ hx)
  rw [hdS, hdP] at hd
  dsimp [S] at hd
  rw [hP] at hd
  dsimp [Q] at hd
  linear_combination -hd

private theorem euler_coeff (n : ℕ) :
    coeff n (X * derivative ℚ series) = (n : ℚ) * a n := by
  cases n with
  | zero => simp
  | succ n => simp [coeff_succ_X_mul, coeff_derivative, series, mul_comm]

theorem recurrence : type_of% @OMA.S_oeis_a177127.main := by
  intro n hn
  let E : ℚ⟦X⟧ := X * derivative ℚ series
  have hC (k : ℕ) : C (k : ℚ) = (k : ℚ⟦X⟧) := map_natCast C k
  have hC₄ : C (4 : ℚ) = (4 : ℚ⟦X⟧) := hC 4
  have hC₅ : C (5 : ℚ) = (5 : ℚ⟦X⟧) := hC 5
  have hC₆ : C (6 : ℚ) = (6 : ℚ⟦X⟧) := hC 6
  have hC₈ : C (8 : ℚ) = (8 : ℚ⟦X⟧) := hC 8
  have hC₁₁ : C (11 : ℚ) = (11 : ℚ⟦X⟧) := hC 11
  have hC₁₆ : C (16 : ℚ) = (16 : ℚ⟦X⟧) := hC 16
  have hC₃₂ : C (32 : ℚ) = (32 : ℚ⟦X⟧) := hC 32
  have h : E - C 6 * (X * E) - C 11 * (X ^ 2 * E) + C 32 * (X ^ 3 * E) - C 16 * (X ^ 4 * E) +
      (series - C 4 * (X * series) + C 5 * (X ^ 2 * series)) =
      1 + C 8 * X - C 16 * X ^ 2 + C 8 * X ^ 3 := by
    calc
      _ = (1 - 6 * X - 11 * X ^ 2 + 32 * X ^ 3 - 16 * X ^ 4) * E +
          (1 - 4 * X + 5 * X ^ 2) * series := by rw [hC₆, hC₁₁, hC₃₂, hC₁₆, hC₄, hC₅]; ring
      _ = _ := by rw [hC₈, hC₁₆]; exact differential
  have hₙ := congrArg (coeff n) h
  have h₁ : 1 ≤ n := by omega
  have h₂ : 2 ≤ n := by omega
  have h₃ : 3 ≤ n := by omega
  have h₄' : 4 ≤ n := by omega
  have hn₀ : n ≠ 0 := by omega
  have hn₁ : n ≠ 1 := by omega
  have hn₂ : n ≠ 2 := by omega
  have hn₃ : n ≠ 3 := by omega
  have hshift (f : ℚ⟦X⟧) : coeff n (X * f) = coeff (n - 1) f := by
    simpa using (coeff_X_pow_mul' f 1 n).trans (if_pos h₁)
  simp only [map_add, map_sub, coeff_C_mul, hshift,
    coeff_X_pow_mul', if_pos h₂, if_pos h₃, if_pos h₄', coeff_X,
    coeff_one, coeff_X_pow, if_neg hn₀, if_neg hn₁, if_neg hn₂, if_neg hn₃,
    mul_zero, add_zero, sub_zero] at hₙ
  simp only [E, euler_coeff] at hₙ
  simp only [series, coeff_mk] at hₙ
  rw [Nat.cast_sub h₁, Nat.cast_sub h₂, Nat.cast_sub h₃, Nat.cast_sub hn] at hₙ
  have hq : (((n : ℚ)) + 1) * a n + 2 * (-3 * (n : ℚ) + 1) * a (n - 1) +
      (-11 * (n : ℚ) + 27) * a (n - 2) + 32 * ((n : ℚ) - 3) * a (n - 3) +
      16 * (-(n : ℚ) + 4) * a (n - 4) = 0 := by
    linear_combination hₙ
  exact_mod_cast hq

end A177127Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a177127.main := A177127Proof.recurrence
