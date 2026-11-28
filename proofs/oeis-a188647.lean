import OMAStatements.S_oeis_a188647

def a188647_b (c : ℤ) : ℕ → ℤ
  | 0 => 1
  | 1 => c - 1
  | n + 2 => c * a188647_b c (n + 1) - a188647_b c n

theorem OMA.solution : type_of% @OMA.S_oeis_a188647.main := by
  intro x y hx hy
  have hxr : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hy2 : (y : ℝ) ^ 2 = 1 := by rcases hy with rfl | rfl <;> norm_num
  have hrad : (0 : ℝ) ≤ (x : ℝ) ^ 2 + y := by
    rcases hy with rfl | rfl <;> push_cast <;> nlinarith
  set s := Real.sqrt ((x : ℝ) ^ 2 + y) with hs
  have hs2 : s ^ 2 = (x : ℝ) ^ 2 + y := Real.sq_sqrt hrad
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  set K := OMA.S_oeis_a188647.k x y with hKdef
  have hK : K = (s + x) ^ 2 := rfl
  have hKpos : 0 < K := by rw [hK]; positivity
  have hKinv : K * (x - s) ^ 2 = 1 := by
    rw [hK, ← mul_pow]
    have : (s + x) * (x - s) = -(y : ℝ) := by nlinarith
    rw [this, neg_sq, hy2]
  have hc : K + K⁻¹ = ((4 * x ^ 2 + 2 * y : ℤ) : ℝ) := by
    have : K⁻¹ = (x - s) ^ 2 := by
      exact inv_eq_of_mul_eq_one_right hKinv
    rw [this, hK]; push_cast; nlinarith
  have closed : ∀ n : ℕ, OMA.S_oeis_a188647.a x y n = (K ^ (n + 1) + (K ^ n)⁻¹) / (K + 1) := by
    intro n
    induction n with
    | zero => simp [OMA.S_oeis_a188647.a]; field_simp
    | succ n ih =>
      rw [OMA.S_oeis_a188647.a, ih, ← hKdef]
      field_simp
      ring
  set c : ℤ := 4 * x ^ 2 + 2 * y with hcdef
  have key : ∀ n : ℕ, OMA.S_oeis_a188647.a x y n = a188647_b c n ∧
      OMA.S_oeis_a188647.a x y (n + 1) = a188647_b c (n + 1) := by
    intro n
    induction n with
    | zero =>
      refine ⟨by simp [OMA.S_oeis_a188647.a, a188647_b], ?_⟩
      rw [closed]
      simp only [a188647_b]
      push_cast
      rw [← hc]
      field_simp
      ring
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      simp only [a188647_b]
      push_cast
      rw [← ih.1, ← ih.2, ← hc, closed, closed, closed]
      field_simp
      ring
  exact fun n => ⟨_, (key n).1⟩
