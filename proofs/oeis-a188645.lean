import OMAStatements.S_oeis_a188645

-- Problem oeis-a188645: for integers x >= 1, y = 1 or -1 and k = (sqrt(x^2 + y) + x)^2, the number
-- (k^n + k^(-n)) / 2 is an integer for every n >= 0.
-- Upstream: statements/oeis-a188645.lean (declaration OMA.S_oeis_a188645.main)
-- Credit: @cclyles (the owner of the agent is credited as the solver)
--
-- Proof: let s = sqrt(x^2 + y), A = (s + x)^2 and B = (s - x)^2. Then A * B = (s^2 - x^2)^2 = y^2 = 1, so B = 1/A,
-- and A + B = 2 s^2 + 2 x^2 = 4 x^2 + 2 y is an integer. T(n) = (A^n + B^n) / 2 satisfies T(0) = 1,
-- T(1) = 2 x^2 + y and T(n+2) = (A + B) T(n+1) - A B T(n), so every T(n) is an integer by induction.

open OMA.S_oeis_a188645

theorem OMA.solution : type_of% @OMA.S_oeis_a188645.main := by
  intro x y hx hy n
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hy2 : (y : ℝ) ^ 2 = 1 := by
    rcases hy with rfl | rfl <;> norm_num
  have hnn : (0 : ℝ) ≤ (x : ℝ) ^ 2 + y := by
    rcases hy with rfl | rfl <;> push_cast <;> nlinarith
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = Real.sqrt ((x : ℝ) ^ 2 + y) := ⟨_, rfl⟩
  have hs2 : s ^ 2 = (x : ℝ) ^ 2 + y := by
    rw [hs]
    exact Real.sq_sqrt hnn
  have h5 : (s + x) * (s - x) = y := by linear_combination hs2
  have hab : (s + x) ^ 2 * (s - x) ^ 2 = 1 := by
    calc (s + x) ^ 2 * (s - x) ^ 2 = ((s + x) * (s - x)) ^ 2 := by ring
      _ = 1 := by rw [h5, hy2]
  have hsum : (s + x) ^ 2 + (s - x) ^ 2 = 4 * (x : ℝ) ^ 2 + 2 * y := by linear_combination 2 * hs2
  have hinv : ((s + x) ^ 2)⁻¹ = (s - x) ^ 2 := (eq_inv_of_mul_eq_one_right hab).symm
  have e : ∀ (A B : ℝ) (j : ℕ), A ^ (j + 1 + 1) + B ^ (j + 1 + 1)
      = (A + B) * (A ^ (j + 1) + B ^ (j + 1)) - (A * B) * (A ^ j + B ^ j) := by
    intro A B j
    ring
  have key : ∀ j : ℕ, (∃ m : ℤ, (((s + x) ^ 2) ^ j + ((s - x) ^ 2) ^ j) / 2 = m) ∧
      (∃ m : ℤ, (((s + x) ^ 2) ^ (j + 1) + ((s - x) ^ 2) ^ (j + 1)) / 2 = m) := by
    intro j
    induction j with
    | zero =>
      refine ⟨⟨1, by norm_num⟩, ⟨2 * x ^ 2 + y, ?_⟩⟩
      simp only [zero_add, pow_one]
      push_cast
      linarith [hsum]
    | succ j ih =>
      obtain ⟨⟨m0, h0⟩, ⟨m1, h1⟩⟩ := ih
      refine ⟨⟨m1, h1⟩, ⟨(4 * x ^ 2 + 2 * y) * m1 - m0, ?_⟩⟩
      push_cast
      rw [← h0, ← h1, e ((s + x) ^ 2) ((s - x) ^ 2) j, hab, hsum]
      ring
  obtain ⟨m, hm⟩ := (key n).1
  refine ⟨m, ?_⟩
  rw [← hm]
  unfold k
  rw [← hs, zpow_neg, zpow_natCast, ← inv_pow, hinv]
