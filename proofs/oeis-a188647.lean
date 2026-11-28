import OMAStatements.S_oeis_a188647

-- Problem oeis-a188647: with k = (sqrt(x^2 + y) + x)^2 for integers x >= 1 and y = 1 or -1, the sequence
-- a(0) = 1, a(n+1) = a(n) * k - (k - 1) / k^(n+1) consists of integers.
-- Upstream: statements/oeis-a188647.lean (declaration OMA.S_oeis_a188647.main)
-- Credit: @cclyles (the owner of the agent is credited as the solver)
--
-- Proof: let s = sqrt(x^2 + y), A = (s + x)^2 = k and B = (s - x)^2. Then A * B = (s^2 - x^2)^2 = 1, so
-- 1/k^(n+1) = B^(n+1), and A + B = 4 x^2 + 2 y is an integer. Hence W(n) = A^n + B^n is an integer for all n
-- (W(n+2) = (A + B) W(n+1) - W(n)). The recurrence of a gives a(n+1) + a(n) = W(n+1) by induction, so
-- a(n+1) = W(n+1) - a(n) is an integer.

open OMA.S_oeis_a188647

theorem OMA.solution : type_of% @OMA.S_oeis_a188647.main := by
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
  have hK : k x y = (s + x) ^ 2 := by
    unfold k
    rw [← hs]
  have e : ∀ (A B : ℝ) (j : ℕ), A ^ (j + 1 + 1) + B ^ (j + 1 + 1)
      = (A + B) * (A ^ (j + 1) + B ^ (j + 1)) - (A * B) * (A ^ j + B ^ j) := by
    intro A B j
    ring
  have keyW : ∀ j : ℕ, (∃ m : ℤ, ((s + x) ^ 2) ^ j + ((s - x) ^ 2) ^ j = m) ∧
      (∃ m : ℤ, ((s + x) ^ 2) ^ (j + 1) + ((s - x) ^ 2) ^ (j + 1) = m) := by
    intro j
    induction j with
    | zero =>
      refine ⟨⟨2, by norm_num⟩, ⟨4 * x ^ 2 + 2 * y, ?_⟩⟩
      simp only [zero_add, pow_one]
      push_cast
      linarith [hsum]
    | succ j ih =>
      obtain ⟨⟨m0, h0⟩, ⟨m1, h1⟩⟩ := ih
      refine ⟨⟨m1, h1⟩, ⟨(4 * x ^ 2 + 2 * y) * m1 - m0, ?_⟩⟩
      push_cast
      rw [← h0, ← h1, e ((s + x) ^ 2) ((s - x) ^ 2) j, hab, hsum]
      ring
  have h00 : a x y 0 = 1 := rfl
  have hrec : ∀ j : ℕ, a x y (j + 1)
      = a x y j * (s + x) ^ 2 - ((s + x) ^ 2 - 1) * ((s - x) ^ 2) ^ (j + 1) := by
    intro j
    have h0 : a x y (j + 1) = a x y j * k x y - (k x y - 1) / k x y ^ (j + 1) := rfl
    rw [h0, hK, div_eq_mul_inv, ← inv_pow, hinv]
  have hpair : ∀ j : ℕ, a x y (j + 1) + a x y j
      = ((s + x) ^ 2) ^ (j + 1) + ((s - x) ^ 2) ^ (j + 1) := by
    intro j
    induction j with
    | zero =>
      have h1 := hrec 0
      linear_combination h1 + (1 + (s + x) ^ 2) * h00 - hab
    | succ j ih =>
      have h2 := hrec (j + 1)
      have h1 := hrec j
      linear_combination h2 + h1 + (s + x) ^ 2 * ih - ((s - x) ^ 2) ^ (j + 1) * hab
  have hint : ∀ j : ℕ, ∃ z : ℤ, a x y j = z := by
    intro j
    induction j with
    | zero => exact ⟨1, by rw [h00]; norm_num⟩
    | succ j ih =>
      obtain ⟨z, hz⟩ := ih
      obtain ⟨w, hw⟩ := (keyW j).2
      refine ⟨w - z, ?_⟩
      push_cast
      linarith [hpair j]
  exact hint n
