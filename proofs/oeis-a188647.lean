import OMAStatements.S_oeis_a188647

-- Problem: A188647: Array read by antidiagonals of a(n) = a(n-1)*k-((k-1)/(k^n)) where a(0)=1 and k=(sqrt(x^2+1)+x)^2 for integers x>=1.
-- Upstream: formal-conjectures statements/oeis-a188647.lean:0 (declaration OMA.S_oeis_a188647.main)
-- Credit: @amtamaddon (the owner of the agent is credited as the solver)

open OMA.S_oeis_a188647

theorem OMA.solution : type_of% @OMA.S_oeis_a188647.main := by
  intro x y hx hy n
  have hy2 : ((y : ℝ)) ^ 2 = 1 := by
    rcases hy with rfl | rfl <;> norm_num
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hnn : (0 : ℝ) ≤ (x : ℝ) ^ 2 + y := by
    rcases hy with rfl | rfl <;> push_cast <;> nlinarith
  have hss : (Real.sqrt ((x : ℝ) ^ 2 + y)) ^ 2 = (x : ℝ) ^ 2 + y := Real.sq_sqrt hnn
  have hk : k x y = (Real.sqrt ((x : ℝ) ^ 2 + y) + x) ^ 2 := rfl
  generalize Real.sqrt ((x : ℝ) ^ 2 + y) = s at hss hk
  have hkv : k x y * (x - s) ^ 2 = 1 := by
    rw [hk]
    have e : (s + x) ^ 2 * (x - s) ^ 2 = (x ^ 2 - s ^ 2) ^ 2 := by ring
    rw [e, hss]
    have e2 : ((x : ℝ) ^ 2 - (x ^ 2 + y)) ^ 2 = (y : ℝ) ^ 2 := by ring
    rw [e2, hy2]
  have hk0 : k x y ≠ 0 := by
    intro h
    rw [h] at hkv
    simp at hkv
  have hinv : 1 / k x y = (x - s) ^ 2 := by
    rw [div_eq_iff hk0]
    linarith
  have hm : k x y + 1 / k x y = ((4 * x ^ 2 + 2 * y : ℤ) : ℝ) := by
    rw [hinv, hk]
    push_cast
    linear_combination 2 * hss
  have hrec : ∀ n, a x y (n + 2) = (k x y + 1 / k x y) * a x y (n + 1) - a x y n := by
    intro n
    have e1 : a x y (n + 2) = a x y (n + 1) * k x y - (k x y - 1) / k x y ^ (n + 2) := rfl
    have e2 : a x y (n + 1) = a x y n * k x y - (k x y - 1) / k x y ^ (n + 1) := rfl
    have e3 : (k x y - 1) / k x y ^ (n + 2) = (a x y n * k x y - a x y (n + 1)) / k x y := by
      rw [e2]
      field_simp
      ring
    rw [e1, e3]
    field_simp
    ring
  have key : ∀ n, (∃ z : ℤ, a x y n = z) ∧ (∃ z : ℤ, a x y (n + 1) = z) := by
    intro n
    induction n with
    | zero =>
      refine ⟨⟨1, by simp [a]⟩, ⟨4 * x ^ 2 + 2 * y - 1, ?_⟩⟩
      have e : a x y 1 = k x y + 1 / k x y - 1 := by
        have e0 : a x y 1 = 1 * k x y - (k x y - 1) / k x y ^ (0 + 1) := rfl
        rw [e0]
        field_simp
        ring
      rw [e, hm]
      push_cast
      ring
    | succ n ih =>
      obtain ⟨⟨z1, h1⟩, ⟨z2, h2⟩⟩ := ih
      refine ⟨⟨z2, h2⟩, ⟨(4 * x ^ 2 + 2 * y) * z2 - z1, ?_⟩⟩
      rw [hrec, hm, h1, h2]
      push_cast
      ring
  exact (key n).1
