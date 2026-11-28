import OMAStatements.S_oeis_a060774

-- Problem: A060774: a(n) = number of lattice paths from (0,0,0) to (n,n,n) along the cracks on the surface of a Rubik-ized n X n X n cube so that no step increases distance from goal.
-- Upstream: formal-conjectures statements/oeis-a060774.lean:0 (declaration OMA.S_oeis_a060774.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Both C(3n, n) and C(2n, n) satisfy first-order recurrences with polynomial coefficients
(hB1, hC1). Each of Mathar's recurrences is a polynomial combination of shifted copies of these two
relations, which is checked by `linear_combination`. -/

namespace A060774Aux

open OMA.S_oeis_a060774

theorem hB1 (m : ℕ) :
    2 * ((m : ℚ) + 1) * (2 * (m : ℚ) + 1) * ((3 * (m + 1)).choose (m + 1) : ℚ) =
      3 * (3 * (m : ℚ) + 1) * (3 * (m : ℚ) + 2) * ((3 * m).choose m : ℚ) := by
  have h1 : ((3 * m).choose m : ℚ) * (m.factorial : ℚ) * ((2 * m).factorial : ℚ) =
      ((3 * m).factorial : ℚ) := by
    have h := Nat.choose_mul_factorial_mul_factorial (show m ≤ 3 * m by omega)
    have e : 3 * m - m = 2 * m := by omega
    rw [e] at h
    exact_mod_cast h
  have h2 : ((3 * (m + 1)).choose (m + 1) : ℚ) * ((m + 1).factorial : ℚ) *
      ((2 * (m + 1)).factorial : ℚ) = ((3 * (m + 1)).factorial : ℚ) := by
    have h := Nat.choose_mul_factorial_mul_factorial (show m + 1 ≤ 3 * (m + 1) by omega)
    have e : 3 * (m + 1) - (m + 1) = 2 * (m + 1) := by omega
    rw [e] at h
    exact_mod_cast h
  have f1 : ((m + 1).factorial : ℚ) = ((m : ℚ) + 1) * (m.factorial : ℚ) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  have f2 : ((2 * (m + 1)).factorial : ℚ) =
      (2 * (m : ℚ) + 2) * (2 * (m : ℚ) + 1) * ((2 * m).factorial : ℚ) := by
    have e : 2 * (m + 1) = 2 * m + 1 + 1 := by ring
    rw [e, Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    ring
  have f3 : ((3 * (m + 1)).factorial : ℚ) =
      (3 * (m : ℚ) + 3) * (3 * (m : ℚ) + 2) * (3 * (m : ℚ) + 1) * ((3 * m).factorial : ℚ) := by
    have e : 3 * (m + 1) = 3 * m + 2 + 1 := by ring
    rw [e, Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    ring
  rw [f1, f2, f3] at h2
  have p1 : (m.factorial : ℚ) ≠ 0 := by positivity
  have p2 : ((2 * m).factorial : ℚ) ≠ 0 := by positivity
  have p3 : (m : ℚ) + 1 ≠ 0 := by positivity
  have p : ((m : ℚ) + 1) * (m.factorial : ℚ) * ((2 * m).factorial : ℚ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero p3 p1) p2
  apply mul_left_cancel₀ p
  linear_combination h2 - (3 * (m : ℚ) + 3) * (3 * (m : ℚ) + 2) * (3 * (m : ℚ) + 1) * h1

theorem hC1 (m : ℕ) :
    ((m : ℚ) + 1) * ((2 * (m + 1)).choose (m + 1) : ℚ) =
      2 * (2 * (m : ℚ) + 1) * ((2 * m).choose m : ℚ) := by
  have h := Nat.succ_mul_centralBinom_succ m
  rw [Nat.centralBinom_eq_two_mul_choose, Nat.centralBinom_eq_two_mul_choose] at h
  exact_mod_cast h

theorem hB2 (m : ℕ) :
    2 * (((m : ℚ) + 1) + 1) * (2 * ((m : ℚ) + 1) + 1) * ((3 * (m + 2)).choose (m + 2) : ℚ) =
      3 * (3 * ((m : ℚ) + 1) + 1) * (3 * ((m : ℚ) + 1) + 2) * ((3 * (m + 1)).choose (m + 1) : ℚ) := by
  have h := hB1 (m + 1)
  have e : ((m + 1 : ℕ) : ℚ) = (m : ℚ) + 1 := by push_cast; ring
  rw [e] at h
  exact h

theorem hC2 (m : ℕ) :
    (((m : ℚ) + 1) + 1) * ((2 * (m + 2)).choose (m + 2) : ℚ) =
      2 * (2 * ((m : ℚ) + 1) + 1) * ((2 * (m + 1)).choose (m + 1) : ℚ) := by
  have h := hC1 (m + 1)
  have e : ((m + 1 : ℕ) : ℚ) = (m : ℚ) + 1 := by push_cast; ring
  rw [e] at h
  exact h

theorem hB3 (m : ℕ) :
    2 * (((m : ℚ) + 2) + 1) * (2 * ((m : ℚ) + 2) + 1) * ((3 * (m + 3)).choose (m + 3) : ℚ) =
      3 * (3 * ((m : ℚ) + 2) + 1) * (3 * ((m : ℚ) + 2) + 2) * ((3 * (m + 2)).choose (m + 2) : ℚ) := by
  have h := hB1 (m + 2)
  have e : ((m + 2 : ℕ) : ℚ) = (m : ℚ) + 2 := by push_cast; ring
  rw [e] at h
  exact h

theorem hC3 (m : ℕ) :
    (((m : ℚ) + 2) + 1) * ((2 * (m + 3)).choose (m + 3) : ℚ) =
      2 * (2 * ((m : ℚ) + 2) + 1) * ((2 * (m + 2)).choose (m + 2) : ℚ) := by
  have h := hC1 (m + 2)
  have e : ((m + 2 : ℕ) : ℚ) = (m : ℚ) + 2 := by push_cast; ring
  rw [e] at h
  exact h

theorem hB4 (m : ℕ) :
    2 * (((m : ℚ) + 3) + 1) * (2 * ((m : ℚ) + 3) + 1) * ((3 * (m + 4)).choose (m + 4) : ℚ) =
      3 * (3 * ((m : ℚ) + 3) + 1) * (3 * ((m : ℚ) + 3) + 2) * ((3 * (m + 3)).choose (m + 3) : ℚ) := by
  have h := hB1 (m + 3)
  have e : ((m + 3 : ℕ) : ℚ) = (m : ℚ) + 3 := by push_cast; ring
  rw [e] at h
  exact h

theorem hC4 (m : ℕ) :
    (((m : ℚ) + 3) + 1) * ((2 * (m + 4)).choose (m + 4) : ℚ) =
      2 * (2 * ((m : ℚ) + 3) + 1) * ((2 * (m + 3)).choose (m + 3) : ℚ) := by
  have h := hC1 (m + 3)
  have e : ((m + 3 : ℕ) : ℚ) = (m : ℚ) + 3 := by push_cast; ring
  rw [e] at h
  exact h

/-- The closed form without the special value at 0. -/
def f (k : ℕ) : ℚ := 6 * ((3 * k).choose k : ℚ) - 6 * ((2 * k).choose k : ℚ)

theorem af (k : ℕ) (hk : k ≠ 0) : (a k : ℚ) = f k := by
  simp [a, f, hk]

theorem pure4 (m : ℕ) :
    2 * ((m : ℚ)  +  4) * (2 * ((m : ℚ)  +  4) - 1) * (((m : ℚ)  +  4) - 1) * f (m + 4)
      + (((m : ℚ)  +  4) - 1) * (13 * ((m : ℚ)  +  4) ^ 2 - 209 * ((m : ℚ)  +  4) + 258) * f (m + 3)
      + 2 * (-259 * ((m : ℚ)  +  4) ^ 3 + 1785 * ((m : ℚ)  +  4) ^ 2 - 3728 * ((m : ℚ)  +  4) + 2460) * f (m + 2)
      + 6 * (295 * ((m : ℚ)  +  4) ^ 3 - 2068 * ((m : ℚ)  +  4) ^ 2 + 4833 * ((m : ℚ)  +  4) - 3780) * f (m + 1)
      - 36 * (3 * ((m : ℚ)  +  4) - 10) * (2 * ((m : ℚ)  +  4) - 7) * (3 * ((m : ℚ)  +  4) - 11) * f m = 0 := by
  unfold f
  linear_combination (18 + 6 * (m : ℚ)) * hB4 m
    + (-252 - 156 * (m : ℚ) - 24 * (m : ℚ) ^ 2) * hC4 m
    + (-24 + 60 * (m : ℚ)) * hB3 m
    + (1044 - 42 * (m : ℚ) - 174 * (m : ℚ) ^ 2) * hC3 m
    + (-804 - 372 * (m : ℚ)) * hB2 m
    + (8028 + 9144 * (m : ℚ) + 2412 * (m : ℚ) ^ 2) * hC2 m
    + (72 + 144 * (m : ℚ)) * hB1 m
    + (-216 - 972 * (m : ℚ) - 972 * (m : ℚ) ^ 2) * hC1 m

theorem pure2 (m : ℕ) :
    2 * ((m : ℚ)  +  2) * (((m : ℚ)  +  2) - 1) * (2 * ((m : ℚ)  +  2) - 1) * (11 * ((m : ℚ)  +  2) ^ 2 - 33 * ((m : ℚ)  +  2) + 24) * f (m + 2)
      - (((m : ℚ)  +  2) - 1) * (473 * ((m : ℚ)  +  2) ^ 4 - 1892 * ((m : ℚ)  +  2) ^ 3 + 2561 * ((m : ℚ)  +  2) ^ 2 - 1338 * ((m : ℚ)  +  2) + 216) * f (m + 1)
      + 6 * (3 * ((m : ℚ)  +  2) - 5) * (3 * ((m : ℚ)  +  2) - 4) * (2 * ((m : ℚ)  +  2) - 3) * (11 * ((m : ℚ)  +  2) ^ 2 - 11 * ((m : ℚ)  +  2) + 2) * f m = 0 := by
  unfold f
  linear_combination (12 + 78 * (m : ℚ) + 132 * (m : ℚ) ^ 2 + 66 * (m : ℚ) ^ 3) * hB2 m
    + (-72 - 516 * (m : ℚ) - 1104 * (m : ℚ) ^ 2 - 924 * (m : ℚ) ^ 3 - 264 * (m : ℚ) ^ 4) * hC2 m
    + (-288 - 972 * (m : ℚ) - 924 * (m : ℚ) ^ 2 - 264 * (m : ℚ) ^ 3) * hB1 m
    + (864 + 5076 * (m : ℚ) + 9630 * (m : ℚ) ^ 2 + 7128 * (m : ℚ) ^ 3 + 1782 * (m : ℚ) ^ 4) * hC1 m

end A060774Aux

open A060774Aux in
theorem OMA.solution : type_of% @OMA.S_oeis_a060774.main := by
  refine ⟨?_, ?_⟩
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    have hm : m ≠ 0 := by omega
    have e1 : m + 4 - 1 = m + 3 := rfl
    have e2 : m + 4 - 2 = m + 2 := rfl
    have e3 : m + 4 - 3 = m + 1 := rfl
    have e4 : m + 4 - 4 = m := rfl
    rw [e1, e2, e3, e4]
    have a4 := af (m + 4) (by omega)
    have a3 := af (m + 3) (by omega)
    have a2 := af (m + 2) (by omega)
    have a1 := af (m + 1) (by omega)
    have a0 := af m hm
    apply Int.cast_injective (α := ℚ)
    push_cast
    rw [a4, a3, a2, a1, a0]
    linear_combination pure4 m
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    have hm : m ≠ 0 := by omega
    have e1 : m + 2 - 1 = m + 1 := rfl
    have e2 : m + 2 - 2 = m := rfl
    rw [e1, e2]
    have a2 := af (m + 2) (by omega)
    have a1 := af (m + 1) (by omega)
    have a0 := af m hm
    apply Int.cast_injective (α := ℚ)
    push_cast
    rw [a2, a1, a0]
    linear_combination pure2 m
