import OMAStatements.S_oeis_a218263

-- Problem: A218263: Number of standard Young tableaux of n cells and height >= 3.
-- Upstream: formal-conjectures statements/oeis-a218263.lean:0 (declaration OMA.S_oeis_a218263.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! The central binomial coefficients b(n) = binomial(n, floor(n/2)) satisfy
(n+1) b(n) = 2 b(n-1) + 4 (n-1) b(n-2), and I satisfies I(n) = I(n-1) + (n-1) I(n-2). The operator of
the conjectured recurrence is a left multiple of each of these two recurrences (it is their least
common left multiple), so it annihilates both I and b, hence a = I - b. -/

namespace A218263Aux

theorem half (j : ℕ) : ((2 * j + 1).choose j : ℚ) = (Nat.centralBinom (j + 1) : ℚ) / 2 := by
  have h1 : (2 * j + 1).choose (j + 1) = (2 * j + 1).choose j := Nat.choose_symm_half j
  have h2 : Nat.centralBinom (j + 1) = (2 * j + 1).choose j + (2 * j + 1).choose (j + 1) := by
    rw [Nat.centralBinom_eq_two_mul_choose]
    have e : 2 * (j + 1) = (2 * j + 1) + 1 := by ring
    rw [e, Nat.choose_succ_succ]
  have h1' : ((2 * j + 1).choose (j + 1) : ℚ) = ((2 * j + 1).choose j : ℚ) := by exact_mod_cast h1
  have h2' : (Nat.centralBinom (j + 1) : ℚ) =
      ((2 * j + 1).choose j : ℚ) + ((2 * j + 1).choose (j + 1) : ℚ) := by exact_mod_cast h2
  linarith

theorem step (k : ℕ) : ((k : ℚ) + 1) * (Nat.centralBinom (k + 1) : ℚ) =
    2 * (2 * (k : ℚ) + 1) * (Nat.centralBinom k : ℚ) := by
  have h := Nat.succ_mul_centralBinom_succ k
  have h' : (((k + 1) * Nat.centralBinom (k + 1) : ℕ) : ℚ) =
      ((2 * (2 * k + 1) * Nat.centralBinom k : ℕ) : ℚ) := by exact_mod_cast h
  push_cast at h'
  linear_combination h'

/-- b(2j) = binomial(2j, j). -/
theorem beven (j : ℕ) : ((2 * j).choose (2 * j / 2) : ℚ) = (Nat.centralBinom j : ℚ) := by
  have e : 2 * j / 2 = j := by omega
  rw [e, Nat.centralBinom_eq_two_mul_choose]

/-- b(2j+1) = binomial(2j+2, j+1) / 2. -/
theorem bodd (j : ℕ) : ((2 * j + 1).choose ((2 * j + 1) / 2) : ℚ) =
    (Nat.centralBinom (j + 1) : ℚ) / 2 := by
  have e : (2 * j + 1) / 2 = j := by omega
  rw [e, half j]

/-- The recurrence (k+3) b(k+2) = 2 b(k+1) + 4 (k+1) b(k). -/
theorem brec (k : ℕ) : ((k : ℚ) + 3) * ((k + 2).choose ((k + 2) / 2) : ℚ) =
    2 * ((k + 1).choose ((k + 1) / 2) : ℚ) + 4 * ((k : ℚ) + 1) * (k.choose (k / 2) : ℚ) := by
  rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
  · have e1 : 2 * j + 2 = 2 * (j + 1) := by ring
    rw [e1, beven (j + 1), bodd j, beven j]
    have s := step j
    push_cast
    linear_combination 2 * s
  · have e1 : 2 * j + 1 + 2 = 2 * (j + 1) + 1 := by ring
    have e2 : 2 * j + 1 + 1 = 2 * (j + 1) := by ring
    rw [e1, e2, bodd (j + 1), beven (j + 1), bodd j]
    have s := step (j + 1)
    push_cast at s ⊢
    linear_combination s

end A218263Aux

theorem OMA.solution : type_of% @OMA.S_oeis_a218263.main := by
  intro I _ _ hI a ha n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  have e1 : m + 4 - 1 = m + 3 := rfl
  have e2 : m + 4 - 2 = m + 2 := rfl
  have e3 : m + 4 - 3 = m + 1 := rfl
  have e4 : m + 4 - 4 = m := rfl
  rw [e1, e2, e3, e4, ha (m + 4), ha (m + 3), ha (m + 2), ha (m + 1), ha m]
  have i4 := hI (m + 4) (by omega)
  have i3 := hI (m + 3) (by omega)
  have i2 := hI (m + 2) (by omega)
  have f1 : m + 3 - 1 = m + 2 := rfl
  have f2 : m + 3 - 2 = m + 1 := rfl
  have g1 : m + 2 - 1 = m + 1 := rfl
  have g2 : m + 2 - 2 = m := rfl
  rw [e1, e2] at i4
  rw [f1, f2] at i3
  rw [g1, g2] at i2
  have b4 := A218263Aux.brec (m + 2)
  have b3 := A218263Aux.brec (m + 1)
  have b2 := A218263Aux.brec m
  have z1 : m + 2 + 2 = m + 4 := rfl
  have z2 : m + 2 + 1 = m + 3 := rfl
  have z3 : m + 1 + 2 = m + 3 := rfl
  have z4 : m + 1 + 1 = m + 2 := rfl
  rw [z1, z2] at b4
  rw [z3, z4] at b3
  push_cast at i4 i3 i2 b4 b3 b2 ⊢
  linear_combination
    (((m : ℚ) + 4 - 6) * ((m : ℚ) + 4 - 3) * ((m : ℚ) + 4 + 1)) * i4 +
    ((-((m : ℚ) + 4) ^ 3 + 6 * ((m : ℚ) + 4) ^ 2 + 11 * ((m : ℚ) + 4) - 36) +
      ((m : ℚ) + 4 - 6) * ((m : ℚ) + 4 - 3) * ((m : ℚ) + 4 + 1)) * i3 +
    (-4 * ((m : ℚ) + 4 - 5) * ((m : ℚ) + 4 - 1) * ((m : ℚ) + 4 - 2)) * i2 -
    (((m : ℚ) + 4 - 6) * ((m : ℚ) + 4 - 3)) * b4 -
    (-((m : ℚ) + 4 - 1) * ((m : ℚ) + 4 - 7)) * b3 -
    (-((m : ℚ) + 4 - 5) * ((m : ℚ) + 4 - 1) * ((m : ℚ) + 4 - 2)) * b2
