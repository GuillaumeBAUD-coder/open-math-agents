import OMAStatements.S_oeis_a005522

-- Problem: A005522: a(n) = 1 + L(n) + F(2*n-1) with {L(n)}_{n>=0} the Lucas numbers (A000032) and F(2*n-1)_{n>=0} the bisected Fibonacci numbers (A001519).
-- Upstream: formal-conjectures statements/oeis-a005522.lean:0 (declaration OMA.S_oeis_a005522.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Put b(n) = a(n+1) = 1 + L(n+1) + F(2n+1). The three parts are annihilated by E - 1,
E^2 - E - 1 and E^2 - 3E + 1, so b satisfies the recurrence with operator
(E - 1)(E^2 - 3E + 1)(E^2 - E - 1). The g.f. identity is this recurrence read coefficientwise, with
the first five coefficients checked directly. -/

namespace A005522Aux

open OMA.S_oeis_a005522 PowerSeries

theorem pstep (j : ℕ) : (Nat.fib (2 * (j + 2) + 1) : ℤ) =
    3 * (Nat.fib (2 * (j + 1) + 1) : ℤ) - (Nat.fib (2 * j + 1) : ℤ) := by
  have h1 : Nat.fib (2 * j + 3 + 2) = Nat.fib (2 * j + 3) + Nat.fib (2 * j + 3 + 1) := Nat.fib_add_two
  have h2 : Nat.fib (2 * j + 2 + 2) = Nat.fib (2 * j + 2) + Nat.fib (2 * j + 2 + 1) := Nat.fib_add_two
  have h3 : Nat.fib (2 * j + 1 + 2) = Nat.fib (2 * j + 1) + Nat.fib (2 * j + 1 + 1) := Nat.fib_add_two
  have e5 : 2 * (j + 2) + 1 = 2 * j + 3 + 2 := by ring
  have e3 : 2 * (j + 1) + 1 = 2 * j + 3 := by ring
  rw [e5, e3]
  have h1q : (Nat.fib (2 * j + 3 + 2) : ℤ) = Nat.fib (2 * j + 3) + Nat.fib (2 * j + 4) := by
    exact_mod_cast h1
  have h2q : (Nat.fib (2 * j + 4) : ℤ) = Nat.fib (2 * j + 2) + Nat.fib (2 * j + 3) := by
    exact_mod_cast h2
  have h3q : (Nat.fib (2 * j + 3) : ℤ) = Nat.fib (2 * j + 1) + Nat.fib (2 * j + 2) := by
    exact_mod_cast h3
  linear_combination h1q + h2q - h3q

/-- b(n) = a(n+1). -/
def b (n : ℕ) : ℤ := 1 + lucas (n + 1) + (Nat.fib (2 * n + 1) : ℤ)

theorem ab (n : ℕ) : a (n + 1) = b n := by
  have e : 2 * (n + 1) - 1 = 2 * n + 1 := by omega
  have h : ¬ (n + 1 = 0) := by omega
  unfold a b
  rw [if_neg h, e]

theorem rec (n : ℕ) : b (n + 5) = 5 * b (n + 4) - 7 * b (n + 3) + b (n + 2) + 3 * b (n + 1) - b n := by
  have p0 : (Nat.fib (2 * (n + 2) + 1) : ℤ) = 3 * (Nat.fib (2 * (n + 1) + 1) : ℤ) - (Nat.fib (2 * n + 1) : ℤ) := pstep n
  have p1 : (Nat.fib (2 * (n + 3) + 1) : ℤ) = 3 * (Nat.fib (2 * (n + 2) + 1) : ℤ) - (Nat.fib (2 * (n + 1) + 1) : ℤ) := pstep (n + 1)
  have p2 : (Nat.fib (2 * (n + 4) + 1) : ℤ) = 3 * (Nat.fib (2 * (n + 3) + 1) : ℤ) - (Nat.fib (2 * (n + 2) + 1) : ℤ) := pstep (n + 2)
  have p3 : (Nat.fib (2 * (n + 5) + 1) : ℤ) = 3 * (Nat.fib (2 * (n + 4) + 1) : ℤ) - (Nat.fib (2 * (n + 3) + 1) : ℤ) := pstep (n + 3)
  have q0 : lucas (n + 2 + 1) = lucas (n + 1 + 1) + lucas (n + 1) := rfl
  have q1 : lucas (n + 3 + 1) = lucas (n + 2 + 1) + lucas (n + 1 + 1) := rfl
  have q2 : lucas (n + 4 + 1) = lucas (n + 3 + 1) + lucas (n + 2 + 1) := rfl
  have q3 : lucas (n + 5 + 1) = lucas (n + 4 + 1) + lucas (n + 3 + 1) := rfl
  simp only [b]
  linear_combination (1) * p0 + (0) * p1 + (-2) * p2 + (1) * p3 + (-1) * q0 + (4) * q1 + (-4) * q2 + (1) * q3

theorem b0 : b 0 = 3 := by decide
theorem b1 : b 1 = 6 := by decide
theorem b2 : b 2 = 10 := by decide
theorem b3 : b 3 = 21 := by decide
theorem b4 : b 4 = 46 := by decide

theorem gfC : PowerSeries.mk (fun n => (b n : ℚ)) * C 1 +
    PowerSeries.mk (fun n => (b n : ℚ)) * X * C (-5) +
    PowerSeries.mk (fun n => (b n : ℚ)) * X * X * C 7 +
    PowerSeries.mk (fun n => (b n : ℚ)) * X * X * X * C (-1) +
    PowerSeries.mk (fun n => (b n : ℚ)) * X * X * X * X * C (-3) +
    PowerSeries.mk (fun n => (b n : ℚ)) * X * X * X * X * X * C 1 =
    (1 : ℚ⟦X⟧) * C 3 + (1 : ℚ⟦X⟧) * X * C (-9) + (1 : ℚ⟦X⟧) * X * X * C 1 + (1 : ℚ⟦X⟧) * X * X * X * C 10 + (1 : ℚ⟦X⟧) * X * X * X * X * C (-4) := by
  ext n
  cases n with
  | zero =>
    simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_zero_mul_X, PowerSeries.coeff_mk]
    simp [b0]
  | succ n =>
    cases n with
    | zero =>
      simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_zero_mul_X, PowerSeries.coeff_mk]
      simp [b0, b1]
      norm_num
    | succ n =>
      cases n with
      | zero =>
        simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_zero_mul_X, PowerSeries.coeff_mk]
        simp [b0, b1, b2]
        norm_num
      | succ n =>
        cases n with
        | zero =>
          simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_zero_mul_X, PowerSeries.coeff_mk]
          simp [b0, b1, b2, b3]
          norm_num
        | succ n =>
          cases n with
          | zero =>
            simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_zero_mul_X, PowerSeries.coeff_mk]
            simp [b0, b1, b2, b3, b4]
            norm_num
          | succ n =>
            simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_mk]
            have h := rec n
            have hq : ((b (n + 5) : ℤ) : ℚ) = 5 * ((b (n + 4) : ℤ) : ℚ) - 7 * ((b (n + 3) : ℤ) : ℚ) + ((b (n + 2) : ℤ) : ℚ) + 3 * ((b (n + 1) : ℤ) : ℚ) - ((b n : ℤ) : ℚ) := by
              exact_mod_cast h
            simp [PowerSeries.coeff_one]
            linear_combination hq

end A005522Aux

open A005522Aux OMA.S_oeis_a005522 in
theorem OMA.solution : type_of% @OMA.S_oeis_a005522.main := by
  have e : (fun n => ((a (n + 1) : ℤ) : ℚ)) = (fun n => ((b n : ℤ) : ℚ)) :=
    funext (fun n => by rw [ab])
  rw [e]
  have h := A005522Aux.gfC
  simp only [map_ofNat, map_neg, map_one] at h
  linear_combination h
