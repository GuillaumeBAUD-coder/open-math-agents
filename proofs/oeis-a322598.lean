import OMAStatements.S_oeis_a322598

-- Problem: A322598: a(n) is the number of unlabeled rank-3 graded lattices with 3 coatoms and n atoms.
-- Upstream: formal-conjectures statements/oeis-a322598.lean:0 (declaration OMA.S_oeis_a322598.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Since 9 (6m+t)^2 + 4 (6m+t) + 3 = (9 t^2 + 4 t + 3) + 12 (27 m^2 + (9t+2) m), one has
a(6m+t) = 27 m^2 + (9t+2) m + floor((9 t^2 + 4 t + 3)/12). Writing n = 6m + r with r = 0..5, every
term of the recurrence is then an explicit quadratic in m and the recurrence is a polynomial
identity. The g.f. identity is the same recurrence read coefficientwise, with the first six
coefficients checked directly. -/

namespace A322598Aux

open OMA.S_oeis_a322598 PowerSeries

theorem cl (m t : ℕ) : a (6 * m + t) =
    27 * (m : ℤ) ^ 2 + (9 * (t : ℤ) + 2) * (m : ℤ) + (9 * (t : ℤ) ^ 2 + 4 * (t : ℤ) + 3) / 12 := by
  unfold a
  have e : 9 * ((6 * m + t : ℕ) : ℤ) ^ 2 + 4 * ((6 * m + t : ℕ) : ℤ) + 3 =
      (9 * (t : ℤ) ^ 2 + 4 * (t : ℤ) + 3) + 12 * (27 * (m : ℤ) ^ 2 + (9 * (t : ℤ) + 2) * (m : ℤ)) := by
    push_cast
    ring
  rw [e, Int.add_mul_ediv_left _ _ (by norm_num)]
  ring

theorem rec (n : ℕ) : a (n + 6) = a (n + 5) + a (n + 4) - a (n + 2) - a (n + 1) + a n := by
  obtain ⟨m, hm⟩ : ∃ m, n = 6 * m + 0 ∨ n = 6 * m + 1 ∨ n = 6 * m + 2 ∨ n = 6 * m + 3 ∨
      n = 6 * m + 4 ∨ n = 6 * m + 5 := ⟨n / 6, by omega⟩
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl
  · show a (6 * m + 6) = a (6 * m + 5) + a (6 * m + 4) - a (6 * m + 2) - a (6 * m + 1) + a (6 * m + 0)
    rw [cl m 6, cl m 5, cl m 4, cl m 2, cl m 1, cl m 0]
    norm_num
    ring
  · show a (6 * m + 7) = a (6 * m + 6) + a (6 * m + 5) - a (6 * m + 3) - a (6 * m + 2) + a (6 * m + 1)
    rw [cl m 7, cl m 6, cl m 5, cl m 3, cl m 2, cl m 1]
    norm_num
    ring
  · show a (6 * m + 8) = a (6 * m + 7) + a (6 * m + 6) - a (6 * m + 4) - a (6 * m + 3) + a (6 * m + 2)
    rw [cl m 8, cl m 7, cl m 6, cl m 4, cl m 3, cl m 2]
    norm_num
    ring
  · show a (6 * m + 9) = a (6 * m + 8) + a (6 * m + 7) - a (6 * m + 5) - a (6 * m + 4) + a (6 * m + 3)
    rw [cl m 9, cl m 8, cl m 7, cl m 5, cl m 4, cl m 3]
    norm_num
    ring
  · show a (6 * m + 10) = a (6 * m + 9) + a (6 * m + 8) - a (6 * m + 6) - a (6 * m + 5) + a (6 * m + 4)
    rw [cl m 10, cl m 9, cl m 8, cl m 6, cl m 5, cl m 4]
    norm_num
    ring
  · show a (6 * m + 11) = a (6 * m + 10) + a (6 * m + 9) - a (6 * m + 7) - a (6 * m + 6) + a (6 * m + 5)
    rw [cl m 11, cl m 10, cl m 9, cl m 7, cl m 6, cl m 5]
    norm_num
    ring

theorem a0 : a 0 = 0 := by norm_num [a]
theorem a1 : a 1 = 1 := by norm_num [a]
theorem a2 : a 2 = 3 := by norm_num [a]
theorem a3 : a 3 = 8 := by norm_num [a]
theorem a4 : a 4 = 13 := by norm_num [a]
theorem a5 : a 5 = 20 := by norm_num [a]

theorem gfC : PowerSeries.mk (fun n => (a n : ℚ)) * C 1 +
    PowerSeries.mk (fun n => (a n : ℚ)) * X * C (-1) +
    PowerSeries.mk (fun n => (a n : ℚ)) * X * X * C (-1) +
    PowerSeries.mk (fun n => (a n : ℚ)) * X * X * X * X * C 1 +
    PowerSeries.mk (fun n => (a n : ℚ)) * X * X * X * X * X * C 1 +
    PowerSeries.mk (fun n => (a n : ℚ)) * X * X * X * X * X * X * C (-1) =
    (1 : ℚ⟦X⟧) * X * C 1 + (1 : ℚ⟦X⟧) * X * X * C 2 + (1 : ℚ⟦X⟧) * X * X * X * C 4 + (1 : ℚ⟦X⟧) * X * X * X * X * C 2 := by
  ext n
  cases n with
  | zero =>
    simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_zero_mul_X, PowerSeries.coeff_mk]
    simp [a0]
  | succ n =>
    cases n with
    | zero =>
      simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_zero_mul_X, PowerSeries.coeff_mk]
      simp [a0, a1]
    | succ n =>
      cases n with
      | zero =>
        simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_zero_mul_X, PowerSeries.coeff_mk]
        simp [a0, a1, a2]
        norm_num
      | succ n =>
        cases n with
        | zero =>
          simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_zero_mul_X, PowerSeries.coeff_mk]
          simp [a1, a2, a3]
          norm_num
        | succ n =>
          cases n with
          | zero =>
            simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_zero_mul_X, PowerSeries.coeff_mk]
            simp [a0, a2, a3, a4]
            norm_num
          | succ n =>
            cases n with
            | zero =>
              simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_zero_mul_X, PowerSeries.coeff_mk]
              simp [a0, a1, a3, a4, a5]
              norm_num
            | succ n =>
              simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_mk]
              have h := rec n
              have hq : ((a (n + 6) : ℤ) : ℚ) = ((a (n + 5) : ℤ) : ℚ) + ((a (n + 4) : ℤ) : ℚ) - ((a (n + 2) : ℤ) : ℚ) - ((a (n + 1) : ℤ) : ℚ) + ((a n : ℤ) : ℚ) := by
                exact_mod_cast h
              simp [PowerSeries.coeff_one]
              linear_combination hq

end A322598Aux

theorem OMA.solution : type_of% @OMA.S_oeis_a322598.main := by
  refine ⟨?_, ?_⟩
  · have h := A322598Aux.gfC
    simp only [map_ofNat, map_neg, map_one] at h
    linear_combination h
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
    exact A322598Aux.rec m
