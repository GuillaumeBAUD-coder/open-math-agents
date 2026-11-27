import OMAStatements.S_oeis_a341249

/-!
Counterexample at n = 2: floor(s * 2) = 2, a 2 = floor((2 + sqrt 2) * 2) = 6,
and r * s * 2 - a 2 = 4 * sqrt 2 - 2 > 2.
-/

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a341249.main) := by
  intro h
  have h2 : OMA.S_oeis_a341249.r * OMA.S_oeis_a341249.s * ((2 : ℕ) : ℝ) -
      (OMA.S_oeis_a341249.a 2 : ℝ) < 2 := (h 2 (by norm_num)).2
  have hsq_gt : (1 : ℝ) < Real.sqrt 2 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  have hsq_lt : Real.sqrt 2 < 3 / 2 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  have hfl1 : ⌊OMA.S_oeis_a341249.s * ((2 : ℕ) : ℝ)⌋ = 2 := by
    rw [Int.floor_eq_iff]
    unfold OMA.S_oeis_a341249.s
    push_cast
    constructor <;> linarith
  have ha2 : OMA.S_oeis_a341249.a 2 = 6 := by
    unfold OMA.S_oeis_a341249.a
    rw [hfl1, Int.floor_eq_iff]
    unfold OMA.S_oeis_a341249.r
    push_cast
    constructor <;> linarith
  have hrs : OMA.S_oeis_a341249.r * OMA.S_oeis_a341249.s * ((2 : ℕ) : ℝ) =
      4 + 4 * Real.sqrt 2 := by
    unfold OMA.S_oeis_a341249.r OMA.S_oeis_a341249.s
    have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    push_cast
    linear_combination 2 * hsq
  rw [ha2, hrs] at h2
  push_cast at h2
  linarith
