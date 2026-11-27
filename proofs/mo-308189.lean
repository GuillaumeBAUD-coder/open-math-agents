import OMAStatements.S_mo_308189

/-!
# MathOverflow 308189, "An inequality with rotation", is false

The question (Venkat, 2018) asks: if `P(z) = ∑_{m ≤ n} a_m z^m` has degree `n ≥ 1` and no zero in
`|z| < 1`, is it true that for every complex `α` with `|α| = 1` and every `|z| = 1`

  `|α z P'(z) + z P'(z) - (n - (|a₀| - 1)/(|a₀| + 1)) P(z)| ≤ (n - (|a₀| - 1)/(|a₀| + 1)) max_{|z|=1} |P(z)|`?

It is not. Take `P(z) = 4z + 5`: degree `1`, only zero `-5/4` of modulus `5/4 > 1`, so the
hypothesis holds; `|a₀| = 5` gives the factor `1 - 4/6 = 1/3`, and `max_{|z|=1} |P| = 9`, attained
at `z = 1`. With `α = z = 1` the left side is `|2·4 - (1/3)·9| = 5`, while the right side is
`(1/3)·9 = 3`.

Two comments on the question already record the failure: Philipp Lampe observes that the right
side is negative for `P = 2`, and Willie Wong notes that for `P = λ(2 + z)` with real `λ` the
inequality fails as `λ → ∞`. Since the same computation refutes the largest possible reading of
the question, this is the mathematics and not just a slip of the translation: only the degree-one
case is claimed here, and the question's own comment suggests `n ≥ 2` as a repaired hypothesis.
-/

open Polynomial

/-- The counterexample polynomial `4X + 5`. -/
noncomputable def Pc : ℂ[X] := C 5 + C 4 * X

open OMA.S_mo_308189 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_308189.main) := by
  intro h
  have hdeg : Pc.natDegree = 1 := by
    rw [Pc]
    compute_degree!
  -- `Pc` has no zero in the open unit disc: its only zero is `-5/4`
  have hzero : ∀ w : ℂ, ‖w‖ < 1 → Pc.eval w ≠ 0 := by
    intro w hw hc
    rw [Pc] at hc
    simp only [eval_add, eval_mul, eval_C, eval_X] at hc
    have h4 : (4 : ℂ) * w = -5 := by linear_combination hc
    have hnorm : (4 : ℝ) * ‖w‖ = 5 := by
      calc (4 : ℝ) * ‖w‖ = ‖(4 : ℂ) * w‖ := by rw [norm_mul]; simp
        _ = ‖(-5 : ℂ)‖ := by rw [h4]
        _ = 5 := by norm_num
    have : ‖w‖ = 5 / 4 := by linarith
    linarith
  obtain ⟨M, hM, hineq⟩ := h Pc hdeg.ge hzero
  obtain ⟨hMmem, hMub⟩ := hM
  -- `9 = |Pc 1|` is attained on the unit circle and bounds `|Pc|` there, so `M = 9`
  have hM9 : (9 : ℝ) ∈ circleNorms Pc := by
    refine ⟨(1 : ℂ), ?_, ?_⟩
    · norm_num
    · rw [Pc]
      simp
      norm_num
  have hle : ∀ t ∈ circleNorms Pc, t ≤ 9 := by
    intro t ht
    obtain ⟨w, hw, hval⟩ := ht
    rw [← hval]
    rw [Pc]
    simp only [eval_add, eval_mul, eval_C, eval_X]
    calc ‖(5 : ℂ) + 4 * w‖ ≤ ‖(5 : ℂ)‖ + ‖(4 : ℂ) * w‖ := norm_add_le _ _
      _ = 5 + 4 * ‖w‖ := by rw [norm_mul]; norm_num
      _ = 5 + 4 := by rw [hw]; norm_num
      _ = 9 := by norm_num
  have hMval : M = 9 := le_antisymm (hle M hMmem) (hMub hM9)
  have hrot : rotationBound Pc = 1 / 3 := by
    rw [Pc, rotationBound]
    simp only [show (C 5 + C 4 * X : ℂ[X]).natDegree = 1 from by compute_degree!,
      show (C 5 + C 4 * X : ℂ[X]).coeff 0 = 5 from by simp]
    norm_num
  have hkey := hineq 1 1 (by norm_num) (by norm_num)
  have hderiv : Pc.derivative.eval 1 = 4 := by
    rw [Pc]
    simp
  have heval : Pc.eval 1 = 9 := by
    rw [Pc]
    simp
    norm_num
  rw [hrot, hMval, hderiv, heval] at hkey
  have hnum : (1 : ℂ) * 1 * 4 + 1 * 4 - ((1 / 3 : ℝ) : ℂ) * 9 = (5 : ℂ) := by
    norm_num
  rw [hnum] at hkey
  norm_num at hkey
