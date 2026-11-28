import OMAStatements.S_mo_476014

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_476014.main) := by
  intro h
  let f : ℝ → ℝ := fun x => 1 + x + Real.sqrt x
  let g : ℝ → ℝ := fun x => 1 + x
  have hconv : ConvexOn ℝ (Set.Ioi 0) f := by
    apply h (1 / 2) f g 1 2 (by norm_num) (by norm_num)
    · intro x hx
      dsimp [f]
      linarith [Real.sqrt_nonneg x]
    · intro x hx y hy u hu0 hu1
      dsimp [f]
      rw [← Real.sqrt_eq_rpow u, ← Real.sqrt_eq_rpow (1 - u)]
      have hsu : u ≤ Real.sqrt u := by
        have hsq : Real.sqrt u ^ 2 = u := Real.sq_sqrt (le_of_lt hu0)
        have hnn : 0 ≤ Real.sqrt u := Real.sqrt_nonneg u
        nlinarith
      have hs1u : 1 - u ≤ Real.sqrt (1 - u) := by
        have hsq : Real.sqrt (1 - u) ^ 2 = 1 - u := Real.sq_sqrt (by linarith)
        have hnn : 0 ≤ Real.sqrt (1 - u) := Real.sqrt_nonneg (1 - u)
        nlinarith
      have hsqrt_add :
          Real.sqrt (u * x + (1 - u) * y) ≤
            Real.sqrt u * Real.sqrt x + Real.sqrt (1 - u) * Real.sqrt y := by
        have hxy : 0 ≤ u * x + (1 - u) * y := by nlinarith
        have hlhs : Real.sqrt (u * x + (1 - u) * y) ^ 2 = u * x + (1 - u) * y :=
          Real.sq_sqrt hxy
        have h1 : Real.sqrt u ^ 2 = u := Real.sq_sqrt (le_of_lt hu0)
        have h2 : Real.sqrt x ^ 2 = x := Real.sq_sqrt (le_of_lt hx)
        have h3 : Real.sqrt (1 - u) ^ 2 = 1 - u := Real.sq_sqrt (by linarith)
        have h4 : Real.sqrt y ^ 2 = y := Real.sq_sqrt (le_of_lt hy)
        have hn1 : 0 ≤ Real.sqrt u := Real.sqrt_nonneg _
        have hn2 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg _
        have hn3 : 0 ≤ Real.sqrt (1 - u) := Real.sqrt_nonneg _
        have hn4 : 0 ≤ Real.sqrt y := Real.sqrt_nonneg _
        have hB : 0 ≤ Real.sqrt u * Real.sqrt x + Real.sqrt (1 - u) * Real.sqrt y :=
          add_nonneg (mul_nonneg hn1 hn2) (mul_nonneg hn3 hn4)
        have hprod : 0 ≤ (Real.sqrt u * Real.sqrt x) * (Real.sqrt (1 - u) * Real.sqrt y) :=
          mul_nonneg (mul_nonneg hn1 hn2) (mul_nonneg hn3 hn4)
        have hrhs :
            (Real.sqrt u * Real.sqrt x + Real.sqrt (1 - u) * Real.sqrt y) ^ 2 =
              u * x + (1 - u) * y +
                2 * ((Real.sqrt u * Real.sqrt x) * (Real.sqrt (1 - u) * Real.sqrt y)) := by
          calc
            (Real.sqrt u * Real.sqrt x + Real.sqrt (1 - u) * Real.sqrt y) ^ 2
                = Real.sqrt u ^ 2 * Real.sqrt x ^ 2 + Real.sqrt (1 - u) ^ 2 * Real.sqrt y ^ 2 +
                    2 * ((Real.sqrt u * Real.sqrt x) * (Real.sqrt (1 - u) * Real.sqrt y)) := by
                  ring
            _ = u * x + (1 - u) * y +
                  2 * ((Real.sqrt u * Real.sqrt x) * (Real.sqrt (1 - u) * Real.sqrt y)) := by
                  rw [h1, h2, h3, h4]
        by_contra hlt
        push_neg at hlt
        have hpos1 :
            0 < Real.sqrt (u * x + (1 - u) * y) +
                  (Real.sqrt u * Real.sqrt x + Real.sqrt (1 - u) * Real.sqrt y) := by
          linarith
        have hpos2 :
            0 < Real.sqrt (u * x + (1 - u) * y) -
                  (Real.sqrt u * Real.sqrt x + Real.sqrt (1 - u) * Real.sqrt y) := by
          linarith
        have hmul :
            0 < (Real.sqrt (u * x + (1 - u) * y) +
                  (Real.sqrt u * Real.sqrt x + Real.sqrt (1 - u) * Real.sqrt y)) *
                (Real.sqrt (u * x + (1 - u) * y) -
                  (Real.sqrt u * Real.sqrt x + Real.sqrt (1 - u) * Real.sqrt y)) :=
          mul_pos hpos1 hpos2
        have hdiff :
            (Real.sqrt (u * x + (1 - u) * y) +
              (Real.sqrt u * Real.sqrt x + Real.sqrt (1 - u) * Real.sqrt y)) *
            (Real.sqrt (u * x + (1 - u) * y) -
              (Real.sqrt u * Real.sqrt x + Real.sqrt (1 - u) * Real.sqrt y)) =
            Real.sqrt (u * x + (1 - u) * y) ^ 2 -
              (Real.sqrt u * Real.sqrt x + Real.sqrt (1 - u) * Real.sqrt y) ^ 2 := by
          ring
        linarith
      nlinarith
    · intro x hx
      dsimp [g]
      linarith
    · refine ⟨convex_Ioi 0, ?_⟩
      intro x hx y hy a b ha hb hab
      change 1 + (a * x + b * y) ≤ a * (1 + x) + b * (1 + y)
      nlinarith
    · norm_num
    · norm_num
    · intro x hx
      dsimp [f, g]
      have hnn : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
      have hsq : Real.sqrt x ^ 2 = x := Real.sq_sqrt (le_of_lt hx)
      constructor <;> nlinarith
  have hineq := hconv.2 (show (1 : ℝ) ∈ Set.Ioi 0 by norm_num)
    (show (9 : ℝ) ∈ Set.Ioi 0 by norm_num)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (by norm_num)
  change 1 + ((1 / 2 : ℝ) * 1 + (1 / 2 : ℝ) * 9) +
      Real.sqrt ((1 / 2 : ℝ) * 1 + (1 / 2 : ℝ) * 9) ≤
    (1 / 2 : ℝ) * (1 + 1 + Real.sqrt 1) + (1 / 2 : ℝ) * (1 + 9 + Real.sqrt 9) at hineq
  have hmid : (1 / 2 : ℝ) * 1 + (1 / 2 : ℝ) * 9 = 5 := by norm_num
  rw [hmid] at hineq
  have hs1 : Real.sqrt 1 = 1 := Real.sqrt_one
  have hs9 : Real.sqrt 9 = 3 := by
    have hsq : Real.sqrt 9 ^ 2 = 9 := Real.sq_sqrt (by norm_num)
    have hnn : 0 ≤ Real.sqrt 9 := Real.sqrt_nonneg 9
    nlinarith
  have hs5 : 2 < Real.sqrt 5 := by
    have hsq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
    have hnn : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
    nlinarith
  linarith
