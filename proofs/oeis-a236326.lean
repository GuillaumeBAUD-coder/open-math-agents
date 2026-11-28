import OMAStatements.S_oeis_a236326

/-!
Proof of the claims of A236326 (irregular spiral with center points 1, 2, 3, 4, 5, pattern 1).

* Start points: `pos (k + 1) = 2 * center k - pos k` with `pos 0 = 2`. By induction on k,
  `pos k` depends only on `k % 10`, with values 2, 0, 4, 2, 6, 4, -2, 6, 0, 8.
* Hence the radii repeat as 1, 2, 1, 2, 1, 3, 4, 3, 4, 3, and rotation n + 1 adds the radii of half
  circles 2n and 2n + 1, whose residues mod 10 are `2 * (n % 5)` and `2 * (n % 5) + 1`:
  `a (n + 1) = a n + D (n % 5)` with D = 3, 3, 4, 7, 7.
* Barker's recurrence: `a (m + 6) - a (m + 5) = D (m % 5) = a (m + 1) - a m`.
* Barker's g.f.: the denominator is `1 - X - X^5 + X^6`, so for k ≥ 6 the coefficient of `X^k` is
  `a k - a (k - 1) - a (k - 5) + a (k - 6) = 0`; the first six coefficients follow from
  `a 0, ..., a 5 = 0, 3, 6, 10, 17, 24`.
* Fried's formula: both sides vanish at 0 and have the same increments.
* Ngaokrajang's conjecture: for centers with period 5 the start points have period 10, since
  `startPt (k + 2) = startPt k + 2 * (c (k + 1) - c k)` and the alternating sum of ten consecutive
  centers vanishes (5 is odd). So p = 10 works for every order of the centers and every start.
-/

namespace OMA.Helpers

open OMA.S_oeis_a236326

/-- The start points of the A236326 curve over one period of ten half circles. -/
def posTableA236326 : ℕ → ℤ
  | 0 => 2
  | 1 => 0
  | 2 => 4
  | 3 => 2
  | 4 => 6
  | 5 => 4
  | 6 => -2
  | 7 => 6
  | 8 => 0
  | _ => 8

/-- The radii of the A236326 curve over one period of ten half circles. -/
def radTableA236326 : ℕ → ℤ
  | 0 => 1
  | 1 => 2
  | 2 => 1
  | 3 => 2
  | 4 => 1
  | 5 => 3
  | 6 => 4
  | 7 => 3
  | 8 => 4
  | _ => 3

/-- The length (divided by Pi) added by rotation n + 1, as a function of n % 5. -/
def incA236326 : ℕ → ℤ
  | 0 => 3
  | 1 => 3
  | 2 => 4
  | _ => 7

theorem centerModA236326 (k : ℕ) : center k = ((k % 10 % 5 : ℕ) : ℤ) + 1 := by
  unfold center
  rw [show k % 10 % 5 = k % 5 by omega]

theorem posEqA236326 (k : ℕ) : pos k = posTableA236326 (k % 10) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hstep : pos (k + 1) = 2 * center k - pos k := rfl
    rw [hstep, ih, centerModA236326, show (k + 1) % 10 = (k % 10 + 1) % 10 by omega]
    have hlt : k % 10 < 10 := Nat.mod_lt _ (by norm_num)
    generalize k % 10 = r at hlt ⊢
    interval_cases r <;> decide

theorem radiusEqA236326 (k : ℕ) : radius k = radTableA236326 (k % 10) := by
  unfold radius
  rw [posEqA236326, centerModA236326]
  have hlt : k % 10 < 10 := Nat.mod_lt _ (by norm_num)
  generalize k % 10 = r at hlt ⊢
  interval_cases r <;> decide

theorem stepA236326 (n : ℕ) : a (n + 1) = a n + incA236326 (n % 5) := by
  unfold a
  rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
    radiusEqA236326, radiusEqA236326, show 2 * n % 10 = 2 * (n % 5) by omega,
    show (2 * n + 1) % 10 = 2 * (n % 5) + 1 by omega, add_assoc]
  congr 1
  have hlt : n % 5 < 5 := Nat.mod_lt _ (by norm_num)
  generalize n % 5 = r at hlt ⊢
  interval_cases r <;> decide

theorem aZeroA236326 : a 0 = 0 := by
  simp [a]

theorem valsA236326 : a 1 = 3 ∧ a 2 = 6 ∧ a 3 = 10 ∧ a 4 = 17 ∧ a 5 = 24 := by
  have h1 : a 1 = 3 := by rw [stepA236326 0, aZeroA236326]; decide
  have h2 : a 2 = 6 := by rw [stepA236326 1, h1]; decide
  have h3 : a 3 = 10 := by rw [stepA236326 2, h2]; decide
  have h4 : a 4 = 17 := by rw [stepA236326 3, h3]; decide
  have h5 : a 5 = 24 := by rw [stepA236326 4, h4]; decide
  exact ⟨h1, h2, h3, h4, h5⟩

/-- The increment of rotation m + 6 equals that of rotation m + 1 (also for m = 0). -/
theorem diffA236326 (m : ℕ) : a (m + 6) = a (m + 5) + a (m + 1) - a m := by
  rw [stepA236326 (m + 5), stepA236326 m, show (m + 5) % 5 = m % 5 by omega]
  ring

/-- Barker's recurrence, for n ≥ 7. -/
theorem recA236326 (n : ℕ) (hn : 7 ≤ n) : a n = a (n - 1) + a (n - 5) - a (n - 6) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
  rw [show m + 6 - 1 = m + 5 by omega, show m + 6 - 5 = m + 1 by omega,
    show m + 6 - 6 = m by omega]
  exact diffA236326 m

/-- Fried's formula, for every n (both sides vanish at 0). -/
theorem friedA236326 (n : ℕ) :
    a n = 3 * (n : ℤ) + 4 * ((n / 5 : ℕ) : ℤ) + 4 * (((n + 1) / 5 : ℕ) : ℤ) +
      (((n + 2) / 5 : ℕ) : ℤ) := by
  induction n with
  | zero => simp [aZeroA236326]
  | succ n ih =>
    rw [stepA236326, ih]
    obtain h | h | h | h | h : n % 5 = 0 ∨ n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by
      omega
    all_goals
      rw [h]
      simp only [incA236326]
      push_cast
      omega

open PowerSeries in
/-- Barker's generating function. -/
theorem genFunA236326 :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
        ((X - 1) ^ 2 * (X ^ 4 + X ^ 3 + X ^ 2 + X + 1)) =
      X * (7 * X ^ 4 + 7 * X ^ 3 + 4 * X ^ 2 + 3 * X + 3) := by
  have hF : (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = fun n => (a n : ℚ) := by
    funext n
    split_ifs with h
    · rw [h, aZeroA236326]
      simp
    · rfl
  rw [hF]
  set F : ℕ → ℚ := fun n => (a n : ℚ) with hFdef
  have key : PowerSeries.mk F * ((X - 1) ^ 2 * (X ^ 4 + X ^ 3 + X ^ 2 + X + 1)) =
      C 1 * (PowerSeries.mk F * X ^ 0) - C 1 * (PowerSeries.mk F * X ^ 1) -
        C 1 * (PowerSeries.mk F * X ^ 5) + C 1 * (PowerSeries.mk F * X ^ 6) := by
    simp only [map_one]
    ring
  have hrhs : (X : ℚ⟦X⟧) * (7 * X ^ 4 + 7 * X ^ 3 + 4 * X ^ 2 + 3 * X + 3) =
      C 3 * X ^ 1 + C 3 * X ^ 2 + C 4 * X ^ 3 + C 7 * X ^ 4 + C 7 * X ^ 5 := by
    simp only [map_ofNat]
    ring
  rw [key, hrhs]
  ext k
  simp only [map_sub, map_add, coeff_C_mul_X_pow]
  simp only [coeff_C_mul, coeff_mul_X_pow', coeff_mk]
  obtain ⟨h1, h2, h3, h4, h5⟩ := valsA236326
  by_cases hk : k < 6
  · interval_cases k <;> norm_num [hFdef, aZeroA236326, h1, h2, h3, h4, h5]
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 6 := ⟨k - 6, by omega⟩
    simp only [show 0 ≤ j + 6 by omega, show 1 ≤ j + 6 by omega, show 5 ≤ j + 6 by omega,
      show 6 ≤ j + 6 by omega, show j + 6 - 0 = j + 6 by omega, show j + 6 - 1 = j + 5 by omega,
      show j + 6 - 5 = j + 1 by omega, show j + 6 - 6 = j by omega, show ¬ (j + 6 = 1) by omega,
      show ¬ (j + 6 = 2) by omega, show ¬ (j + 6 = 3) by omega, show ¬ (j + 6 = 4) by omega,
      show ¬ (j + 6 = 5) by omega, if_true, if_false, hFdef]
    have hq : ((a (j + 6) : ℤ) : ℚ) = ((a (j + 5) + a (j + 1) - a j : ℤ) : ℚ) := by
      rw [diffA236326 j]
    push_cast at hq
    rw [hq]
    ring

/-- Two half circles move the start point by twice the difference of their centers. -/
theorem startPtTwoA236326 (c : ℕ → ℤ) (x₀ : ℤ) (j : ℕ) :
    startPt c x₀ (j + 2) = 2 * c (j + 1) - 2 * c j + startPt c x₀ j := by
  show 2 * c (j + 1) - (2 * c j - startPt c x₀ j) = _
  ring

/-- If the centers repeat with period 5, the start points repeat with period 10. -/
theorem loopA236326 (c : ℕ → ℤ) (hc : ∀ j, c (j + 5) = c j) (x₀ : ℤ) (k : ℕ) :
    startPt c x₀ (k + 10) = startPt c x₀ k := by
  have e1 : startPt c x₀ (k + 10) = 2 * c (k + 9) - 2 * c (k + 8) + startPt c x₀ (k + 8) :=
    startPtTwoA236326 c x₀ (k + 8)
  have e2 : startPt c x₀ (k + 8) = 2 * c (k + 7) - 2 * c (k + 6) + startPt c x₀ (k + 6) :=
    startPtTwoA236326 c x₀ (k + 6)
  have e3 : startPt c x₀ (k + 6) = 2 * c (k + 5) - 2 * c (k + 4) + startPt c x₀ (k + 4) :=
    startPtTwoA236326 c x₀ (k + 4)
  have e4 : startPt c x₀ (k + 4) = 2 * c (k + 3) - 2 * c (k + 2) + startPt c x₀ (k + 2) :=
    startPtTwoA236326 c x₀ (k + 2)
  have e5 : startPt c x₀ (k + 2) = 2 * c (k + 1) - 2 * c k + startPt c x₀ k :=
    startPtTwoA236326 c x₀ k
  have p9 : c (k + 9) = c (k + 4) := hc (k + 4)
  have p8 : c (k + 8) = c (k + 3) := hc (k + 3)
  have p7 : c (k + 7) = c (k + 2) := hc (k + 2)
  have p6 : c (k + 6) = c (k + 1) := hc (k + 1)
  have p5 : c (k + 5) = c k := hc k
  linarith

/-- The centers of any order of the five points repeat with period 5. -/
theorem permCenterPeriodA236326 (σ : Equiv.Perm (Fin 5)) (j : ℕ) :
    permCenter σ (j + 5) = permCenter σ j := by
  unfold permCenter
  have h : (⟨(j + 5) % 5, Nat.mod_lt _ (by norm_num)⟩ : Fin 5) =
      ⟨j % 5, Nat.mod_lt _ (by norm_num)⟩ := Fin.ext (by simp)
  rw [h]

theorem permCenterTenA236326 (σ : Equiv.Perm (Fin 5)) (k : ℕ) :
    permCenter σ (k + 10) = permCenter σ k := by
  rw [show k + 10 = k + 5 + 5 by omega, permCenterPeriodA236326, permCenterPeriodA236326]

/-- Ngaokrajang's conjecture: every order of the centers and every start point give a closed
curve, which repeats after ten half circles. -/
theorem loopsA236326 (σ : Equiv.Perm (Fin 5)) (x₀ : ℤ) : ∃ p : ℕ, 0 < p ∧ ∀ k : ℕ,
    startPt (permCenter σ) x₀ (k + p) = startPt (permCenter σ) x₀ k ∧
      permCenter σ (k + p) = permCenter σ k ∧ (k + p) % 2 = k % 2 :=
  ⟨10, by norm_num, fun k => ⟨loopA236326 _ (permCenterPeriodA236326 σ) x₀ k,
    permCenterTenA236326 σ k, by omega⟩⟩

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a236326.main :=
  ⟨OMA.Helpers.loopsA236326, OMA.Helpers.recA236326, OMA.Helpers.genFunA236326,
    fun n _ => OMA.Helpers.friedA236326 n⟩
