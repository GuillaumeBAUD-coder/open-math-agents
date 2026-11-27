import OMAStatements.S_mse_199784
import Mathlib

/-!
An explicit six-strategy game has a fully mixed equilibrium of value
one thirteenth. Against either equilibrium strategy, all pure strategies
of the other player give that value. At any equilibrium the pure
payoffs are bounded on the appropriate side, and their positive
weighted average is the value, so every bound is an equality. The
resulting linear systems determine both strategies. Finally, row and
column sums and entries in fixed rows and columns distinguish every
strategy under any payoff-preserving pair of permutations.
-/

namespace OMA.MSE199784

open Finset S_mse_199784

/-- The one entries of the sign matrix, specified row by row. -/
def positiveEntry (i j : ℕ) : Bool :=
  match i, j with
  | 0, 1 | 0, 4 | 0, 5 => true
  | 1, 2 | 1, 3 | 1, 4 => true
  | 2, 3 | 2, 4 | 2, 5 => true
  | 3, 0 | 3, 4 => true
  | 4, 0 | 4, 2 | 4, 5 => true
  | 5, 0 | 5, 1 | 5, 2 | 5, 3 => true
  | _, _ => false

/-- The payoff table of the example. -/
def game : Matrix (Fin 6) (Fin 6) ℝ :=
  fun i j => if positiveEntry i.val j.val then 1 else -1

/-- The proposed row strategy. -/
noncomputable def rowStrategy (i : Fin 6) : ℝ :=
  match i.val with
  | 0 => 3/13
  | 1 => 1/13
  | 2 => 2/13
  | 3 => 1/13
  | 4 => 2/13
  | _ => 4/13

/-- The proposed column strategy. -/
noncomputable def colStrategy (j : Fin 6) : ℝ :=
  match j.val with
  | 0 => 3/13
  | 1 => 1/13
  | 2 => 2/13
  | 3 => 1/13
  | 4 => 4/13
  | _ => 2/13

/-- Payoff to a pure row against a mixed column strategy. -/
def rowPay (y : Fin 6 → ℝ) (i : Fin 6) : ℝ := ∑ j, game i j * y j

/-- Payoff against a pure column when the row player mixes. -/
def colPay (x : Fin 6 → ℝ) (j : Fin 6) : ℝ := ∑ i, x i * game i j

/-- Writing each index in the same form makes concrete dot products easy to check. -/
lemma sum_six (f : Fin 6 → ℝ) :
    (∑ i, f i) = f 0 + (f 1 + (f 2 + (f 3 + (f 4 + f 5)))) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  rfl

/-- The row strategy has all coordinates positive. -/
lemma row_pos (i : Fin 6) : 0 < rowStrategy i := by
  fin_cases i <;> norm_num [rowStrategy, Fin.isValue]

/-- The column strategy has all coordinates positive. -/
lemma col_pos (j : Fin 6) : 0 < colStrategy j := by
  fin_cases j <;> norm_num [colStrategy, Fin.isValue]

/-- The row strategy has unit total mass. -/
lemma row_simplex : rowStrategy ∈ stdSimplex ℝ (Fin 6) := by
  refine ⟨fun i => (row_pos i).le, ?_⟩
  norm_num [rowStrategy, sum_six, Fin.isValue]

/-- The column strategy has unit total mass. -/
lemma col_simplex : colStrategy ∈ stdSimplex ℝ (Fin 6) := by
  refine ⟨fun j => (col_pos j).le, ?_⟩
  norm_num [colStrategy, sum_six, Fin.isValue]

/-- The column strategy makes every pure row payoff equal to the value. -/
lemma equal_rows (i : Fin 6) : rowPay colStrategy i = 1/13 := by
  fin_cases i <;> norm_num [rowPay, game, positiveEntry, colStrategy, sum_six, Fin.isValue]

/-- The row strategy makes every pure column payoff equal to the value. -/
lemma equal_cols (j : Fin 6) : colPay rowStrategy j = 1/13 := by
  fin_cases j <;> norm_num [colPay, game, positiveEntry, rowStrategy, sum_six, Fin.isValue]

/-- Group the expected payoff by the row player's pure strategy. -/
lemma payoff_rows (x y : Fin 6 → ℝ) : payoff game x y = ∑ i, x i * rowPay y i := by
  simp only [payoff, rowPay, mul_sum, mul_assoc]

/-- Group the expected payoff by the column player's pure strategy. -/
lemma payoff_cols (x y : Fin 6 → ℝ) : payoff game x y = ∑ j, y j * colPay x j := by
  unfold payoff colPay
  rw [sum_comm]
  simp only [mul_sum]
  exact sum_congr rfl fun j _ => sum_congr rfl fun i _ => by ring

/-- The column strategy yields the value against every mixed row strategy. -/
lemma guarantee_col (x : Fin 6 → ℝ) (hx : x ∈ stdSimplex ℝ (Fin 6)) :
    payoff game x colStrategy = 1/13 := by
  simp only [payoff_rows, equal_rows, ← sum_mul, hx.2, one_mul]

/-- The row strategy yields the value against every mixed column strategy. -/
lemma guarantee_row (y : Fin 6 → ℝ) (hy : y ∈ stdSimplex ℝ (Fin 6)) :
    payoff game rowStrategy y = 1/13 := by
  simp only [payoff_cols, equal_cols, ← sum_mul, hy.2, one_mul]

/-- A positively weighted sum of nonnegative numbers can vanish only termwise. -/
lemma zero_weighted (w s : Fin 6 → ℝ) (hw : ∀ i, 0 < w i) (hs : ∀ i, 0 ≤ s i)
    (hz : ∑ i, w i * s i = 0) (i : Fin 6) : s i = 0 := by
  have h := (sum_eq_zero_iff_of_nonneg (fun j _ => mul_nonneg (hw j).le (hs j))).mp
    hz i (mem_univ i)
  exact (mul_eq_zero.mp h).resolve_left (hw i).ne'

/-- The six equations for pure rows uniquely determine the column strategy. -/
lemma solve_rows (y : Fin 6 → ℝ) (h : ∀ i, rowPay y i = 1/13) : y = colStrategy := by
  have h₀ := h 0
  have h₁ := h 1
  have h₂ := h 2
  have h₃ := h 3
  have h₄ := h 4
  have h₅ := h 5
  norm_num [rowPay, game, positiveEntry, sum_six, Fin.isValue] at h₀ h₁ h₂ h₃ h₄ h₅
  funext j
  fin_cases j
  · change y 0 = 3/13
    linarith
  · change y 1 = 1/13
    linarith
  · change y 2 = 2/13
    linarith
  · change y 3 = 1/13
    linarith
  · change y 4 = 4/13
    linarith
  · change y 5 = 2/13
    linarith

/-- The six equations for pure columns uniquely determine the row strategy. -/
lemma solve_cols (x : Fin 6 → ℝ) (h : ∀ j, colPay x j = 1/13) : x = rowStrategy := by
  have h₀ := h 0
  have h₁ := h 1
  have h₂ := h 2
  have h₃ := h 3
  have h₄ := h 4
  have h₅ := h 5
  norm_num [colPay, game, positiveEntry, sum_six, Fin.isValue] at h₀ h₁ h₂ h₃ h₄ h₅
  funext i
  fin_cases i
  · change x 0 = 3/13
    linarith
  · change x 1 = 1/13
    linarith
  · change x 2 = 2/13
    linarith
  · change x 3 = 1/13
    linarith
  · change x 4 = 2/13
    linarith
  · change x 5 = 4/13
    linarith

/-- The two guarantees give an equilibrium. -/
lemma equilibrium : IsNashEquilibrium game rowStrategy colStrategy := by
  refine ⟨row_simplex, col_simplex, ?_, ?_⟩
  · intro x hx
    rw [guarantee_col x hx, guarantee_col rowStrategy row_simplex]
  · intro y hy
    rw [guarantee_row colStrategy col_simplex, guarantee_row y hy]

/-- Pure deviations bound each coordinate payoff, and positive averaging makes the bounds tight. -/
lemma equilibrium_unique (x y : Fin 6 → ℝ) (h : IsNashEquilibrium game x y) :
    x = rowStrategy ∧ y = colStrategy := by
  obtain ⟨hx, hy, hrow, hcol⟩ := h
  have hv : payoff game x y = 1/13 := by
    have hlo := hrow rowStrategy row_simplex
    have hhi := hcol colStrategy col_simplex
    rw [guarantee_row y hy] at hlo
    rw [guarantee_col x hx] at hhi
    exact le_antisymm hhi hlo
  have hle (i : Fin 6) : rowPay y i ≤ 1/13 := by
    have h := hrow (Pi.single i 1) (single_mem_stdSimplex ℝ i)
    simpa [payoff_rows, hv, Pi.single_apply] using h
  have hge (j : Fin 6) : 1/13 ≤ colPay x j := by
    have h := hcol (Pi.single j 1) (single_mem_stdSimplex ℝ j)
    simpa [payoff_cols, hv, Pi.single_apply] using h
  have hzrow : ∑ i, rowStrategy i * (1/13 - rowPay y i) = 0 := by
    simp only [mul_sub, sum_sub_distrib, ← sum_mul,
      row_simplex.2, one_mul, ← payoff_rows, guarantee_row y hy, sub_self]
  have hzcol : ∑ j, colStrategy j * (colPay x j - 1/13) = 0 := by
    simp only [mul_sub, sum_sub_distrib, ← sum_mul, col_simplex.2, one_mul,
      ← payoff_cols, guarantee_col x hx, sub_self]
  refine ⟨solve_cols x (fun j => ?_), solve_rows y (fun i => ?_)⟩
  · exact sub_eq_zero.mp (zero_weighted colStrategy _ col_pos
      (fun j => sub_nonneg.mpr (hge j)) hzcol j)
  · exact (sub_eq_zero.mp (zero_weighted rowStrategy _ row_pos
      (fun i => sub_nonneg.mpr (hle i)) hzrow i)).symm

set_option maxHeartbeats 1000000 in
/-- The row and column sums first fix the strategies of degree two and four. -/
lemma extreme_fixed (σ τ : Equiv.Perm (Fin 6))
    (h : ∀ i j, game (σ i) (τ j) = game i j) :
    σ 3 = 3 ∧ σ 5 = 5 ∧ τ 1 = 1 ∧ τ 4 = 4 := by
  have hr (i : Fin 6) : ∑ j, game (σ i) j = ∑ j, game i j := by
    calc
      _ = ∑ j, game (σ i) (τ j) := (Equiv.sum_comp τ (fun j => game (σ i) j)).symm
      _ = _ := sum_congr rfl (fun j _ => h i j)
  have hc (j : Fin 6) : ∑ i, game i (τ j) = ∑ i, game i j := by
    calc
      _ = ∑ i, game (σ i) (τ j) := (Equiv.sum_comp σ (fun i => game i (τ j))).symm
      _ = _ := sum_congr rfl (fun i _ => h i j)
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h₃ := hr 3
    generalize σ 3 = i at h₃ ⊢
    fin_cases i
    all_goals first
      | rfl
      | revert h₃
        norm_num [game, positiveEntry, sum_six, Fin.isValue]
  · have h₅ := hr 5
    generalize σ 5 = i at h₅ ⊢
    fin_cases i
    all_goals first
      | rfl
      | revert h₅
        norm_num [game, positiveEntry, sum_six, Fin.isValue]
  · have h₁ := hc 1
    generalize τ 1 = j at h₁ ⊢
    fin_cases j
    all_goals first
      | rfl
      | revert h₁
        norm_num [game, positiveEntry, sum_six, Fin.isValue]
  · have h₄ := hc 4
    generalize τ 4 = j at h₄ ⊢
    fin_cases j
    all_goals first
      | rfl
      | revert h₄
        norm_num [game, positiveEntry, sum_six, Fin.isValue]

set_option maxHeartbeats 3000000 in
/-- Entries in fixed rows and columns, together with the sums, pin all remaining strategies. -/
lemma asymmetric : IsTotallyAsymmetric game := by
  intro σ τ h
  obtain ⟨hr₃, hr₅, hc₁, hc₄⟩ := extreme_fixed σ τ h
  have hr (i : Fin 6) : ∑ j, game (σ i) j = ∑ j, game i j := by
    calc
      _ = ∑ j, game (σ i) (τ j) := (Equiv.sum_comp τ (fun j => game (σ i) j)).symm
      _ = _ := sum_congr rfl (fun j _ => h i j)
  have hc (j : Fin 6) : ∑ i, game i (τ j) = ∑ i, game i j := by
    calc
      _ = ∑ i, game (σ i) (τ j) := (Equiv.sum_comp σ (fun i => game i (τ j))).symm
      _ = _ := sum_congr rfl (fun i _ => h i j)
  have hc₅ : τ 5 = 5 := by
    have hd := hc 5
    have h₃ := h 3 5
    have h₅ := h 5 5
    rw [hr₃] at h₃
    rw [hr₅] at h₅
    generalize τ 5 = j at hd h₃ h₅ ⊢
    fin_cases j
    all_goals first
      | rfl
      | revert hd h₃ h₅
        norm_num [game, positiveEntry, sum_six, Fin.isValue]
  have hrall (i : Fin 6) : σ i = i := by
    have hd := hr i
    have h₁ := h i 1
    have h₄ := h i 4
    have h₅ := h i 5
    rw [hc₁] at h₁
    rw [hc₄] at h₄
    rw [hc₅] at h₅
    generalize σ i = k at hd h₁ h₄ h₅ ⊢
    fin_cases i <;> fin_cases k
    all_goals first
      | rfl
      | revert hd h₁ h₄ h₅
        norm_num [game, positiveEntry, sum_six, Fin.isValue]
  have hcall (j : Fin 6) : τ j = j := by
    have hd := hc j
    have h₃ := h 3 j
    have h₄ := h 4 j
    have h₅ := h 5 j
    rw [hrall] at h₃ h₄ h₅
    generalize τ j = k at hd h₃ h₄ h₅ ⊢
    fin_cases j <;> fin_cases k
    all_goals first
      | rfl
      | revert hd h₃ h₄ h₅
        norm_num [game, positiveEntry, sum_six, Fin.isValue]
  exact ⟨Equiv.ext hrall, Equiv.ext hcall⟩

end OMA.MSE199784

open OMA.MSE199784 in
theorem OMA.solution : type_of% @OMA.S_mse_199784.main := by
  refine ⟨6, 6, game, by decide, by decide, ?_, asymmetric,
    rowStrategy, colStrategy, equilibrium, row_pos, col_pos, equilibrium_unique⟩
  intro i j
  by_cases h : positiveEntry i.val j.val
  · exact Or.inl (if_pos h)
  · exact Or.inr (if_neg h)
