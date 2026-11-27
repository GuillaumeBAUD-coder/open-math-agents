import OMAStatements.S_oeis_a223299
import Mathlib

/-!
# Proof of the A223299 formulas

The 36 oriented row states have 6, 9 or 12 successors. For each state the
number of two-row extensions is eleven times its number of one-row extensions
minus twelve. Summing the identity propagates it to every grid height.
Credit: @thomasfredrickson with Codex. Source: https://oeis.org/A223299
-/

namespace A223299Proof
open OMA.S_oeis_a223299

private def total {α : Type} (xs : List α) (f : α → ℕ) := (xs.map f).sum

private theorem length_flat {α β : Type} (xs : List α) (f : α → List β) :
    (xs.flatMap f).length = total xs (fun r => (f r).length) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [total, ih]

private def ways : ℕ → Row → ℕ
  | 0, _ => 1
  | n+1, r => total (after r) (ways n)

private theorem count_grids (n : ℕ) (r : Row) : (grids n r).length = ways n r := by
  induction n generalizing r with
  | zero => rfl
  | succ n ih => simp only [grids, ways, length_flat, List.length_map, ih]

private theorem count_all (n : ℕ) : a (n+1) = total rows (ways n) := by
  simp only [a, length_flat, count_grids]

private theorem sum_identity {α : Type} (xs : List α) (u v w : α → ℕ)
    (h : ∀ x ∈ xs, u x + 12 * v x = 11 * w x) :
    total xs u + 12 * total xs v = 11 * total xs w := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hx := h x List.mem_cons_self
    have hs := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    simp only [total, List.map_cons, List.sum_cons] at hs ⊢
    omega

-- Exhaustive identity for all 36 first rows. All larger heights follow by summation.
set_option maxRecDepth 10000 in
private theorem two_steps : ∀ r ∈ rows, ways 2 r + 12 * ways 0 r = 11 * ways 1 r := by
  decide +kernel

private theorem row_recurrence (n : ℕ) : ∀ r ∈ rows,
    ways (n+2) r + 12 * ways n r = 11 * ways (n+1) r := by
  induction n with
  | zero => exact two_steps
  | succ n ih =>
    intro r _
    exact sum_identity (after r) (ways (n+2)) (ways n) (ways (n+1))
      (fun s hs => ih s (List.mem_filter.mp hs).1)

theorem recurrence (n : ℕ) : a (n+3) + 12 * a (n+1) = 11 * a (n+2) := by
  simp only [count_all]
  exact sum_identity rows _ _ _ (row_recurrence n)

theorem initial : a 1 = 36 ∧ a 2 = 324 := by
  simp only [count_all]
  decide +kernel

open PowerSeries

private theorem coeffNumeralMul (n k : ℕ) [Nat.AtLeastTwo k] (g : PowerSeries ℚ) :
    coeff n (ofNat(k) * g) = ofNat(k) * coeff n g := coeff_C_mul n g (ofNat(k) : ℚ)

/-- Ordinary generating function, given by its polynomial identity with unit denominator. -/
theorem generating_function :
    let F : PowerSeries ℚ := PowerSeries.mk (fun n => (a n : ℚ))
    (1 - 11 * X + 12 * X ^ 2) * F = 36 * X * (1 - 2 * X) := by
  dsimp only
  let F : PowerSeries ℚ := PowerSeries.mk (fun n => (a n : ℚ))
  change _ * F = _
  have hc (n : ℕ) : coeff n F = (a n : ℚ) := PowerSeries.coeff_mk _ _
  have h0 : a 0 = 0 := rfl
  calc
    _ = F - 11 * (X * F) + 12 * (X * (X * F)) := by ring
    _ = 36 * X - 72 * X ^ 2 := by
      ext n
      simp only [map_add, map_sub, coeffNumeralMul]
      rcases n with _ | _ | _ | n
      · simp
        rfl
      · norm_num [coeff_succ_X_mul, hc, h0, initial.1, coeff_X, coeff_X_pow]
      · norm_num [coeff_succ_X_mul, hc, h0, initial.1, initial.2, coeff_X, coeff_X_pow]
      · simp only [coeff_succ_X_mul, hc, coeff_X, coeff_X_pow]
        simp only [show n+1+1+1 ≠ 1 by omega, show n+1+1+1 ≠ 2 by omega, ite_false]
        have hr : (a (n+3) : ℚ) + 12 * a (n+1) = 11 * a (n+2) := by exact_mod_cast recurrence n
        linarith
    _ = _ := by ring

theorem closed_form (n : ℕ) : (a (n+1) : ℝ) = closedValue (n+1) := by
  let s : ℝ := Real.sqrt 73
  have hs : s^2 = 73 := Real.sq_sqrt (by norm_num)
  have hne : s ≠ 0 := by positivity
  let u := (11-s)/2
  let v := (11+s)/2
  have hu : u^2 + 12 = 11*u := by dsimp [u]; nlinarith
  have hv : v^2 + 12 = 11*v := by dsimp [v]; nlinarith
  have law (k : ℕ) :
      closedValue (k+2) + 12 * closedValue k = 11 * closedValue (k+1) := by
    change 3/s*((s-1)*u^(k+2)+(s+1)*v^(k+2)) + 12*(3/s*((s-1)*u^k+(s+1)*v^k)) =
      11*(3/s*((s-1)*u^(k+1)+(s+1)*v^(k+1)))
    rw [pow_add u k 2, pow_add v k 2, pow_succ u k, pow_succ v k]
    linear_combination (3/s*(s-1)*u^k)*hu + (3/s*(s+1)*v^k)*hv
  have one : (a 1 : ℝ) = closedValue 1 := by
    rw [initial.1]
    change (36 : ℝ) = 3/s * ((s-1)*((11-s)/2)^1+(s+1)*((11+s)/2)^1)
    field_simp
    ring
  have two : (a 2 : ℝ) = closedValue 2 := by
    rw [initial.2]
    change (324 : ℝ) = 3/s * ((s-1)*((11-s)/2)^2+(s+1)*((11+s)/2)^2)
    field_simp
    nlinarith [congrArg (fun x : ℝ => s*x) hs]
  have pairs (k : ℕ) : (a (k+1) : ℝ) = closedValue (k+1) ∧ (a (k+2) : ℝ) = closedValue (k+2) := by
    induction k with
    | zero => exact ⟨one,two⟩
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      have hr : (a (k+3) : ℝ) + 12 * a (k+1) = 11 * a (k+2) := by exact_mod_cast recurrence k
      rw [ih.1, ih.2] at hr
      linarith [law (k+1)]
  exact (pairs n).1

end A223299Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a223299.main := by
  exact ⟨A223299Proof.recurrence, A223299Proof.generating_function, A223299Proof.closed_form⟩
