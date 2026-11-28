import OMAStatements.S_oeis_a222993

/-!
Proof of Barker's two conjectures for A222993 (n X 2 arrays with entries 0..2 whose successive
rows and successive columns have nondecreasing least-squares slopes).

For a row of two cells the least-squares slope is the right entry minus the left entry
(`a222993_slope_two`), so the row condition says that the row differences
`d i = M i 1 - M i 0` (`a222993D`) are nondecreasing from top to bottom (`a222993_chain_iff`).
The column condition then holds automatically: with `x̄` the mean row index, the least-squares
numerator of a column `c` is `Σ (i - x̄)(c i - c̄) = Σ i c i - (Σ i)(Σ c)/n` (`a222993_centred`), so
slope(column 1) - slope(column 0) has the sign of `n Σ i d i - (Σ i)(Σ d)`, which is nonnegative by
Chebyshev's sum inequality because `d` and the index are both nondecreasing (`a222993_col_le`).
Hence an array is good iff `d` is nondecreasing (`a222993_good_iff`).

Let `C m lo` (`a222993C`) count sequences of `m` rows whose differences are nondecreasing and at
least `lo`. Putting a row `p` in front of such a sequence keeps it valid iff `lo ≤ d(p)` and the
rest is valid with bound `d(p)` (`a222993_cons`), so `C 0 lo = 1` and
`C (m+1) lo = Σ_{p : lo ≤ d(p)} C m (d(p))`. A difference `e` occurs for `3 - |e|` of the nine
rows, which gives the recursions `a222993_step2`, ..., `a222993_stepm2` and, by induction,
  C m 2 = 1, C m 1 = 2^(m+1) - 1, C m 0 = (3^(m+2) + 1)/2 - 2^(m+2),
  C m (-1) = 27 3^m/2 - 4(m+3)2^m - 1/2, C m (-2) = (3^(m+4) - 2^(m+5)(m+2) - 2m - 13)/4.
Since every difference is at least -2, a(n) = C n (-2) (`a222993_a_eq`), which is Barker's closed
form. The generating function follows by comparing coefficients: the closed form gives the
recurrence a(n) = 9a(n-1) - 31a(n-2) + 51a(n-3) - 40a(n-4) + 12a(n-5), and the first five
coefficients are checked directly.
-/

namespace OMA.Helpers

open OMA.S_oeis_a222993 (Good T a)

/-- The least-squares slope of two points is the difference of their values. -/
theorem a222993_slope_two (v : Fin 2 → ℕ) : S_oeis_a222993.slope v = (v 1 : ℚ) - v 0 := by
  unfold S_oeis_a222993.slope
  simp [Fin.sum_univ_two]
  field_simp
  ring

/-- The centred cross sum: `Σ (i - x̄)(c i - c̄) = Σ i c i - (Σ i)(Σ c)/m`. -/
theorem a222993_centred {m : ℕ} (hm : (m : ℚ) ≠ 0) (c : Fin m → ℚ) :
    ∑ i : Fin m, (((i : ℕ) : ℚ) - (∑ i : Fin m, ((i : ℕ) : ℚ)) / m) *
        (c i - (∑ i : Fin m, c i) / m) =
      ∑ i : Fin m, ((i : ℕ) : ℚ) * c i - (∑ i : Fin m, ((i : ℕ) : ℚ)) * (∑ i : Fin m, c i) / m := by
  simp only [sub_mul, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

/-- Column comparison: if the difference of two columns is monotone, their least-squares slopes
are in order (Chebyshev's sum inequality). -/
theorem a222993_col_le {m : ℕ} (v w : Fin m → ℕ)
    (h : Monotone fun i => (w i : ℚ) - (v i : ℚ)) :
    S_oeis_a222993.slope v ≤ S_oeis_a222993.slope w := by
  unfold S_oeis_a222993.slope
  split_ifs with hm
  · exact le_rfl
  · have hm0 : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hpos : (0 : ℚ) < m := by positivity
    dsimp only
    apply div_le_div_of_nonneg_right ?_ (Finset.sum_nonneg fun i _ => sq_nonneg _)
    rw [a222993_centred hm0 (fun i => (v i : ℚ)), a222993_centred hm0 (fun i => (w i : ℚ))]
    have hidx : Monotone fun i : Fin m => ((i : ℕ) : ℚ) := fun a b hab => Nat.cast_le.mpr hab
    have cheb := (h.monovary hidx).sum_mul_sum_le_card_mul_sum
    simp only [Fintype.card_fin, Finset.sum_sub_distrib, sub_mul] at cheb
    have key : (∑ i : Fin m, ((i : ℕ) : ℚ)) * (∑ i : Fin m, (w i : ℚ)) / m -
        (∑ i : Fin m, ((i : ℕ) : ℚ)) * (∑ i : Fin m, (v i : ℚ)) / m ≤
        ∑ i : Fin m, ((i : ℕ) : ℚ) * (w i : ℚ) - ∑ i : Fin m, ((i : ℕ) : ℚ) * (v i : ℚ) := by
      rw [← sub_div, div_le_iff₀ hpos]
      have e1 : ∑ i : Fin m, ((i : ℕ) : ℚ) * (w i : ℚ) = ∑ i : Fin m, (w i : ℚ) * ((i : ℕ) : ℚ) :=
        Finset.sum_congr rfl fun i _ => mul_comm _ _
      have e2 : ∑ i : Fin m, ((i : ℕ) : ℚ) * (v i : ℚ) = ∑ i : Fin m, (v i : ℚ) * ((i : ℕ) : ℚ) :=
        Finset.sum_congr rfl fun i _ => mul_comm _ _
      rw [e1, e2]
      nlinarith [cheb]
    linarith


/-- The difference (right entry minus left entry) of a row of two cells. -/
def a222993D (p : Fin 2 → Fin 3) : ℤ := ((p 1 : ℕ) : ℤ) - ((p 0 : ℕ) : ℤ)

theorem a222993_D_ge (p : Fin 2 → Fin 3) : -2 ≤ a222993D p := by
  unfold a222993D
  have := (p 0).isLt
  omega

/-- On `Fin m`, a sequence is monotone iff each term is at most the next one. -/
theorem a222993_chain_iff {m : ℕ} (f : Fin m → ℤ) :
    (∀ i i' : Fin m, i.val + 1 = i'.val → f i ≤ f i') ↔ Monotone f := by
  cases m with
  | zero => exact ⟨fun _ => Subsingleton.monotone f, fun _ i => i.elim0⟩
  | succ k =>
    rw [Fin.monotone_iff_le_succ]
    constructor
    · intro h i
      exact h _ _ (by simp)
    · intro h i i' hii'
      have hi : i.val < k := by have := i'.isLt; omega
      have e1 : i = Fin.castSucc ⟨i.val, hi⟩ := Fin.ext rfl
      have e2 : i' = Fin.succ ⟨i.val, hi⟩ := Fin.ext (by simp; omega)
      rw [e1, e2]
      exact h _

/-- An n X 2 array is good iff the row differences are nondecreasing from top to bottom. -/
theorem a222993_good_iff {n : ℕ} (M : Fin n → Fin 2 → Fin 3) :
    Good M ↔ Monotone fun i => a222993D (M i) := by
  have hrow : ∀ i, S_oeis_a222993.slope (fun j => (M i j : ℕ)) = (a222993D (M i) : ℚ) := by
    intro i
    rw [a222993_slope_two]
    simp [a222993D]
  rw [← a222993_chain_iff]
  constructor
  · intro h i i' hii'
    have := h.1 i i' hii'
    rw [hrow, hrow] at this
    exact_mod_cast this
  · intro h
    refine ⟨fun i i' hii' => ?_, fun j j' hjj' => ?_⟩
    · rw [hrow, hrow]
      exact_mod_cast h i i' hii'
    · have hj'lt := j'.isLt
      have hj : j = 0 := Fin.ext (by rw [Fin.val_zero]; omega)
      have hj' : j' = 1 := Fin.ext (by rw [Fin.val_one]; omega)
      subst hj hj'
      apply a222993_col_le
      have hm : Monotone fun i => a222993D (M i) := (a222993_chain_iff _).mp h
      intro x y hxy
      have := hm hxy
      simp only [a222993D] at this
      simp only
      exact_mod_cast this

/-- The number of sequences of `m` rows whose differences are nondecreasing and at least `lo`. -/
noncomputable def a222993C (m : ℕ) (lo : ℤ) : ℕ := by
  classical
  exact ∑ g : Fin m → Fin 2 → Fin 3,
    if Monotone (Matrix.vecCons lo fun i => a222993D (g i)) then 1 else 0

theorem a222993_cons {m : ℕ} (lo : ℤ) (p : Fin 2 → Fin 3) (g : Fin m → Fin 2 → Fin 3) :
    Monotone (Matrix.vecCons lo fun i =>
        a222993D ((Fin.cons p g : Fin (m + 1) → Fin 2 → Fin 3) i)) ↔
      lo ≤ a222993D p ∧ Monotone (Matrix.vecCons (a222993D p) fun i => a222993D (g i)) := by
  have e : (fun i => a222993D ((Fin.cons p g : Fin (m + 1) → Fin 2 → Fin 3) i)) =
      Matrix.vecCons (a222993D p) fun i => a222993D (g i) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  rw [e, monotone_vecCons]
  simp

theorem a222993_C_zero (lo : ℤ) : a222993C 0 lo = 1 := by
  classical
  unfold a222993C
  rw [Fintype.sum_unique]
  exact if_pos (Subsingleton.monotone _)

theorem a222993_C_succ (m : ℕ) (lo : ℤ) :
    a222993C (m + 1) lo =
      ∑ p : Fin 2 → Fin 3, if lo ≤ a222993D p then a222993C m (a222993D p) else 0 := by
  classical
  unfold a222993C
  rw [Fintype.sum_equiv (Fin.consEquiv fun _ => Fin 2 → Fin 3).symm _
    (fun x => if Monotone (Matrix.vecCons lo fun i =>
      a222993D ((Fin.cons x.1 x.2 : Fin (m + 1) → Fin 2 → Fin 3) i)) then 1 else 0)
    (fun g => by simp), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [a222993_cons]
  split_ifs with hp
  · exact Finset.sum_congr rfl fun g _ => if_congr (and_iff_right hp) rfl rfl
  · exact Finset.sum_eq_zero fun g _ => if_neg fun h => hp h.1

theorem a222993_a_eq (n : ℕ) : a n = a222993C n (-2) := by
  classical
  unfold a T a222993C
  rw [Fintype.card_subtype, Finset.card_filter]
  refine Finset.sum_congr rfl fun M _ => if_congr ?_ rfl rfl
  rw [a222993_good_iff]
  cases n with
  | zero => exact ⟨fun _ => Subsingleton.monotone _, fun _ => Subsingleton.monotone _⟩
  | succ k =>
    rw [monotone_vecCons]
    exact ⟨fun h => ⟨a222993_D_ge _, h⟩, fun h => h.2⟩


theorem a222993_C_succ_nine (m : ℕ) (lo : ℤ) :
    a222993C (m + 1) lo = ∑ x : Fin 3, ∑ y : Fin 3,
      if lo ≤ ((y : ℕ) : ℤ) - ((x : ℕ) : ℤ) then a222993C m (((y : ℕ) : ℤ) - ((x : ℕ) : ℤ))
      else 0 := by
  rw [a222993_C_succ, Fintype.sum_equiv (piFinTwoEquiv fun _ => Fin 3)
    (fun p => if lo ≤ a222993D p then a222993C m (a222993D p) else 0)
    (fun q => if lo ≤ ((q.2 : ℕ) : ℤ) - ((q.1 : ℕ) : ℤ) then
      a222993C m (((q.2 : ℕ) : ℤ) - ((q.1 : ℕ) : ℤ)) else 0) (fun p => rfl),
    Fintype.sum_prod_type]

theorem a222993_step2 (m : ℕ) : a222993C (m + 1) 2 = a222993C m 2 := by
  rw [a222993_C_succ_nine]
  simp [Fin.sum_univ_three]

theorem a222993_step1 (m : ℕ) : a222993C (m + 1) 1 = 2 * a222993C m 1 + a222993C m 2 := by
  rw [a222993_C_succ_nine]
  simp [Fin.sum_univ_three]
  ring

theorem a222993_step0 (m : ℕ) :
    a222993C (m + 1) 0 = 3 * a222993C m 0 + 2 * a222993C m 1 + a222993C m 2 := by
  rw [a222993_C_succ_nine]
  simp [Fin.sum_univ_three]
  ring

theorem a222993_stepm1 (m : ℕ) :
    a222993C (m + 1) (-1) =
      2 * a222993C m (-1) + 3 * a222993C m 0 + 2 * a222993C m 1 + a222993C m 2 := by
  rw [a222993_C_succ_nine]
  simp [Fin.sum_univ_three]
  ring

theorem a222993_stepm2 (m : ℕ) :
    a222993C (m + 1) (-2) = a222993C m (-2) + 2 * a222993C m (-1) + 3 * a222993C m 0 +
      2 * a222993C m 1 + a222993C m 2 := by
  rw [a222993_C_succ_nine]
  simp [Fin.sum_univ_three]
  ring


theorem a222993_closed (m : ℕ) :
    (a222993C m 2 : ℚ) = 1 ∧
    (a222993C m 1 : ℚ) = 2 ^ (m + 1) - 1 ∧
    (a222993C m 0 : ℚ) = (3 ^ (m + 2) + 1) / 2 - 2 ^ (m + 2) ∧
    (a222993C m (-1) : ℚ) = 27 * 3 ^ m / 2 - 4 * ((m : ℚ) + 3) * 2 ^ m - 1 / 2 ∧
    (a222993C m (-2) : ℚ) = (3 ^ (m + 4) - 2 ^ (m + 5) * ((m : ℚ) + 2) - 2 * m - 13) / 4 := by
  induction m with
  | zero =>
    simp only [a222993_C_zero]
    norm_num
  | succ m ih =>
    obtain ⟨h2, h1, h0, hm1, hm2⟩ := ih
    rw [a222993_step2, a222993_step1, a222993_step0, a222993_stepm1, a222993_stepm2]
    push_cast
    refine ⟨h2, ?_, ?_, ?_, ?_⟩
    · rw [h1, h2]
      ring
    · rw [h0, h1, h2]
      ring
    · rw [hm1, h0, h1, h2]
      ring
    · rw [hm2, hm1, h0, h1, h2]
      ring

theorem a222993_a_closed (n : ℕ) :
    (a n : ℚ) = (3 ^ (n + 4) - 2 ^ (n + 5) * ((n : ℚ) + 2) - 2 * n - 13) / 4 := by
  rw [a222993_a_eq]
  exact (a222993_closed n).2.2.2.2

theorem a222993_barker (n : ℕ) (_hn : 1 ≤ n) :
    (a n : ℚ) = (-13 - 2 ^ (6 + n) + 3 ^ (4 + n) - 2 * (1 + 2 ^ (4 + n)) * n) / 4 := by
  rw [a222993_a_closed]
  ring

open PowerSeries in
theorem a222993_gf :
    (PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ))) *
        ((1 - X) ^ 2 * (1 - 2 * X) ^ 2 * (1 - 3 * X)) =
      X * (9 - 31 * X + 51 * X ^ 2 - 40 * X ^ 3 + 12 * X ^ 4) := by
  set F : ℕ → ℚ := fun n => if n = 0 then (0 : ℚ) else (a n : ℚ) with hF
  have key : PowerSeries.mk F * ((1 - X) ^ 2 * (1 - 2 * X) ^ 2 * (1 - 3 * X)) =
      PowerSeries.mk F * X ^ 0 - C 9 * (PowerSeries.mk F * X ^ 1) +
        C 31 * (PowerSeries.mk F * X ^ 2) - C 51 * (PowerSeries.mk F * X ^ 3) +
        C 40 * (PowerSeries.mk F * X ^ 4) - C 12 * (PowerSeries.mk F * X ^ 5) := by
    simp only [map_ofNat]
    ring
  have hrhs : (X : ℚ⟦X⟧) * (9 - 31 * X + 51 * X ^ 2 - 40 * X ^ 3 + 12 * X ^ 4) =
      C 9 * X ^ 1 - C 31 * X ^ 2 + C 51 * X ^ 3 - C 40 * X ^ 4 + C 12 * X ^ 5 := by
    simp only [map_ofNat]
    ring
  rw [key, hrhs]
  ext k
  simp only [map_sub, map_add, coeff_C_mul_X_pow]
  simp only [coeff_C_mul, coeff_mul_X_pow', coeff_mk]
  by_cases hk : k < 6
  · interval_cases k <;> simp [hF, a222993_a_closed] <;> norm_num
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 6 := ⟨k - 6, by omega⟩
    simp only [show 1 ≤ j + 6 by omega, show 2 ≤ j + 6 by omega, show 3 ≤ j + 6 by omega,
      show 4 ≤ j + 6 by omega, show 5 ≤ j + 6 by omega, zero_le,
      show j + 6 - 0 = j + 6 by omega, show j + 6 - 1 = j + 5 by omega,
      show j + 6 - 2 = j + 4 by omega, show j + 6 - 3 = j + 3 by omega,
      show j + 6 - 4 = j + 2 by omega, show j + 6 - 5 = j + 1 by omega,
      show ¬ (j + 6 = 1) by omega, show ¬ (j + 6 = 2) by omega, show ¬ (j + 6 = 3) by omega,
      show ¬ (j + 6 = 4) by omega, show ¬ (j + 6 = 5) by omega,
      show ¬ (j + 6 = 0) by omega, show ¬ (j + 5 = 0) by omega, show ¬ (j + 4 = 0) by omega,
      show ¬ (j + 3 = 0) by omega, show ¬ (j + 2 = 0) by omega, show ¬ (j + 1 = 0) by omega,
      if_true, if_false, hF]
    rw [a222993_a_closed, a222993_a_closed, a222993_a_closed, a222993_a_closed,
      a222993_a_closed, a222993_a_closed]
    push_cast
    ring

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a222993.main :=
  ⟨OMA.Helpers.a222993_gf, OMA.Helpers.a222993_barker⟩
