import OMAStatements.S_oeis_a128392

namespace OMA.S_oeis_a128392

open PowerSeries




/-! ### Coefficients of `(1 - X ^ a) ^ n` and of the truncated product -/

theorem cpow (a : ℕ) (ha : 0 < a) (n : ℕ) : ∀ t r, r < a →
    coeff (a * t + r) ((1 - (X : PowerSeries ℤ) ^ a) ^ n) =
      if r = 0 then (-1) ^ t * (n.choose t : ℤ) else 0 := by
  induction n with
  | zero =>
    intro t r hr
    rw [pow_zero, coeff_one]
    rcases Nat.eq_zero_or_pos r with rfl | hr0
    · rcases Nat.eq_zero_or_pos t with rfl | ht
      · simp
      · simp [Nat.choose_eq_zero_of_lt ht]
        omega
    · simp [hr0.ne']
  | succ n ih =>
    intro t r hr
    have e : (1 - (X : PowerSeries ℤ) ^ a) ^ (n + 1) =
        (1 - X ^ a) ^ n - (1 - X ^ a) ^ n * X ^ a := by ring
    rw [e, map_sub, coeff_mul_X_pow']
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · rw [if_neg (by omega), sub_zero, ih 0 r hr]
      simp
    · obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
      rw [if_pos (by nlinarith), show a * (t' + 1) + r - a = a * t' + r by
        rw [mul_add, mul_one]; omega, ih (t' + 1) r hr, ih t' r hr]
      split_ifs
      · rw [Nat.choose_succ_succ', pow_succ]
        push_cast
        ring
      · simp

/-- `C(24, t)` for `t ≤ 6`, as a table. -/
def ch (t : ℕ) : ℤ := [1, 24, 276, 2024, 10626, 42504, 134596].getD t 0

theorem ch_eq (t : ℕ) (ht : t ≤ 6) : ch t = (Nat.choose 24 t : ℤ) := by
  interval_cases t <;> rfl

/-- The coefficient of `X ^ j` in `(1 - X ^ a) ^ 24`, for `j / a ≤ 6`. -/
def cf (a j : ℕ) : ℤ := if j % a = 0 then (-1) ^ (j / a) * ch (j / a) else 0

theorem coeff_factor (a j : ℕ) (ha : 0 < a) (hj : j / a ≤ 6) :
    coeff j ((1 - (X : PowerSeries ℤ) ^ a) ^ 24) = cf a j := by
  have h := cpow a ha 24 (j / a) (j % a) (Nat.mod_lt _ ha)
  rw [Nat.div_add_mod] at h
  rw [h, cf]
  split_ifs
  · rw [ch_eq _ hj]
  · rfl

/-- The coefficients of `∏_{i < m} (1 - X ^ (i + 1)) ^ 24`, by convolution. -/
def M : ℕ → ℕ → ℤ
  | 0, j => if j = 0 then 1 else 0
  | m + 1, j => ∑ i ∈ Finset.range (j + 1), M m i * cf (m + 1) (j - i)

theorem coeff_prod (m : ℕ) : ∀ j, j ≤ 6 →
    coeff j (∏ i ∈ Finset.range m, (1 - (X : PowerSeries ℤ) ^ (i + 1)) ^ 24) = M m j := by
  induction m with
  | zero =>
    intro j _
    simp [M, coeff_one]
  | succ m ih =>
    intro j hj
    rw [Finset.prod_range_succ, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, M]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have hi' : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [ih i (by omega), coeff_factor (m + 1) (j - i) (by omega)
      (le_trans (Nat.div_le_self _ _) (by omega))]

theorem tau_succ (n : ℕ) :
    tau (n + 1) = coeff n (∏ m ∈ Finset.range (n + 1), (1 - (X : PowerSeries ℤ) ^ (m + 1)) ^ 24) := by
  unfold tau
  rw [coeff_succ_X_mul]

theorem tau_one : tau 1 = 1 := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, tau_succ, coeff_prod 1 0 (by norm_num)]
  decide +kernel

theorem tau_two : tau 2 = -24 := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, tau_succ, coeff_prod 2 1 (by norm_num)]
  decide +kernel

theorem tau_seven : tau 7 = -16744 := by
  rw [show (7 : ℕ) = 6 + 1 from rfl, tau_succ, coeff_prod 7 6 (by norm_num)]
  decide +kernel

/-! ### The matrix A126988 at the indices 1, 2 and 7 -/

theorem app_one (g : ℕ → ℤ) : app g 1 = g 1 := by
  simp [app, T]

theorem app_two (g : ℕ → ℤ) : app g 2 = 2 * g 1 + g 2 := by
  simp only [app]
  rw [show Finset.Icc 1 2 = {1, 2} by decide]
  simp [T]

theorem app_seven (g : ℕ → ℤ) : app g 7 = 7 * g 1 + g 7 := by
  simp only [app]
  rw [show Finset.Icc 1 7 = {1, 2, 3, 4, 5, 6, 7} by decide]
  simp [T, Finset.sum_insert]

theorem iter (k : ℕ) : (app^[k] tau) 1 = tau 1 ∧ (app^[k] tau) 2 = tau 2 + 2 * k * tau 1 ∧
    (app^[k] tau) 7 = tau 7 + 7 * k * tau 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    obtain ⟨h1, h2, h7⟩ := ih
    rw [Function.iterate_succ_apply']
    refine ⟨?_, ?_, ?_⟩
    · rw [app_one, h1]
    · rw [app_two, h1, h2]
      push_cast
      ring
    · rw [app_seven, h1, h7]
      push_cast
      ring

/-- Control: the zero of A128392 itself, at n = 2 for k = 12. -/
theorem control : (app^[12] tau) 2 = 0 := by
  rw [(iter 12).2.1, tau_two, tau_one]
  norm_num

theorem disproof : ¬ (∀ k : ℕ, 1 ≤ k → ((∃ n : ℕ, 1 ≤ n ∧ (app^[k] tau) n = 0) ↔ k = 12)) := by
  intro h
  have hz : (app^[2392] tau) 7 = 0 := by
    rw [(iter 2392).2.2, tau_seven, tau_one]
    norm_num
  have := (h 2392 (by norm_num)).mp ⟨7, by norm_num, hz⟩
  norm_num at this

end OMA.S_oeis_a128392

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a128392.main) :=
  OMA.S_oeis_a128392.disproof
