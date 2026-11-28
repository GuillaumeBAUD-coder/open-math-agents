import OMAStatements.S_oeis_a267847
import Mathlib

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Rule 227 maps (l,c,r) to (l and (c or r)) or (not l and not c). By induction, after t+2 steps every cell is ON except cells t and t+2. So for n>=2 the row -n..n reads 1...1010, i.e. a(n) = 2^(2n+1) - 6 = 2(4^n - 3) (geometric sum); the recurrence and generating function follow. No computer search.

namespace OMA.P_oeis_a267847

open OMA.S_oeis_a267847

lemma r227 (l c r : Bool) : ruleOut 227 l c r = ((l && (c || r)) || (!l && !c)) := by
  cases l <;> cases c <;> cases r <;> decide

lemma cs (t : ℕ) (i : ℤ) : cell 227 (t+1) i =
    ((cell 227 t (i-1) && (cell 227 t i || cell 227 t (i+1))) || (!cell 227 t (i-1) && !cell 227 t i)) := by
  show ruleOut 227 _ _ _ = _
  rw [r227]

lemma c0 (i : ℤ) : cell 227 0 i = decide (i = 0) := rfl
lemma c1 (i : ℤ) : cell 227 1 i = decide (i ≠ 0 ∧ i ≠ 1) := by
  rw [cs, c0, c0, c0, Bool.eq_iff_iff]; simp; omega

lemma cellE (t : ℕ) (i : ℤ) : cell 227 (t+2) i = decide (i ≠ t ∧ i ≠ t+2) := by
  induction t generalizing i with
  | zero => rw [cs, c1, c1, c1, Bool.eq_iff_iff]; simp; omega
  | succ t ih => rw [show t+1+2 = (t+2)+1 by ring, cs, ih, ih, ih, Bool.eq_iff_iff]; simp; omega

lemma g (m : ℕ) : ∑ j ∈ Finset.range m, (2:ℤ) ^ (m - j) = 2 ^ (m+1) - 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, show m + 1 - m = 1 by omega]
    have : ∑ j ∈ Finset.range m, (2:ℤ) ^ (m + 1 - j) = 2 * ∑ j ∈ Finset.range m, (2:ℤ) ^ (m - j) := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j hj
      simp only [Finset.mem_range] at hj
      rw [show m + 1 - j = (m - j) + 1 by omega, pow_succ]; ring
    rw [this, ih]; ring

lemma aE (n : ℕ) : a (n+2) = 2 ^ (2*n+5) - 6 := by
  unfold a
  rw [show 2*(n+2)+1 = (2*n+2) + 3 by ring, Finset.sum_range_add]
  have h1 : ∑ x ∈ Finset.range (2*n+2), (if cell 227 (n+2) ((x:ℤ) - ((n+2:ℕ):ℤ)) then (2:ℤ) ^ (2*(n+2) - x) else 0)
      = 4 * ∑ j ∈ Finset.range (2*n+2), (2:ℤ) ^ ((2*n+2) - j) := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j hj
    simp only [Finset.mem_range] at hj
    rw [cellE, decide_eq_true (by push_cast; omega), if_pos rfl,
      show 2*(n+2) - j = (2*n+2-j) + 2 by omega, pow_add]; ring
  rw [h1, g]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, cellE]
  rw [decide_eq_false (by push_cast; omega), decide_eq_true (by push_cast; omega), decide_eq_false (by push_cast; omega)]
  simp only [Bool.false_eq_true, if_false, if_true, show 2*(n+2) - (2*n+2+1) = 1 by omega]
  rw [show 2*n+5 = (2*n+2+1) + 2 by ring, pow_add]; ring

lemma ps (f : ℕ → ℚ) (n k : ℕ) :
    PowerSeries.coeff n (PowerSeries.mk f * PowerSeries.X ^ k) = if k ≤ n then f (n-k) else 0 := by
  rw [PowerSeries.coeff_mul_X_pow']; simp

lemma ps1 (f : ℕ → ℚ) (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.mk f * PowerSeries.X) = if 1 ≤ n then f (n-1) else 0 := by
  rw [← ps, pow_one]

lemma a0 : a 0 = 1 := by decide
lemma a1 : a 1 = 4 := by decide

open PowerSeries in
theorem main_proof :
    (∀ n : ℕ, 4 ≤ n → (a n : ℚ) = 5 * a (n - 1) - 4 * a (n - 2)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) * (1 - 4 * X) : PowerSeries ℚ) = 1 - X + 10 * X ^ 2 + 8 * X ^ 3) ∧
    (∀ n : ℕ, 2 ≤ n → (a n : ℚ) = 2 * ((4 : ℚ) ^ n - 3)) := by
  have cf : ∀ n : ℕ, 2 ≤ n → (a n : ℚ) = 2 * ((4 : ℚ) ^ n - 3) := by
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n-2, by omega⟩
    rw [aE]; push_cast
    rw [show 2*m+5 = 2*(m+2)+1 by ring, pow_succ, pow_mul]; norm_num; ring
  have hrec : ∀ n : ℕ, 4 ≤ n → (a n : ℚ) = 5 * a (n - 1) - 4 * a (n - 2) := by
    intro n hn
    rw [cf n (by omega), cf (n-1) (by omega), cf (n-2) (by omega)]
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n-4, by omega⟩
    simp only [show m+4-1 = m+3 by omega, show m+4-2 = m+2 by omega, pow_succ]; ring
  refine ⟨hrec, ?_, cf⟩
  rw [show ((1 - X) * (1 - 4 * X) : PowerSeries ℚ) = 1 - C (5:ℚ) * X + C (4:ℚ) * X ^ 2 by simp only [map_ofNat]; ring]
  rw [show (1 - X + 10 * X ^ 2 + 8 * X ^ 3 : PowerSeries ℚ) = 1 - X + C (10:ℚ) * X ^ 2 + C (8:ℚ) * X ^ 3 by simp only [map_ofNat]]
  ext n
  simp only [mul_add, mul_sub, mul_one, map_add, map_sub, mul_left_comm _ (C _), PowerSeries.coeff_C_mul, ps, ps1, PowerSeries.coeff_X,
    PowerSeries.coeff_mk, PowerSeries.coeff_X_pow, PowerSeries.coeff_one]
  have a2 : (a 2 : ℚ) = 26 := by rw [cf 2 le_rfl]; norm_num
  have a3 : (a 3 : ℚ) = 122 := by rw [cf 3 (by norm_num)]; norm_num
  rcases (show n ≤ 3 ∨ 4 ≤ n by omega) with h | h
  · interval_cases n <;> simp [a0, a1, a2, a3] <;> try norm_num
  · rw [hrec n h]
    simp [show n ≠ 0 by omega, show n ≠ 1 by omega, show n ≠ 2 by omega, show n ≠ 3 by omega, show 1 ≤ n by omega, show 2 ≤ n by omega]
end OMA.P_oeis_a267847

theorem OMA.solution : type_of% @OMA.S_oeis_a267847.main :=
  OMA.P_oeis_a267847.main_proof
