import OMAStatements.S_oeis_a267926
import Mathlib

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Rule 246 maps (l,c,r) to (l or c or r) and (l or not c or not r). By induction cell t i is ON iff -t <= i <= t and (i - t) mod 4 is not 1. Hence row n+2 is row n followed by the bits 0111, so a(n+2) = 16 a(n) + 7, which gives the recurrence and the generating function. No computer search.

namespace OMA.P_oeis_a267926

open OMA.S_oeis_a267926

lemma r246 (l c r : Bool) : ruleOut 246 l c r = ((l || c || r) && (l || !c || !r)) := by
  cases l <;> cases c <;> cases r <;> decide

lemma cellE (t : ℕ) (i : ℤ) : cell 246 t i = decide (-(t:ℤ) ≤ i ∧ i ≤ t ∧ (i - t) % 4 ≠ 1) := by
  induction t generalizing i with
  | zero => show decide (i = 0) = _; rw [Bool.eq_iff_iff]; simp; omega
  | succ t ih =>
    show ruleOut 246 _ _ _ = _
    rw [r246, ih, ih, ih, Bool.eq_iff_iff]; simp; omega

lemma step (n : ℕ) : a (n+2) = 16 * a n + 7 := by
  unfold a
  rw [show 2*(n+2)+1 = (2*n+1) + 4 by ring, Finset.sum_range_add, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro j hj
    simp only [Finset.mem_range] at hj
    rw [cellE, cellE]
    have hc : (-((n+2:ℕ):ℤ) ≤ (j:ℤ) - ((n+2:ℕ):ℤ) ∧ (j:ℤ) - ((n+2:ℕ):ℤ) ≤ ((n+2:ℕ):ℤ) ∧ ((j:ℤ) - ((n+2:ℕ):ℤ) - ((n+2:ℕ):ℤ)) % 4 ≠ 1) ↔
        (-(n:ℤ) ≤ (j:ℤ) - n ∧ (j:ℤ) - n ≤ n ∧ ((j:ℤ) - n - n) % 4 ≠ 1) := by push_cast; omega
    by_cases h : (-(n:ℤ) ≤ (j:ℤ) - n ∧ (j:ℤ) - n ≤ n ∧ ((j:ℤ) - n - n) % 4 ≠ 1)
    · rw [decide_eq_true (hc.mpr h), decide_eq_true h, if_pos rfl, if_pos rfl,
        show 2*(n+2) - j = (2*n-j) + 4 by omega, pow_add]; ring
    · rw [decide_eq_false (fun h' => h (hc.mp h')), decide_eq_false h]; simp
  · simp only [Finset.sum_range_succ, Finset.sum_range_zero, cellE]
    have e0 : ¬ ((-((n+2:ℕ):ℤ) ≤ ((2*n+1+0:ℕ):ℤ) - ((n+2:ℕ):ℤ) ∧ ((2*n+1+0:ℕ):ℤ) - ((n+2:ℕ):ℤ) ≤ ((n+2:ℕ):ℤ) ∧ (((2*n+1+0:ℕ):ℤ) - ((n+2:ℕ):ℤ) - ((n+2:ℕ):ℤ)) % 4 ≠ 1)) := by push_cast; omega
    have e1 : ((-((n+2:ℕ):ℤ) ≤ ((2*n+1+1:ℕ):ℤ) - ((n+2:ℕ):ℤ) ∧ ((2*n+1+1:ℕ):ℤ) - ((n+2:ℕ):ℤ) ≤ ((n+2:ℕ):ℤ) ∧ (((2*n+1+1:ℕ):ℤ) - ((n+2:ℕ):ℤ) - ((n+2:ℕ):ℤ)) % 4 ≠ 1)) := by push_cast; omega
    have e2 : ((-((n+2:ℕ):ℤ) ≤ ((2*n+1+2:ℕ):ℤ) - ((n+2:ℕ):ℤ) ∧ ((2*n+1+2:ℕ):ℤ) - ((n+2:ℕ):ℤ) ≤ ((n+2:ℕ):ℤ) ∧ (((2*n+1+2:ℕ):ℤ) - ((n+2:ℕ):ℤ) - ((n+2:ℕ):ℤ)) % 4 ≠ 1)) := by push_cast; omega
    have e3 : ((-((n+2:ℕ):ℤ) ≤ ((2*n+1+3:ℕ):ℤ) - ((n+2:ℕ):ℤ) ∧ ((2*n+1+3:ℕ):ℤ) - ((n+2:ℕ):ℤ) ≤ ((n+2:ℕ):ℤ) ∧ (((2*n+1+3:ℕ):ℤ) - ((n+2:ℕ):ℤ) - ((n+2:ℕ):ℤ)) % 4 ≠ 1)) := by push_cast; omega
    rw [decide_eq_false e0, decide_eq_true e1, decide_eq_true e2, decide_eq_true e3]
    simp only [Bool.false_eq_true, if_false, if_true]
    rw [show 2*(n+2) - (2*n+1+1) = 2 by omega, show 2*(n+2) - (2*n+1+2) = 1 by omega,
      show 2*(n+2) - (2*n+1+3) = 0 by omega]
    norm_num

lemma a0 : a 0 = 1 := by decide
lemma a1 : a 1 = 7 := by decide

lemma ps (f : ℕ → ℚ) (n k : ℕ) :
    PowerSeries.coeff n (PowerSeries.mk f * PowerSeries.X ^ k) = if k ≤ n then f (n-k) else 0 := by
  rw [PowerSeries.coeff_mul_X_pow']; simp

lemma ps1 (f : ℕ → ℚ) (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.mk f * PowerSeries.X) = if 1 ≤ n then f (n-1) else 0 := by
  rw [← ps, pow_one]

open PowerSeries in
theorem main_proof :
    (∀ n : ℕ, 3 ≤ n → (a n : ℚ) = a (n - 1) + 16 * a (n - 2) - 16 * a (n - 3)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) * (1 - 4 * X) * (1 + 4 * X) : PowerSeries ℚ) = 1 + 6 * X) := by
  have hrec : ∀ n : ℕ, 3 ≤ n → (a n : ℚ) = a (n - 1) + 16 * a (n - 2) - 16 * a (n - 3) := by
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n-3, by omega⟩
    simp only [show m+3-1 = m+2 by omega, show m+3-2 = m+1 by omega, show m+3-3 = m by omega]
    rw [show m+3 = (m+1)+2 by ring, step, step]; push_cast; ring
  refine ⟨hrec, ?_⟩
  rw [show ((1 - X) * (1 - 4 * X) * (1 + 4 * X) : PowerSeries ℚ) = 1 - X - C (16:ℚ) * X ^ 2 + C (16:ℚ) * X ^ 3 by simp only [map_ofNat]; ring]
  rw [show (1 + 6 * X : PowerSeries ℚ) = 1 + C (6:ℚ) * X by simp only [map_ofNat]]
  ext n
  simp only [mul_add, mul_sub, mul_one, map_add, map_sub, mul_left_comm _ (C _), PowerSeries.coeff_C_mul, ps, ps1, PowerSeries.coeff_X,
    PowerSeries.coeff_mk, PowerSeries.coeff_X_pow, PowerSeries.coeff_one]
  have a2 : a 2 = 23 := by rw [show (2:ℕ) = 0 + 2 by rfl, step, a0]; norm_num
  rcases (show n ≤ 2 ∨ 3 ≤ n by omega) with h | h
  · interval_cases n <;> simp [a0, a1, a2] <;> try norm_num
  · rw [hrec n h]
    simp [show n ≠ 0 by omega, show n ≠ 1 by omega, show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega]
    ring
end OMA.P_oeis_a267926

theorem OMA.solution : type_of% @OMA.S_oeis_a267926.main :=
  OMA.P_oeis_a267926.main_proof
