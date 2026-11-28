import OMAStatements.S_oeis_a266250
import Mathlib

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Rule 9 maps (l,c,r) to (not l) and (c = r). Steps 0..4 are computed cell by cell; from step 4 on, by induction, step 2k+4 has ON cells exactly 2k,2k+1,2k+2,2k+4 and step 2k+5 has OFF cells exactly 2k-1,2k+1,...,2k+5. So the ON count is 4 at even t>=4 and 2t-5 at odd t>=5; summing gives the closed form, and recurrence and generating function follow coefficientwise. No computer search.

namespace OMA.P_oeis_a266250

open OMA.S_oeis_a266250

lemma r9 (l c r : Bool) : ruleOut 9 l c r = (!l && (c && r || !c && !r)) := by
  cases l <;> cases c <;> cases r <;> decide

lemma cs (t : ℕ) (i : ℤ) : cell 9 (t+1) i =
    (!cell 9 t (i-1) && (cell 9 t i && cell 9 t (i+1) || !cell 9 t i && !cell 9 t (i+1))) := by
  show ruleOut 9 _ _ _ = _
  rw [r9]

lemma c0 (i : ℤ) : cell 9 0 i = decide (i = 0) := rfl
lemma c1 (i : ℤ) : cell 9 1 i = decide (i ≠ -1 ∧ i ≠ 0 ∧ i ≠ 1) := by
  rw [cs, c0, c0, c0, Bool.eq_iff_iff]; simp; omega
lemma c2 (i : ℤ) : cell 9 2 i = decide (i = 0 ∨ i = 2) := by
  rw [cs, c1, c1, c1, Bool.eq_iff_iff]; simp; omega
lemma c3 (i : ℤ) : cell 9 3 i = decide (i ≠ -1 ∧ i ≠ 0 ∧ i ≠ 1 ∧ i ≠ 2 ∧ i ≠ 3) := by
  rw [cs, c2, c2, c2, Bool.eq_iff_iff]; simp; omega
lemma c4 (i : ℤ) : cell 9 4 i = decide (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 4) := by
  rw [cs, c3, c3, c3, Bool.eq_iff_iff]; simp; omega

lemma cellE (k : ℕ) :
    (∀ i : ℤ, cell 9 (2*k+4) i = decide (i = 2*k ∨ i = 2*k+1 ∨ i = 2*k+2 ∨ i = 2*k+4)) ∧
    (∀ i : ℤ, cell 9 (2*k+5) i = decide (i ≠ 2*k-1 ∧ i ≠ 2*k+1 ∧ i ≠ 2*k+2 ∧ i ≠ 2*k+3 ∧ i ≠ 2*k+4 ∧ i ≠ 2*k+5)) := by
  induction k with
  | zero =>
    have h4 : ∀ i : ℤ, cell 9 (2*0+4) i = decide (i = 2*(0:ℕ) ∨ i = 2*(0:ℕ)+1 ∨ i = 2*(0:ℕ)+2 ∨ i = 2*(0:ℕ)+4) := by
      intro i; rw [show 2*0+4 = 4 by rfl, c4, Bool.eq_iff_iff]; simp
    refine ⟨h4, fun i => ?_⟩
    rw [show 2*0+5 = 4+1 by rfl, cs, c4, c4, c4, Bool.eq_iff_iff]; simp; omega
  | succ k ih =>
    have h1 : ∀ i : ℤ, cell 9 (2*(k+1)+4) i = decide (i = 2*((k+1:ℕ):ℤ) ∨ i = 2*((k+1:ℕ):ℤ)+1 ∨ i = 2*((k+1:ℕ):ℤ)+2 ∨ i = 2*((k+1:ℕ):ℤ)+4) := by
      intro i
      rw [show 2*(k+1)+4 = (2*k+5)+1 by ring, cs, ih.2, ih.2, ih.2, Bool.eq_iff_iff]; simp; omega
    refine ⟨h1, fun i => ?_⟩
    rw [show 2*(k+1)+5 = (2*(k+1)+4)+1 by ring, cs, h1, h1, h1, Bool.eq_iff_iff]; simp; omega

lemma onE (k : ℕ) : onCount 9 (2*k+4) = 4 ∧ onCount 9 (2*k+5) = 2*(2*k+5) + 1 - 6 := by
  constructor
  · unfold onCount
    simp only [cellE k |>.1]
    rw [Finset.sum_boole]
    have : (Finset.range (2*(2*k+4)+1)).filter (fun j : ℕ => ((j:ℤ) - ((2*k+4:ℕ):ℤ)) = 2*k ∨ ((j:ℤ) - ((2*k+4:ℕ):ℤ)) = 2*k+1 ∨ ((j:ℤ) - ((2*k+4:ℕ):ℤ)) = 2*k+2 ∨ ((j:ℤ) - ((2*k+4:ℕ):ℤ)) = 2*k+4) = {4*k+4, 4*k+5, 4*k+6, 4*k+8} := by
      ext j; simp; omega
    simp only [decide_eq_true_eq]; rw [this]
    rw [Finset.card_insert_of_notMem (by simp), Finset.card_insert_of_notMem (by simp),
      Finset.card_insert_of_notMem (by simp), Finset.card_singleton]; rfl
  · unfold onCount
    simp only [cellE k |>.2]
    rw [Finset.sum_boole]
    have : (Finset.range (2*(2*k+5)+1)).filter (fun j : ℕ => ((j:ℤ) - ((2*k+5:ℕ):ℤ)) ≠ 2*k-1 ∧ ((j:ℤ) - ((2*k+5:ℕ):ℤ)) ≠ 2*k+1 ∧ ((j:ℤ) - ((2*k+5:ℕ):ℤ)) ≠ 2*k+2 ∧ ((j:ℤ) - ((2*k+5:ℕ):ℤ)) ≠ 2*k+3 ∧ ((j:ℤ) - ((2*k+5:ℕ):ℤ)) ≠ 2*k+4 ∧ ((j:ℤ) - ((2*k+5:ℕ):ℤ)) ≠ 2*k+5) = Finset.range (2*(2*k+5)+1) \ {4*k+4, 4*k+6, 4*k+7, 4*k+8, 4*k+9, 4*k+10} := by
      ext j; simp; omega
    simp only [decide_eq_true_eq]; rw [this, Finset.card_sdiff, Finset.inter_eq_left.mpr (by intro x; simp; omega)]
    rw [Finset.card_insert_of_notMem (by simp), Finset.card_insert_of_notMem (by simp),
      Finset.card_insert_of_notMem (by simp), Finset.card_insert_of_notMem (by simp),
      Finset.card_insert_of_notMem (by simp), Finset.card_singleton, Finset.card_range]; simp only [Nat.cast_id]

lemma on0 : onCount 9 0 = 1 := by decide
lemma on1 : onCount 9 1 = 0 := by decide
lemma on2 : onCount 9 2 = 2 := by decide
lemma on3 : onCount 9 3 = 2 := by decide

/-- ON count as a function of the step for t ≥ 4. -/
lemma onBig (t : ℕ) (ht : 4 ≤ t) : (onCount 9 t : ℚ) = if Even t then 4 else 2 * (t : ℚ) - 5 := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' t
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m-2, by omega⟩
    have he : Even (2*k+4) := ⟨k+2, by omega⟩
    rw [show 2*(k+2) = 2*k+4 by ring, (onE k).1]; simp [he]
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m-2, by omega⟩
    rw [show 2*(k+2)+1 = 2*k+5 by ring, (onE k).2]
    have : ¬ Even (2*k+5) := Nat.not_even_iff_odd.mpr ⟨k+2, by omega⟩
    rw [show 2*(2*k+5)+1-6 = 4*k+5 by omega]
    simp only [this, if_false]; push_cast; ring

lemma ps (f : ℕ → ℚ) (n k : ℕ) :
    PowerSeries.coeff n (PowerSeries.mk f * PowerSeries.X ^ k) = if k ≤ n then f (n-k) else 0 := by
  rw [PowerSeries.coeff_mul_X_pow']; simp

lemma ps1 (f : ℕ → ℚ) (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.mk f * PowerSeries.X) = if 1 ≤ n then f (n-1) else 0 := by
  rw [← ps, pow_one]

lemma key (n : ℕ) (hn : 3 ≤ n) : (a n : ℚ) = ((n : ℚ) ^ 2 - (-1 : ℚ) ^ n * ((n : ℚ) - 4) + 2) / 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n-3, by omega⟩
  induction m with
  | zero => simp [a, Finset.sum_range_succ, on0, on1, on2, on3]; norm_num
  | succ m ih =>
    have : a (m+1+3) = a (m+3) + (onCount 9 (m+1+3) : ℤ) := by
      simp only [a]; rw [show m+1+3 = (m+3)+1 by ring, Finset.sum_range_succ (n := m+3+1)]
    rw [this]; push_cast; rw [ih (by omega), onBig _ (by omega)]
    rcases Nat.even_or_odd m with h | h
    · have h' : Even (m+1+3) := by
        rw [show m+1+3 = m+4 by ring]; exact h.add ⟨2, rfl⟩
      simp only [h', if_true, pow_succ, h.neg_one_pow]; push_cast; ring
    · have h' : ¬ Even (m+1+3) := by
        rw [show m+1+3 = m+4 by ring, Nat.not_even_iff_odd]; exact h.add_even ⟨2, rfl⟩
      simp only [h', if_false, pow_succ, h.neg_one_pow]; push_cast; ring

open PowerSeries in
theorem main_proof :
    (∀ n : ℕ, 3 ≤ n → (a n : ℚ) = ((n : ℚ) ^ 2 - (-1 : ℚ) ^ n * ((n : ℚ) - 4) + 2) / 2) ∧
    (∀ n : ℕ, 8 ≤ n → (a n : ℚ) = a (n - 1) + 2 * a (n - 2) - 2 * a (n - 3) - a (n - 4) + a (n - 5)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) ^ 3 * (1 + X) ^ 2 : PowerSeries ℚ) = 1 + 2 * X ^ 3 + X ^ 4 + X ^ 5 - 2 * X ^ 6 + X ^ 7) := by
  have hrec : ∀ n : ℕ, 8 ≤ n → (a n : ℚ) = a (n - 1) + 2 * a (n - 2) - 2 * a (n - 3) - a (n - 4) + a (n - 5) := by
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 8 := ⟨n-8, by omega⟩
    rw [key _ (by omega), key _ (by omega), key _ (by omega), key _ (by omega), key _ (by omega), key _ (by omega)]
    simp only [show m+8-1 = m+7 by omega, show m+8-2 = m+6 by omega, show m+8-3 = m+5 by omega,
      show m+8-4 = m+4 by omega, show m+8-5 = m+3 by omega, pow_succ]
    push_cast; ring
  refine ⟨key, hrec, ?_⟩
  rw [show ((1 - X) ^ 3 * (1 + X) ^ 2 : PowerSeries ℚ) = 1 - X - C (2:ℚ) * X ^ 2 + C (2:ℚ) * X ^ 3 + X ^ 4 - X ^ 5 by simp only [map_ofNat]; ring]
  rw [show (1 + 2 * X ^ 3 + X ^ 4 + X ^ 5 - 2 * X ^ 6 + X ^ 7 : PowerSeries ℚ) = 1 + C (2:ℚ) * X ^ 3 + X ^ 4 + X ^ 5 - C (2:ℚ) * X ^ 6 + X ^ 7 by simp only [map_ofNat]]
  ext n
  simp only [mul_add, mul_sub, mul_one, map_add, map_sub, mul_left_comm _ (C _), PowerSeries.coeff_C_mul, ps, ps1, PowerSeries.coeff_X,
    PowerSeries.coeff_mk, PowerSeries.coeff_X_pow, PowerSeries.coeff_one]
  have a0 : (a 0 : ℚ) = 1 := by simp [a, on0]
  have a1 : (a 1 : ℚ) = 1 := by simp [a, Finset.sum_range_succ, on0, on1]
  have a2 : (a 2 : ℚ) = 3 := by simp [a, Finset.sum_range_succ, on0, on1, on2]
  have v : ∀ m : ℕ, 3 ≤ m → (a m : ℚ) = ((m : ℚ) ^ 2 - (-1 : ℚ) ^ m * ((m : ℚ) - 4) + 2) / 2 := key
  rcases (show n ≤ 7 ∨ 8 ≤ n by omega) with h | h
  · interval_cases n <;> simp [a0, a1, a2, v] <;> try norm_num
  · rw [hrec n h]
    simp [show n ≠ 0 by omega, show n ≠ 3 by omega, show n ≠ 4 by omega, show n ≠ 5 by omega, show n ≠ 6 by omega, show n ≠ 7 by omega,
      show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega, show 4 ≤ n by omega, show 5 ≤ n by omega]
    ring
end OMA.P_oeis_a266250

theorem OMA.solution : type_of% @OMA.S_oeis_a266250.main :=
  OMA.P_oeis_a266250.main_proof
