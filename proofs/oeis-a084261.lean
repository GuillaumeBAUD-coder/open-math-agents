import OMAStatements.S_oeis_a084261
import Mathlib

namespace A084261aux

open OMA.S_oeis_a084261 in
lemma a_ext (n N : ℕ) (h : n + 1 ≤ N) :
    a n = ∑ j ∈ Finset.range N, (n.choose j : ℤ) * interlaced j := by
  unfold a transform
  apply Finset.sum_subset (Finset.range_mono h)
  intro j _ hj
  rw [Finset.mem_range, not_lt] at hj
  rw [Nat.choose_eq_zero_of_lt (by omega)]
  simp

open OMA.S_oeis_a084261 in
lemma sum_pairs (g : ℕ → ℤ) (M : ℕ) :
    ∑ j ∈ Finset.range (2 * M), g j = ∑ i ∈ Finset.range M, (g (2 * i) + g (2 * i + 1)) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [show 2 * (M + 1) = 2 * M + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      ih, Finset.sum_range_succ]
    ring

open OMA.S_oeis_a084261 in
/-- The telescoping potential. -/
def U (k : ℕ) : ℕ → ℤ
  | 0 => 0
  | s + 1 => 2 * ((s + 1).factorial : ℤ) * ((k + 1).choose (2 * s) : ℤ)

open OMA.S_oeis_a084261 in
/-- The summand of the recurrence combination at index `j`. -/
def T (k j : ℕ) : ℤ :=
  interlaced j * (2 * ((k + 3).choose j : ℤ) - 4 * ((k + 2).choose j : ℤ)
    - ((k : ℤ) + 1) * ((k + 1).choose j : ℤ) + ((k : ℤ) + 1) * (k.choose j : ℤ))

open OMA.S_oeis_a084261 in
lemma T_odd (k i : ℕ) : T k (2 * i + 1) = 0 := by
  unfold T interlaced
  rw [if_neg (by omega)]
  ring

open OMA.S_oeis_a084261 in
lemma T_even (k i : ℕ) : T k (2 * i) = U k i - U k (i + 1) := by
  cases i with
  | zero =>
    have hU : U k 0 - U k (0 + 1) = -2 := by simp [U]
    have hT : T k (2 * 0) = -2 := by norm_num [T, interlaced]
    rw [hU, hT]
  | succ s =>
    have hU1 : U k (s + 1) = 2 * ((s + 1).factorial : ℤ) * ((k + 1).choose (2 * s) : ℤ) := rfl
    have hU2 : U k (s + 1 + 1)
        = 2 * ((s + 1 + 1).factorial : ℤ) * ((k + 1).choose (2 * (s + 1)) : ℤ) := rfl
    rw [hU1, hU2, show 2 * (s + 1) = 2 * s + 2 by ring, Nat.factorial_succ (s + 1)]
    unfold T interlaced
    rw [if_pos (by omega), show (2 * s + 2) / 2 = s + 1 by omega]
    have h1 : (k + 3).choose (2 * s + 2)
        = (k + 2).choose (2 * s + 1) + (k + 2).choose (2 * s + 2) :=
      Nat.choose_succ_succ (k + 2) (2 * s + 1)
    have h2 : (k + 2).choose (2 * s + 1) = (k + 1).choose (2 * s) + (k + 1).choose (2 * s + 1) :=
      Nat.choose_succ_succ (k + 1) (2 * s)
    have h3 : (k + 2).choose (2 * s + 2)
        = (k + 1).choose (2 * s + 1) + (k + 1).choose (2 * s + 2) :=
      Nat.choose_succ_succ (k + 1) (2 * s + 1)
    have h4 : (k + 1).choose (2 * s + 2) = k.choose (2 * s + 1) + k.choose (2 * s + 2) :=
      Nat.choose_succ_succ k (2 * s + 1)
    have h5 : (k + 1) * k.choose (2 * s + 1) = (k + 1).choose (2 * s + 2) * (2 * s + 2) :=
      Nat.add_one_mul_choose_eq k (2 * s + 1)
    have P1 : (((k + 3).choose (2 * s + 2) : ℕ) : ℤ)
        = ((k + 2).choose (2 * s + 1) : ℤ) + ((k + 2).choose (2 * s + 2) : ℤ) := by
      exact_mod_cast h1
    have P2 : (((k + 2).choose (2 * s + 1) : ℕ) : ℤ)
        = ((k + 1).choose (2 * s) : ℤ) + ((k + 1).choose (2 * s + 1) : ℤ) := by
      exact_mod_cast h2
    have P3 : (((k + 2).choose (2 * s + 2) : ℕ) : ℤ)
        = ((k + 1).choose (2 * s + 1) : ℤ) + ((k + 1).choose (2 * s + 2) : ℤ) := by
      exact_mod_cast h3
    have P4 : (((k + 1).choose (2 * s + 2) : ℕ) : ℤ)
        = (k.choose (2 * s + 1) : ℤ) + (k.choose (2 * s + 2) : ℤ) := by
      exact_mod_cast h4
    have Ab : ((k : ℤ) + 1) * (k.choose (2 * s + 1) : ℤ)
        = ((k + 1).choose (2 * s + 2) : ℤ) * (2 * (s : ℤ) + 2) := by
      exact_mod_cast h5
    push_cast
    linear_combination ((s + 1).factorial : ℤ)
      * (2 * P1 + 2 * P2 - 2 * P3 - ((k : ℤ) + 1) * P4 - Ab)

end A084261aux

theorem OMA.solution : type_of% @OMA.S_oeis_a084261.main := by
  intro k
  have hsum : 2 * OMA.S_oeis_a084261.a (k + 3) - 4 * OMA.S_oeis_a084261.a (k + 2)
      - ((k : ℤ) + 1) * OMA.S_oeis_a084261.a (k + 1) + ((k : ℤ) + 1) * OMA.S_oeis_a084261.a k
      = ∑ j ∈ Finset.range (2 * (k + 2)), A084261aux.T k j := by
    rw [A084261aux.a_ext (k + 3) (2 * (k + 2)) (by omega),
      A084261aux.a_ext (k + 2) (2 * (k + 2)) (by omega),
      A084261aux.a_ext (k + 1) (2 * (k + 2)) (by omega),
      A084261aux.a_ext k (2 * (k + 2)) (by omega)]
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    unfold A084261aux.T
    ring
  rw [hsum, A084261aux.sum_pairs]
  have hstep : ∀ i ∈ Finset.range (k + 2),
      A084261aux.T k (2 * i) + A084261aux.T k (2 * i + 1)
        = A084261aux.U k i - A084261aux.U k (i + 1) := fun i _ => by
    rw [A084261aux.T_even, A084261aux.T_odd, add_zero]
  rw [Finset.sum_congr rfl hstep, Finset.sum_range_sub']
  have hU0 : A084261aux.U k 0 = 0 := rfl
  have hU2 : A084261aux.U k (k + 1 + 1)
      = 2 * ((k + 1 + 1).factorial : ℤ) * ((k + 1).choose (2 * (k + 1)) : ℤ) := rfl
  rw [show k + 2 = k + 1 + 1 by ring, hU0, hU2, Nat.choose_eq_zero_of_lt (by omega)]
  simp
