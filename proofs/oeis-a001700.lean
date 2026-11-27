import OMAStatements.S_oeis_a001700
import Mathlib

namespace OMA.S_oeis_a001700.Proof

open Finset

/-- The summand of `hyp`, written with binomials and factorials. -/
noncomputable def F (n k : ℕ) : ℚ :=
  (-1) ^ k * (n.choose k : ℚ) * ((2 * k).factorial : ℚ) /
    (4 ^ k * (k.factorial : ℚ) * ((k + 1).factorial : ℚ))

/-- The WZ certificate. -/
noncomputable def G (n k : ℕ) : ℚ := -2 * k * (k + 1) / (n + 1) * F (n + 1) k

noncomputable def S (n : ℕ) : ℚ := ∑ k ∈ range (n + 1), F n k

lemma choose_succ_right_q (m k : ℕ) :
    (m.choose (k + 1) : ℚ) * (k + 1) = (m.choose k : ℚ) * ((m : ℚ) - k) := by
  rcases le_or_gt k m with h | h
  · have := Nat.choose_succ_right_eq m k
    rw [← Nat.cast_sub h]
    exact_mod_cast this
  · rw [Nat.choose_eq_zero_of_lt h, Nat.choose_eq_zero_of_lt (by omega)]
    simp

lemma choose_mul_succ_q (n k : ℕ) :
    (n.choose k : ℚ) * (n + 1) = ((n + 1).choose k : ℚ) * ((n : ℚ) + 1 - k) := by
  rcases le_or_gt k (n + 1) with h | h
  · have := Nat.choose_mul_succ_eq n k
    have e : ((n : ℚ) + 1 - k) = ((n + 1 - k : ℕ) : ℚ) := by
      rw [Nat.cast_sub h]; push_cast; ring
    rw [e]
    exact_mod_cast this
  · rw [Nat.choose_eq_zero_of_lt (by omega), Nat.choose_eq_zero_of_lt h]
    simp

lemma step (n k : ℕ) :
    2 * ((n : ℚ) + 2) * F (n + 1) k - (2 * n + 3) * F n k = G n (k + 1) - G n k := by
  have hv := choose_succ_right_q (n + 1) k
  have hw := choose_mul_succ_q n k
  have hn1 : (n : ℚ) + 1 ≠ 0 := by positivity
  have hk1 : (k : ℚ) + 1 ≠ 0 := by positivity
  have e1 : (n.choose k : ℚ) = ((n + 1).choose k : ℚ) * ((n : ℚ) + 1 - k) / (n + 1) := by
    rw [eq_div_iff hn1]; exact hw
  have e2 : ((n + 1).choose (k + 1) : ℚ) = ((n + 1).choose k : ℚ) * ((n : ℚ) + 1 - k) / (k + 1) := by
    rw [eq_div_iff hk1, hv]; push_cast; ring
  simp only [F, G]
  rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, Nat.factorial_succ (2 * k + 1),
    Nat.factorial_succ (2 * k), Nat.factorial_succ (k + 1), Nat.factorial_succ k]
  push_cast
  rw [e1, e2]
  have h1 : ((2 * k).factorial : ℚ) ≠ 0 := by positivity
  have h2 : (k.factorial : ℚ) ≠ 0 := by positivity
  field_simp
  ring

lemma G_zero (n : ℕ) : G n 0 = 0 := by simp [G]

lemma F_zero_of_lt (n k : ℕ) (h : n < k) : F n k = 0 := by
  simp [F, Nat.choose_eq_zero_of_lt h]

lemma rec (n : ℕ) : 2 * ((n : ℚ) + 2) * S (n + 1) = (2 * n + 3) * S n := by
  have tel := Finset.sum_range_sub (G n) (n + 2)
  rw [G_zero, sub_zero] at tel
  have hG : G n (n + 2) = 0 := by
    simp [G, F_zero_of_lt (n + 1) (n + 2) (by omega)]
  rw [hG] at tel
  have hsum : ∑ i ∈ range (n + 2), (2 * ((n : ℚ) + 2) * F (n + 1) i - (2 * n + 3) * F n i) = 0 := by
    rw [← tel]
    exact Finset.sum_congr rfl fun i _ => step n i
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
  have hS : ∑ i ∈ range (n + 2), F n i = S n := by
    rw [Finset.sum_range_succ, F_zero_of_lt n (n + 1) (by omega), add_zero]; rfl
  rw [hS] at hsum
  show 2 * ((n : ℚ) + 2) * ∑ k ∈ range (n + 2), F (n + 1) k = (2 * n + 3) * S n
  linarith

lemma eval_two (k : ℕ) : (ascPochhammer ℚ k).eval 2 = ((k + 1).factorial : ℚ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [ascPochhammer_succ_eval, ih, Nat.factorial_succ (k + 1)]
    push_cast; ring

lemma eval_half (k : ℕ) :
    (ascPochhammer ℚ k).eval (1 / 2) = ((2 * k).factorial : ℚ) / (4 ^ k * (k.factorial : ℚ)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [ascPochhammer_succ_eval, ih, show 2 * (k + 1) = 2 * k + 1 + 1 by ring,
      Nat.factorial_succ (2 * k + 1), Nat.factorial_succ (2 * k), Nat.factorial_succ k]
    have h1 : ((2 * k).factorial : ℚ) ≠ 0 := by positivity
    have h2 : (k.factorial : ℚ) ≠ 0 := by positivity
    push_cast
    field_simp
    ring

lemma eval_neg (n k : ℕ) :
    (ascPochhammer ℚ k).eval (-(n : ℚ)) = (-1) ^ k * (k.factorial : ℚ) * (n.choose k : ℚ) := by
  rw [ascPochhammer_eval_neg_eq_descPochhammer, descPochhammer_eval_eq_descFactorial,
    Nat.descFactorial_eq_factorial_mul_choose]
  push_cast; ring

lemma hyp_eq (n : ℕ) : hyp n = S n := by
  unfold hyp S
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [eval_two, eval_half, eval_neg]
  unfold F
  have h1 : ((2 * k).factorial : ℚ) ≠ 0 := by positivity
  have h2 : (k.factorial : ℚ) ≠ 0 := by positivity
  have h3 : ((k + 1).factorial : ℚ) ≠ 0 := by positivity
  field_simp

lemma two_mul_choose (n : ℕ) : 2 * (2 * n + 1).choose (n + 1) = (n + 1).centralBinom := by
  rw [Nat.centralBinom_eq_two_mul_choose]
  have h1 : (2 * (n + 1)).choose (n + 1) = (2 * n + 1).choose n + (2 * n + 1).choose (n + 1) := by
    rw [show 2 * (n + 1) = (2 * n + 1) + 1 by ring]; exact Nat.choose_succ_succ (2 * n + 1) n
  rw [h1, ← Nat.choose_symm_half]
  ring

lemma T_rec (n : ℕ) :
    ((n : ℚ) + 2) * ((2 * (n + 1) + 1).choose (n + 1 + 1) : ℚ) =
      2 * (2 * n + 3) * ((2 * n + 1).choose (n + 1) : ℚ) := by
  have h := Nat.succ_mul_centralBinom_succ (n + 1)
  rw [← two_mul_choose (n + 1), ← two_mul_choose n] at h
  have h' : ((n + 1 + 1 : ℕ) : ℚ) * (2 * ((2 * (n + 1) + 1).choose (n + 1 + 1) : ℚ)) =
      (2 * (2 * (n + 1) + 1) : ℕ) * (2 * ((2 * n + 1).choose (n + 1) : ℚ)) := by
    exact_mod_cast h
  push_cast at h'
  linarith

theorem solution : ∀ n : ℕ, ((Nat.choose (2 * n + 1) (n + 1) : ℕ) : ℚ) = 4 ^ n * hyp n := by
  intro n
  rw [hyp_eq]
  induction n with
  | zero => simp [S, F]
  | succ n ih =>
    have r := rec n
    have hb := T_rec n
    have hn2 : (n : ℚ) + 2 ≠ 0 := by positivity
    have hS : S (n + 1) = (2 * n + 3) * S n / (2 * ((n : ℚ) + 2)) := by
      rw [eq_div_iff (by positivity)]; linarith
    have hT : ((2 * (n + 1) + 1).choose (n + 1 + 1) : ℚ) =
        2 * (2 * n + 3) * ((2 * n + 1).choose (n + 1) : ℚ) / ((n : ℚ) + 2) := by
      rw [eq_div_iff hn2]; linarith
    rw [hT, hS, ih]
    field_simp
    ring

end OMA.S_oeis_a001700.Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a001700.main := OMA.S_oeis_a001700.Proof.solution
