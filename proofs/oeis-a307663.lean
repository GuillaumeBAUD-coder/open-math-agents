import OMAStatements.S_oeis_a307663
import Mathlib

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Sketch: with s(i) = sum_j C(i,j)/j one has s(i+1) = s(i) + (2^(i+1)-1)/(i+1) (Pascal plus
-- (i+1)C(i,k) = (k+1)C(i+1,k+1)); the double sum T(n) = sum_i i s(i) has the closed form
-- T(n) = (2n(n+1)s(n) - 4(n-2)2^n - 8 + n(n-1))/4, and a(n) = (n-1)! T(n). Substituting into the
-- recurrence, field_simp and ring close it. No computer search.

namespace OMA.A307663Proof

open OMA.S_oeis_a307663

def s (i : ℕ) : ℚ := ∑ j ∈ Finset.Icc 1 i, (i.choose j : ℚ) / (j : ℚ)

def T (n : ℕ) : ℚ := ∑ i ∈ Finset.Icc 1 n, (i : ℚ) * s i

lemma icc_eq (f : ℕ → ℚ) (n : ℕ) :
    ∑ j ∈ Finset.Icc 1 n, f j = ∑ k ∈ Finset.range n, f (k + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

lemma s_succ (i : ℕ) : s (i + 1) = s i + ((2 : ℚ) ^ (i + 1) - 1) / ((i : ℚ) + 1) := by
  have h1 : s (i + 1) = ∑ k ∈ Finset.range (i + 1),
      ((i.choose k : ℚ) + (i.choose (k + 1) : ℚ)) / ((k : ℚ) + 1) := by
    unfold s
    rw [icc_eq]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Nat.choose_succ_succ]
    push_cast
    ring
  have h2 : s i = ∑ k ∈ Finset.range (i + 1), (i.choose (k + 1) : ℚ) / ((k : ℚ) + 1) := by
    unfold s
    rw [icc_eq, Finset.sum_range_succ, Nat.choose_succ_self]
    push_cast
    simp
  have h3 : ∑ k ∈ Finset.range (i + 1), (i.choose k : ℚ) / ((k : ℚ) + 1)
      = ∑ k ∈ Finset.range (i + 1), ((i + 1).choose (k + 1) : ℚ) / ((i : ℚ) + 1) := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    have e := Nat.add_one_mul_choose_eq i k
    have e' : ((i : ℚ) + 1) * (i.choose k : ℚ) = ((i + 1).choose (k + 1) : ℚ) * ((k : ℚ) + 1) := by
      exact_mod_cast e
    have hk : (k : ℚ) + 1 ≠ 0 := by positivity
    have hi : (i : ℚ) + 1 ≠ 0 := by positivity
    field_simp
    linear_combination e'
  have h4 : ∑ k ∈ Finset.range (i + 1), ((i + 1).choose (k + 1) : ℚ) = (2 : ℚ) ^ (i + 1) - 1 := by
    have e := Nat.sum_range_choose (i + 1)
    rw [Finset.sum_range_succ'] at e
    simp only [Nat.choose_zero_right] at e
    have e' : ((∑ k ∈ Finset.range (i + 1), (i + 1).choose (k + 1) : ℕ) : ℚ) + 1 = (2 : ℚ) ^ (i + 1) := by
      exact_mod_cast e
    push_cast at e'
    linarith
  rw [h1, h2, ← h4, Finset.sum_div, ← h3, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  ring

lemma T_succ (n : ℕ) : T (n + 1) = T n + ((n : ℚ) + 1) * s (n + 1) := by
  unfold T
  rw [Finset.sum_Icc_succ_top (by omega)]
  push_cast
  ring

lemma T_closed (n : ℕ) : T n = (2 * (n : ℚ) * ((n : ℚ) + 1) * s n
    - 4 * ((n : ℚ) - 2) * (2 : ℚ) ^ n - 8 + (n : ℚ) * ((n : ℚ) - 1)) / 4 := by
  induction n with
  | zero => norm_num [T, s]
  | succ n ih =>
    rw [T_succ, ih, s_succ]
    have hn : (n : ℚ) + 1 ≠ 0 := by positivity
    push_cast
    field_simp
    ring

lemma a_eq (m : ℕ) : a (m + 1) = (m.factorial : ℚ) * T (m + 1) := by
  unfold a T s
  simp only [Nat.add_sub_cancel]
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

theorem mainP : type_of% @OMA.S_oeis_a307663.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have e3 : m + 1 + 3 = m + 3 + 1 := by ring
  have e2 : m + 1 + 2 = m + 2 + 1 := by ring
  rw [e3, e2, a_eq, a_eq, a_eq, a_eq]
  rw [T_succ (m + 3), T_succ (m + 2), T_succ (m + 1)]
  have f1 : (m + 3).factorial = (m + 3) * ((m + 2) * ((m + 1) * m.factorial)) := by
    simp [Nat.factorial_succ]
  have f2 : (m + 2).factorial = (m + 2) * ((m + 1) * m.factorial) := by
    simp [Nat.factorial_succ]
  have f3 : (m + 1).factorial = (m + 1) * m.factorial := by
    simp [Nat.factorial_succ]
  rw [f1, f2, f3]
  have s4 := s_succ (m + 3)
  have s3 := s_succ (m + 2)
  have s2 := s_succ (m + 1)
  rw [s4, s3, s2, T_closed (m + 1)]
  push_cast
  have h1 : (m : ℚ) + 1 + 1 ≠ 0 := by positivity
  have h2 : (m : ℚ) + 2 + 1 ≠ 0 := by positivity
  have h3 : (m : ℚ) + 3 + 1 ≠ 0 := by positivity
  rw [pow_succ (2 : ℚ) (m + 3), pow_succ (2 : ℚ) (m + 2), pow_succ (2 : ℚ) (m + 1)]
  field_simp
  ring


end OMA.A307663Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a307663.main := OMA.A307663Proof.mainP
