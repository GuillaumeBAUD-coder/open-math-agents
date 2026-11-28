import OMAStatements.S_oeis_a027154
import Mathlib

namespace OMA.P027154

open OMA.S_oeis_a027154 Finset

lemma T_zero (n : ℕ) : T n 0 = 1 := by
  rw [T]; simp

lemma T_out (n k : ℕ) (h : n < k) : T n k = 0 := by
  have h0 : k ≠ 0 := by omega
  rw [T]; simp [h0, h]

lemma T_even (n k : ℕ) (hk : k % 2 = 0) (hk2 : 2 ≤ k) : T (n + 1) k = T n (k - 1) + T n k := by
  rcases Nat.lt_or_ge (n + 1) k with h | h
  · rw [T_out _ _ h, T_out n (k - 1) (by omega), T_out n k (by omega)]
  · have h0 : k ≠ 0 := by omega
    have h1 : ¬ (n + 1 < k) := by omega
    have h2 : n ≠ 0 := by omega
    have h3 : ¬ (k % 2 = 1) := by omega
    rw [T]
    by_cases hn : (n + 1) % 2 = 0
    · by_cases hkn : k = n + 1
      · subst hkn
        have z : T n (n + 1) = 0 := T_out _ _ (by omega)
        simp [hn, z, h2]
      · simp [h0, h1, h2, h3, hn, hkn]
    · have hkn : ¬ (k = n + 1) := by omega
      simp [h0, h1, h2, h3, hn, hkn]

lemma T_odd_even (n k : ℕ) (hn : n % 2 = 0) (hk : k % 2 = 1) :
    T (n + 2) k = T n (k - 1) + T (n + 1) (k - 1) + T (n + 1) k := by
  rcases Nat.lt_or_ge (n + 2) k with h | h
  · rw [T_out _ _ h, T_out n (k - 1) (by omega), T_out (n + 1) (k - 1) (by omega),
      T_out (n + 1) k (by omega)]
  · have h0 : k ≠ 0 := by omega
    have h1 : ¬ (n + 2 < k) := by omega
    have h2 : ¬ (n + 2 = 1) := by omega
    have h3 : (n + 2) % 2 = 0 := by omega
    have h4 : ¬ (k = n + 2) := by omega
    rw [T]
    simp [h0, h1, h2, h3, h4, hk]

lemma T_odd_odd (n k : ℕ) (hn : n % 2 = 0) (hk : k % 2 = 1) :
    T (n + 1) k = T (n + 1) (k - 1) + T n (k - 1) + T n k := by
  rcases Nat.lt_or_ge (n + 1) k with h | h
  · rw [T_out _ _ h, T_out (n + 1) (k - 1) (by omega), T_out n (k - 1) (by omega),
      T_out n k (by omega)]
  · have h0 : k ≠ 0 := by omega
    have h1 : ¬ (n + 1 < k) := by omega
    have h3 : ¬ ((n + 1) % 2 = 0) := by omega
    rcases Nat.eq_zero_or_pos n with hz | hp
    · subst hz
      have hk1 : k = 1 := by omega
      subst hk1
      have z : T 0 1 = 0 := T_out _ _ (by omega)
      rw [T]
      simp [T_zero, z]
    · have h2 : n ≠ 0 := by omega
      rw [T]
      by_cases hkn : k = n + 1
      · subst hkn
        have z : T n (n + 1) = 0 := T_out _ _ (by omega)
        simp [h2, h3, z]
        ring
      · simp [h0, h1, h2, h3, hkn, hk]

/-- Sum over the antidiagonal `m` of the entries in even columns. -/
def E (m : ℕ) : ℕ := ∑ p ∈ antidiagonal m, if p.2 % 2 = 0 then T p.1 p.2 else 0

/-- Sum over the antidiagonal `m` of the entries in odd columns. -/
def O (m : ℕ) : ℕ := ∑ p ∈ antidiagonal m, if p.2 % 2 = 1 then T p.1 p.2 else 0

lemma a_eq (m : ℕ) : a m = E m + O m := by
  have h1 : E m + O m = ∑ p ∈ antidiagonal m, T p.1 p.2 := by
    unfold E O
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rcases Nat.mod_two_eq_zero_or_one p.2 with h | h <;> simp [h]
  have h2 : ∑ p ∈ antidiagonal m, T p.1 p.2 = ∑ k ∈ range (m + 1), T (m - k) k := by
    rw [← Finset.Nat.sum_antidiagonal_swap]
    exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => T j i) m
  rw [h1, h2]
  unfold a
  apply Finset.sum_subset
  · intro x hx
    simp only [Finset.mem_range] at hx ⊢
    omega
  · intro x hx hx'
    simp only [Finset.mem_range] at hx hx'
    exact T_out _ _ (by omega)

lemma upE (m : ℕ) :
    (∑ p ∈ antidiagonal m, if p.2 % 2 = 0 then T (p.1 + 1) p.2 else 0) = E (m + 1) := by
  unfold E
  rw [Finset.Nat.sum_antidiagonal_succ]
  have z : T 0 (m + 1) = 0 := T_out _ _ (by omega)
  simp [z]

lemma upO (m : ℕ) :
    (∑ p ∈ antidiagonal m, if p.2 % 2 = 1 then T (p.1 + 1) p.2 else 0) = O (m + 1) := by
  unfold O
  rw [Finset.Nat.sum_antidiagonal_succ]
  have z : T 0 (m + 1) = 0 := T_out _ _ (by omega)
  simp [z]

lemma shiftE (m : ℕ) :
    (∑ p ∈ antidiagonal (m + 1), if p.2 % 2 = 1 then T p.1 (p.2 - 1) else 0) = E m := by
  unfold E
  rw [Finset.Nat.sum_antidiagonal_succ']
  simp only [Nat.zero_mod, zero_ne_one, if_false, zero_add, Nat.add_sub_cancel]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rcases Nat.mod_two_eq_zero_or_one p.2 with h | h
  · have h' : (p.2 + 1) % 2 = 1 := by omega
    simp [h, h']
  · have h' : ¬ ((p.2 + 1) % 2 = 1) := by omega
    simp [h, h']

lemma shiftE1 (m : ℕ) :
    (∑ p ∈ antidiagonal (m + 1), if p.2 % 2 = 1 then T (p.1 + 1) (p.2 - 1) else 0) = E (m + 1) := by
  rw [← upE, Finset.Nat.sum_antidiagonal_succ']
  simp only [Nat.zero_mod, zero_ne_one, if_false, zero_add, Nat.add_sub_cancel]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rcases Nat.mod_two_eq_zero_or_one p.2 with h | h
  · have h' : (p.2 + 1) % 2 = 1 := by omega
    simp [h, h']
  · have h' : ¬ ((p.2 + 1) % 2 = 1) := by omega
    simp [h, h']

lemma shiftO (m : ℕ) :
    (∑ p ∈ antidiagonal (m + 1), if p.2 % 2 = 0 ∧ p.2 ≠ 0 then T p.1 (p.2 - 1) else 0) = O m := by
  unfold O
  rw [Finset.Nat.sum_antidiagonal_succ']
  simp only [ne_eq, not_true_eq_false, and_false, if_false, zero_add, Nat.add_sub_cancel]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rcases Nat.mod_two_eq_zero_or_one p.2 with h | h
  · have h' : ¬ ((p.2 + 1) % 2 = 0) := by omega
    simp [h, h']
  · have h' : (p.2 + 1) % 2 = 0 := by omega
    simp [h, h']

lemma sys1 (m : ℕ) : E (m + 2) = E (m + 1) + O m := by
  rw [← upE (m + 1), ← shiftO m]
  unfold E
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rcases Nat.mod_two_eq_zero_or_one p.2 with h | h
  · rcases Nat.eq_zero_or_pos p.2 with h0 | h0
    · simp [h0, T_zero]
    · have h2 : p.2 ≠ 0 := by omega
      rw [if_pos h, if_pos h, if_pos ⟨h, h2⟩, T_even _ _ h (by omega)]
      ring
  · have h' : ¬ (p.2 % 2 = 0) := by omega
    simp [h']

lemma sys2 (m : ℕ) (hm : m % 2 = 0) : O (m + 2) = O (m + 1) + E m + E (m + 1) := by
  rw [← upO (m + 1), ← shiftE m, ← shiftE1 m]
  unfold O
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  rcases Nat.mod_two_eq_zero_or_one p.2 with h | h
  · have h' : ¬ (p.2 % 2 = 1) := by omega
    simp [h']
  · rw [if_pos h, if_pos h, if_pos h, if_pos h, T_odd_odd _ _ (by omega) h]
    ring

lemma sys3 (m : ℕ) (hm : m % 2 = 0) : O (m + 3) = O (m + 2) + E (m + 1) + E m := by
  rw [← upO (m + 2), Finset.Nat.sum_antidiagonal_succ, ← upO (m + 1), ← shiftE m, ← shiftE1 m]
  have h2 : ¬ ((m + 1 + 1) % 2 = 1) := by omega
  rw [if_neg h2, zero_add, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  dsimp only
  rcases Nat.mod_two_eq_zero_or_one p.2 with h | h
  · have h' : ¬ (p.2 % 2 = 1) := by omega
    simp [h']
  · rw [if_pos h, if_pos h, if_pos h, if_pos h, T_odd_even _ _ (by omega) h]
    ring

lemma E0 : E 0 = 1 := by simp [E, T_zero]

lemma O0 : O 0 = 0 := by simp [O]

lemma E1 : E 1 = 1 := by
  have h := upE 0
  simp [T_zero] at h
  exact h.symm

lemma O1 : O 1 = 0 := by
  have h := upO 0
  simp at h
  exact h.symm

lemma vals : E 2 = 1 ∧ E 3 = 1 ∧ E 4 = 3 ∧ E 5 = 7 ∧ E 6 = 13 ∧ E 7 = 21 ∧ E 8 = 39 ∧
    O 2 = 2 ∧ O 3 = 4 ∧ O 4 = 6 ∧ O 5 = 8 ∧ O 6 = 18 ∧ O 7 = 28 ∧ O 8 = 62 := by
  have e0 := E0; have e1 := E1; have o0 := O0; have o1 := O1
  have e2 : E 2 = E 1 + O 0 := sys1 0
  have e3 : E 3 = E 2 + O 1 := sys1 1
  have e4 : E 4 = E 3 + O 2 := sys1 2
  have e5 : E 5 = E 4 + O 3 := sys1 3
  have e6 : E 6 = E 5 + O 4 := sys1 4
  have e7 : E 7 = E 6 + O 5 := sys1 5
  have e8 : E 8 = E 7 + O 6 := sys1 6
  have o2 : O 2 = O 1 + E 0 + E 1 := sys2 0 (by norm_num)
  have o3 : O 3 = O 2 + E 1 + E 0 := sys3 0 (by norm_num)
  have o4 : O 4 = O 3 + E 2 + E 3 := sys2 2 (by norm_num)
  have o5 : O 5 = O 4 + E 3 + E 2 := sys3 2 (by norm_num)
  have o6 : O 6 = O 5 + E 4 + E 5 := sys2 4 (by norm_num)
  have o7 : O 7 = O 6 + E 5 + E 4 := sys3 4 (by norm_num)
  have o8 : O 8 = O 7 + E 6 + E 7 := sys2 6 (by norm_num)
  omega

lemma both (n : ℕ) : E (n + 6) = 2 * E (n + 4) + 3 * E (n + 2) + 4 * E n ∧
    O (n + 6) = 2 * O (n + 4) + 3 * O (n + 2) + 4 * O n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 3 with h | h
    · have e0 := E0; have e1 := E1; have o0 := O0; have o1 := O1
      obtain ⟨e2, e3, e4, e5, e6, e7, e8, o2, o3, o4, o5, o6, o7, o8⟩ := vals
      interval_cases n <;> simp only [Nat.reduceAdd] <;> omega
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
      have i1 := ih (k + 2) (by omega)
      have i2 := ih (k + 1) (by omega)
      have i3 := ih k (by omega)
      have s9 := sys1 (k + 7)
      have s7 := sys1 (k + 5)
      have s5 := sys1 (k + 3)
      have s3 := sys1 (k + 1)
      simp only [Nat.add_assoc, Nat.reduceAdd] at i1 i2 i3 s9 s7 s5 s3 ⊢
      refine ⟨by omega, ?_⟩
      rcases Nat.mod_two_eq_zero_or_one k with hk | hk
      · have t9 := sys3 (k + 6) (by omega)
        have t7 := sys3 (k + 4) (by omega)
        have t5 := sys3 (k + 2) (by omega)
        have t3 := sys3 k (by omega)
        simp only [Nat.add_assoc, Nat.reduceAdd] at t9 t7 t5 t3
        omega
      · have t9 := sys2 (k + 7) (by omega)
        have t7 := sys2 (k + 5) (by omega)
        have t5 := sys2 (k + 3) (by omega)
        have t3 := sys2 (k + 1) (by omega)
        simp only [Nat.add_assoc, Nat.reduceAdd] at t9 t7 t5 t3
        omega

lemma rec (n : ℕ) (hn : 6 ≤ n) : a n = 2 * a (n - 2) + 3 * a (n - 4) + 4 * a (n - 6) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
  have e2 : m + 6 - 2 = m + 4 := by omega
  have e4 : m + 6 - 4 = m + 2 := by omega
  have e6 : m + 6 - 6 = m := by omega
  rw [e2, e4, e6, a_eq, a_eq, a_eq, a_eq]
  obtain ⟨h1, h2⟩ := both m
  omega

lemma va0 : a 0 = 1 := by rw [a_eq, E0, O0]
lemma va1 : a 1 = 1 := by rw [a_eq, E1, O1]
lemma va2 : a 2 = 3 := by rw [a_eq]; have := vals; omega
lemma va3 : a 3 = 5 := by rw [a_eq]; have := vals; omega
lemma va4 : a 4 = 9 := by rw [a_eq]; have := vals; omega
lemma va5 : a 5 = 15 := by rw [a_eq]; have := vals; omega

end OMA.P027154

open PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a027154.main := by
  refine ⟨OMA.P027154.rec, ?_⟩
  have key : -(PowerSeries.C (1 : ℤ) * PowerSeries.mk (fun n => (OMA.S_oeis_a027154.a n : ℤ)))
      + (PowerSeries.C (2 : ℤ) * (PowerSeries.mk (fun n => (OMA.S_oeis_a027154.a n : ℤ)) * PowerSeries.X ^ 2))
      + (PowerSeries.C (3 : ℤ) * (PowerSeries.mk (fun n => (OMA.S_oeis_a027154.a n : ℤ)) * PowerSeries.X ^ 4))
      + (PowerSeries.C (4 : ℤ) * (PowerSeries.mk (fun n => (OMA.S_oeis_a027154.a n : ℤ)) * PowerSeries.X ^ 6))
      - (-(PowerSeries.C (1 : ℤ))
      - (PowerSeries.X ^ 1 * PowerSeries.C (1 : ℤ))
      - (PowerSeries.X ^ 2 * PowerSeries.C (1 : ℤ))
      - (PowerSeries.X ^ 3 * PowerSeries.C (3 : ℤ))
      - (PowerSeries.X ^ 5 * PowerSeries.C (2 : ℤ))) = 0 := by
    ext n
    simp only [map_add, map_sub, map_neg, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow',
      PowerSeries.coeff_mk, PowerSeries.coeff_mul_C, PowerSeries.coeff_X_pow,
      PowerSeries.coeff_C, map_zero]
    rcases Nat.lt_or_ge n 6 with hlt | hge
    · interval_cases n <;> norm_num [OMA.P027154.va0, OMA.P027154.va1, OMA.P027154.va2,
        OMA.P027154.va3, OMA.P027154.va4, OMA.P027154.va5]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
      have h := OMA.P027154.rec (m + 6) (by omega)
      have h' : ((OMA.S_oeis_a027154.a (m + 6) : ℕ) : ℤ) = 2 * (OMA.S_oeis_a027154.a (m + 6 - 2) : ℤ)
          + 3 * (OMA.S_oeis_a027154.a (m + 6 - 4) : ℤ) + 4 * (OMA.S_oeis_a027154.a (m + 6 - 6) : ℤ) := by
        exact_mod_cast h
      have z0 : ¬ (m + 6 = 0) := by omega
      have z1 : ¬ (m + 6 = 1) := by omega
      have z2 : ¬ (m + 6 = 2) := by omega
      have z3 : ¬ (m + 6 = 3) := by omega
      have z5 : ¬ (m + 6 = 5) := by omega
      have w2 : 2 ≤ m + 6 := by omega
      have w4 : 4 ≤ m + 6 := by omega
      have w6 : 6 ≤ m + 6 := by omega
      simp only [z0, z1, z2, z3, z5, w2, w4, w6, if_true, if_false, zero_mul, sub_zero]
      linear_combination (-1 : ℤ) * h'
  simp only [map_ofNat, map_one] at key
  linear_combination key
